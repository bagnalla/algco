(** * Decidable and finitary pointed containers. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  List
  Program.Equality
.

Import ListNotations.

From algco Require Import
  axioms
  cpo
  order
.

From algco.generic Require Import
  container
  pointed_container
.

(** Directed completeness needs to distinguish the bottom shape from an
    exposed layer.  It does not require finite branching. *)
Record decidable_pointed_container : Type :=
  { dpc_pointed : pointed_container
  ; bottom_shape_dec : forall s : shape (pc_container dpc_pointed),
      {s = bottom_shape dpc_pointed} + {s <> bottom_shape dpc_pointed}
  }.

(** Compactness additionally requires every layer to have only finitely many
    recursive positions.  An enumeration need not be duplicate-free:
    completeness alone suffices to combine finitely many witnesses. *)
Record finitary_pointed_container : Type :=
  { fpc_decidable : decidable_pointed_container
  ; position_enum : forall
      s : shape (pc_container (dpc_pointed fpc_decidable)),
      list (position (pc_container (dpc_pointed fpc_decidable)) s)
  ; position_enum_complete : forall
      (s : shape (pc_container (dpc_pointed fpc_decidable)))
      (p : position (pc_container (dpc_pointed fpc_decidable)) s),
      In p (position_enum s)
  }.

Definition fpc_pointed (C : finitary_pointed_container) : pointed_container :=
  dpc_pointed (fpc_decidable C).

(** A coinductive value exposes information exactly when its outer shape is
    not the distinguished semantic bottom. *)
Definition nu_exposes (C : decidable_pointed_container)
  (x : nu (pc_container (dpc_pointed C))) : Prop :=
  match x with
  | in_nu s _ => s <> bottom_shape (dpc_pointed C)
  end.

Definition nu_exposes_dec (C : decidable_pointed_container)
  (x : nu (pc_container (dpc_pointed C))) :
  {nu_exposes C x} + {~ nu_exposes C x}.
Proof.
  destruct x as [s children].
  unfold nu_exposes.
  destruct (@bottom_shape_dec C s) as [Hs | Hs].
  - right; intro H; apply H, Hs.
  - left; exact Hs.
Defined.

(** Project a recursive position from a layer of the requested shape.  On a
    different shape, return semantic bottom.  Strong excluded middle supplies
    the equality test without requiring decidable equality for payloads stored
    in shapes.  Directedness will ensure that the mismatching case is used only
    for bottom stages in the chains relevant to [nu_sup]. *)
Definition nu_child (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (x : nu (pc_container (dpc_pointed C))) :
  nu (pc_container (dpc_pointed C)).
Proof.
  destruct x as [t children].
  destruct (classicT (s = t)) as [Hst | Hst].
  - subst t; exact (children p).
  - exact (nu_bottom (dpc_pointed C)).
Defined.

Lemma nu_le_exposed_inv (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (y : nu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  nu_le (dpc_pointed C) (in_nu s children) y ->
  exists children' : position (pc_container (dpc_pointed C)) s ->
      nu (pc_container (dpc_pointed C)),
    y = in_nu s children' /\
    forall p, nu_le (dpc_pointed C) (children p) (children' p).
Proof.
  intros Hs Hle.
  dependent destruction Hle.
  - exfalso; apply Hs; reflexivity.
  - exists children2; split; [reflexivity | exact H].
Qed.

Lemma nu_le_layer_inv (C : decidable_pointed_container)
  (x : nu (pc_container (dpc_pointed C)))
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C))) :
  nu_le (dpc_pointed C) x (in_nu s children) ->
  (exists bottom_children, x = in_nu (bottom_shape (dpc_pointed C))
      bottom_children) \/
  (exists children' : position (pc_container (dpc_pointed C)) s ->
      nu (pc_container (dpc_pointed C)),
    x = in_nu s children' /\
    forall p, nu_le (dpc_pointed C) (children' p) (children p)).
Proof.
  intro Hle.
  dependent destruction Hle.
  - left; exists children0; reflexivity.
  - right; exists children1; split; [reflexivity | exact H].
Qed.

Lemma nu_child_same (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s) :
  nu_child C s p (in_nu s children) = children p.
Proof.
  unfold nu_child.
  destruct (classicT (s = s)) as [Hss | Hss].
  - dependent destruction Hss; reflexivity.
  - exfalso; apply Hss; reflexivity.
Qed.

Lemma nu_child_bottom (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (children : position (pc_container (dpc_pointed C))
      (bottom_shape (dpc_pointed C)) ->
    nu (pc_container (dpc_pointed C))) :
  nu_child C s p
    (in_nu (bottom_shape (dpc_pointed C)) children) =
  nu_bottom (dpc_pointed C).
Proof.
  unfold nu_child.
  destruct (classicT (s = bottom_shape (dpc_pointed C))) as [Hs | Hs].
  - destruct (bottom_position_absurd (dpc_pointed C) (eq_rect _ _ p _ Hs)).
  - reflexivity.
Qed.

Lemma nu_child_monotone (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (x y : nu (pc_container (dpc_pointed C))) :
  nu_le (dpc_pointed C) x y ->
  nu_le (dpc_pointed C) (nu_child C s p x) (nu_child C s p y).
Proof.
  intro Hxy.
  destruct Hxy as [children y | t children1 children2 Hchildren].
  - rewrite nu_child_bottom; constructor.
  - unfold nu_child.
    destruct (classicT (s = t)) as [Hst | Hst].
    + dependent destruction Hst; apply Hchildren.
    + apply nu_le_refl.
Qed.

Definition nu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  nat -> nu (pc_container (dpc_pointed C)) :=
  fun i => nu_child C s p (ch i).

Lemma directed_nu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  directed ch -> directed (nu_child_chain C s p ch).
Proof.
  intros Hch i j.
  destruct (Hch i j) as [k [Hik Hjk]].
  exists k; split; apply nu_child_monotone; assumption.
Qed.

Lemma upper_bound_nu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  upper_bound (in_nu s children) ch ->
  upper_bound (children p) (nu_child_chain C s p ch).
Proof.
  intros Hub i.
  unfold nu_child_chain.
  rewrite <- nu_child_same.
  apply nu_child_monotone, Hub.
Qed.

(** This is the generic analogue of [colist_sup] and [cotree_sup].  If no
    stage exposes a constructor, the supremum is bottom.  Otherwise a
    classically selected exposed layer determines the result shape and each
    recursive position takes the supremum of its projected child chain.

    The definition is total even on nondirected inputs.  Shape mismatches in
    such inputs are projected to bottom; the correctness proof will use
    directedness to show that this convention is irrelevant. *)
CoFixpoint nu_sup (C : decidable_pointed_container)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  nu (pc_container (dpc_pointed C)) :=
  match LPO_option (fun n => nu_exposes_dec C (ch n)) with
  | Some n =>
      match ch n with
      | in_nu s _ =>
          in_nu s (fun p => nu_sup C (nu_child_chain C s p ch))
      end
  | None => nu_bottom (dpc_pointed C)
  end.

Lemma nu_sup_unfold (C : decidable_pointed_container)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  nu_sup C ch =
  match LPO_option (fun n => nu_exposes_dec C (ch n)) with
  | Some n =>
      match ch n with
      | in_nu s _ =>
          in_nu s (fun p => nu_sup C (nu_child_chain C s p ch))
      end
  | None => nu_bottom (dpc_pointed C)
  end.
Proof.
  rewrite unfold_nu_eq at 1; simpl.
  destruct (LPO_option (fun n => nu_exposes_dec C (ch n))) as [n |].
  - destruct (ch n); reflexivity.
  - reflexivity.
Qed.

Lemma nu_sup_upper_bound (C : decidable_pointed_container)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  directed ch -> upper_bound (nu_sup C ch) ch.
Proof.
  revert ch.
  cofix CH; intros ch Hch i.
  rewrite nu_sup_unfold.
  destruct (LPO_option (fun n => nu_exposes_dec C (ch n))) eqn:Ho.
  - pose proof Ho as Hexposes.
    apply LPO_option_some in Hexposes.
    destruct (ch n) as [s children] eqn:Hn; simpl in Hexposes.
    destruct (Hch i n) as [k [Hik Hnk]].
    rewrite Hn in Hnk.
    destruct (nu_le_exposed_inv C Hexposes Hnk)
      as [childrenk [Hk Hchildrenk]].
    rewrite Hk in Hik.
    destruct (nu_le_layer_inv C Hik)
      as [[bottom_children Hi] | [childreni [Hi Hchildreni]]].
    + rewrite Hi; constructor.
    + rewrite Hi; constructor; intro p.
      rewrite <- nu_child_same.
      rewrite <- Hi.
      change
        (nu_le (dpc_pointed C) ((nu_child_chain C s p ch) i)
          (nu_sup C (nu_child_chain C s p ch))).
      exact
        ((CH (nu_child_chain C s p ch)
          (@directed_nu_child_chain C s p ch Hch)) i).
  - apply LPO_option_none with (n := i) in Ho.
    destruct (ch i) as [s children]; simpl in Ho.
    destruct (@bottom_shape_dec C s) as [Hs | Hs].
    + dependent destruction Hs; constructor.
    + exfalso; apply Ho, Hs.
Qed.

Lemma nu_sup_least (C : decidable_pointed_container)
  (ch : nat -> nu (pc_container (dpc_pointed C)))
  (ub : nu (pc_container (dpc_pointed C))) :
  directed ch -> upper_bound ub ch -> nu_le (dpc_pointed C) (nu_sup C ch) ub.
Proof.
  revert ch ub.
  cofix CH; intros ch ub Hch Hub.
  rewrite nu_sup_unfold.
  destruct (LPO_option (fun n => nu_exposes_dec C (ch n))) eqn:Ho.
  - pose proof Ho as Hexposes.
    apply LPO_option_some in Hexposes.
    destruct (ch n) as [s children] eqn:Hn; simpl in Hexposes.
    pose proof (Hub n) as Hnub.
    rewrite Hn in Hnub.
    destruct (nu_le_exposed_inv C Hexposes Hnub)
      as [childrenub [Hub_shape Hchildrenub]].
    rewrite Hub_shape in Hub |- *.
    constructor; intro p.
    apply CH.
    + apply directed_nu_child_chain, Hch.
    + apply upper_bound_nu_child_chain, Hub.
  - constructor.
Qed.

Theorem nu_sup_supremum (C : decidable_pointed_container)
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  directed ch -> supremum (nu_sup C ch) ch.
Proof.
  intro Hch; split.
  - apply nu_sup_upper_bound, Hch.
  - intros ub Hub; apply nu_sup_least; assumption.
Qed.

#[global]
Instance CPO_decidable_container_nu (C : decidable_pointed_container) :
  CPO (nu (pc_container (dpc_pointed C))).
Proof.
  constructor; intros ch Hch.
  exists (nu_sup C ch); apply nu_sup_supremum, Hch.
Qed.
