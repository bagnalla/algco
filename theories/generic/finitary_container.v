(** * Decidable and finitary pointed containers. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  IndefiniteDescription
  List
  Program.Equality
.

Import ListNotations.

From algco Require Import
  aCPO
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

(** A finite family of stages in a directed sequence has a common later
    stage.  Keeping the finite family abstract lets compactness aggregate one
    witness for every recursive position without assuming an order on the
    positions themselves. *)
Lemma directed_finite_upper {A I : Type} `{OType A}
  (ch : nat -> A) :
  directed ch ->
  forall (index : I -> nat) (xs : list I),
    exists k, forall x, In x xs -> leq (ch (index x)) (ch k).
Proof.
  intros Hch index xs.
  induction xs as [|x xs [k Hk]].
  - exists 0; intros y Hy; inversion Hy.
  - destruct (Hch (index x) k) as [l [Hxl Hkl]].
    exists l; intros y [Hy | Hy].
    + subst y; exact Hxl.
    + transitivity (ch k); [apply Hk; exact Hy | exact Hkl].
Qed.

(** ** Finite fixed-point observations *)

(** An inductive value exposes information exactly when its outer shape is
    not the distinguished semantic bottom. *)
Definition mu_exposes (C : decidable_pointed_container)
  (x : mu (pc_container (dpc_pointed C))) : Prop :=
  match x with
  | in_mu s _ => s <> bottom_shape (dpc_pointed C)
  end.

Definition mu_exposes_dec (C : decidable_pointed_container)
  (x : mu (pc_container (dpc_pointed C))) :
  {mu_exposes C x} + {~ mu_exposes C x}.
Proof.
  destruct x as [s children].
  unfold mu_exposes.
  destruct (@bottom_shape_dec C s) as [Hs | Hs].
  - right; intro H; apply H, Hs.
  - left; exact Hs.
Defined.

(** Project a recursive position from an inductive layer.  As for [nu_child],
    a shape mismatch projects to bottom. *)
Definition mu_child (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (x : mu (pc_container (dpc_pointed C))) :
  mu (pc_container (dpc_pointed C)).
Proof.
  destruct x as [t children].
  destruct (classicT (s = t)) as [Hst | Hst].
  - subst t; exact (children p).
  - exact (mu_bottom (dpc_pointed C)).
Defined.

Lemma mu_le_exposed_inv (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C)))
  (y : mu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  mu_le (dpc_pointed C) (in_mu s children) y ->
  exists children' : position (pc_container (dpc_pointed C)) s ->
      mu (pc_container (dpc_pointed C)),
    y = in_mu s children' /\
    forall p, mu_le (dpc_pointed C) (children p) (children' p).
Proof.
  intros Hs Hle.
  dependent destruction Hle.
  - exfalso; apply Hs; reflexivity.
  - exists children2; split; [reflexivity | exact H].
Qed.

Lemma mu_le_layer_inv (C : decidable_pointed_container)
  (x : mu (pc_container (dpc_pointed C)))
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C))) :
  mu_le (dpc_pointed C) x (in_mu s children) ->
  (exists bottom_children, x = in_mu (bottom_shape (dpc_pointed C))
      bottom_children) \/
  (exists children' : position (pc_container (dpc_pointed C)) s ->
      mu (pc_container (dpc_pointed C)),
    x = in_mu s children' /\
    forall p, mu_le (dpc_pointed C) (children' p) (children p)).
Proof.
  intro Hle.
  dependent destruction Hle.
  - left; exists children0; reflexivity.
  - right; exists children1; split; [reflexivity | exact H].
Qed.

Lemma mu_child_same (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s) :
  mu_child C s p (in_mu s children) = children p.
Proof.
  unfold mu_child.
  destruct (classicT (s = s)) as [Hss | Hss].
  - dependent destruction Hss; reflexivity.
  - exfalso; apply Hss; reflexivity.
Qed.

Lemma mu_child_bottom (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (children : position (pc_container (dpc_pointed C))
      (bottom_shape (dpc_pointed C)) ->
    mu (pc_container (dpc_pointed C))) :
  mu_child C s p
    (in_mu (bottom_shape (dpc_pointed C)) children) =
  mu_bottom (dpc_pointed C).
Proof.
  unfold mu_child.
  destruct (classicT (s = bottom_shape (dpc_pointed C))) as [Hs | Hs].
  - destruct (bottom_position_absurd (dpc_pointed C) (eq_rect _ _ p _ Hs)).
  - reflexivity.
Qed.

Lemma mu_child_monotone (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (x y : mu (pc_container (dpc_pointed C))) :
  mu_le (dpc_pointed C) x y ->
  mu_le (dpc_pointed C) (mu_child C s p x) (mu_child C s p y).
Proof.
  intro Hxy.
  destruct Hxy as [children y | t children1 children2 Hchildren].
  - rewrite mu_child_bottom; constructor.
  - unfold mu_child.
    destruct (classicT (s = t)) as [Hst | Hst].
    + dependent destruction Hst; apply Hchildren.
    + apply mu_le_refl.
Qed.

Definition mu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> mu (pc_container (dpc_pointed C))) :
  nat -> mu (pc_container (dpc_pointed C)) :=
  fun i => mu_child C s p (ch i).

Lemma directed_mu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> mu (pc_container (dpc_pointed C))) :
  directed ch -> directed (mu_child_chain C s p ch).
Proof.
  intros Hch i j.
  destruct (Hch i j) as [k [Hik Hjk]].
  exists k; split; apply mu_child_monotone; assumption.
Qed.

Lemma upper_bound_mu_child_chain (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (ch : nat -> mu (pc_container (dpc_pointed C))) :
  upper_bound (in_mu s children) ch ->
  upper_bound (children p) (mu_child_chain C s p ch).
Proof.
  intros Hub i.
  unfold mu_child_chain.
  rewrite <- mu_child_same.
  apply mu_child_monotone, Hub.
Qed.

Definition replace_child {P X : Type}
  (p : P) (x : X) (children : P -> X) (q : P) : X :=
  match classicT (q = p) with
  | left _ => x
  | right _ => children q
  end.

Lemma replace_child_same {P X : Type}
  (p : P) (x : X) (children : P -> X) :
  replace_child p x children p = x.
Proof.
  unfold replace_child.
  destruct (classicT (p = p)) as [Hpp | Hpp].
  - reflexivity.
  - exfalso; apply Hpp; reflexivity.
Qed.

Lemma replace_child_other {P X : Type}
  (p q : P) (x : X) (children : P -> X) :
  q <> p -> replace_child p x children q = children q.
Proof.
  intro Hqp; unfold replace_child.
  destruct (classicT (q = p)) as [Heq | Heq].
  - exfalso; apply Hqp, Heq.
  - reflexivity.
Qed.

(** If a layer is the supremum of a directed sequence, each recursive child
    is the supremum of the corresponding projected sequence.  For leastness,
    replace just that child by an arbitrary upper bound and use leastness of
    the whole layer. *)
Lemma supremum_mu_child (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C)))
  (ch : nat -> mu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s) :
  supremum (in_mu s children) ch ->
  supremum (children p) (mu_child_chain C s p ch).
Proof.
  intros [Hub Hlub]; split.
  - apply upper_bound_mu_child_chain; exact Hub.
  - intros ub Hub_child.
    set (replacement := replace_child p ub children).
    assert (Hcandidate : upper_bound (in_mu s replacement) ch).
    { intro i.
      destruct (mu_le_layer_inv C (Hub i)) as
        [[bottom_children Hi] | [childreni [Hi Hchildreni]]].
      - rewrite Hi; constructor.
      - rewrite Hi; constructor; intro q.
        destruct (classicT (q = p)) as [Hqp | Hqp].
        + subst q; unfold replacement; rewrite replace_child_same.
          specialize (Hub_child i).
          unfold mu_child_chain in Hub_child.
          rewrite Hi, mu_child_same in Hub_child.
          exact Hub_child.
        + unfold replacement; rewrite replace_child_other; auto.
    }
    pose proof (Hlub _ Hcandidate) as Hlayer.
    pose proof
      (@mu_child_monotone C s p (in_mu s children)
        (in_mu s replacement) Hlayer) as Hchild.
    rewrite !mu_child_same in Hchild.
    unfold replacement in Hchild; rewrite replace_child_same in Hchild.
    exact Hchild.
Qed.

Lemma mu_le_exposed_not_bottom (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  ~ mu_le (dpc_pointed C) (in_mu s children)
      (mu_bottom (dpc_pointed C)).
Proof.
  intros Hs Hle; unfold mu_bottom in Hle.
  dependent destruction Hle; apply Hs; reflexivity.
Qed.

(** A nonbottom supremum must already expose its outer shape at some stage.
    This isolates the one use of strong LPO in the compactness argument. *)
Lemma supremum_mu_exposed_stage (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    mu (pc_container (dpc_pointed C)))
  (ch : nat -> mu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  supremum (in_mu s children) ch ->
  exists i,
    exists children' : position (pc_container (dpc_pointed C)) s ->
        mu (pc_container (dpc_pointed C)),
      ch i = in_mu s children' /\
      forall p, mu_le (dpc_pointed C) (children' p) (children p).
Proof.
  intros Hs [Hub Hlub].
  destruct (strong_LPO (fun n => mu_exposes_dec C (ch n))) as [Hex | Hnone].
  - destruct Hex as [i Hi].
    destruct (mu_le_layer_inv C (Hub i)) as
      [[bottom_children Hbottom] | [childreni [Hshape Hchildren]]].
    + rewrite Hbottom in Hi; simpl in Hi.
      exfalso; apply Hi; reflexivity.
    + exists i, childreni; split; assumption.
  - assert (Hbottom : upper_bound (mu_bottom (dpc_pointed C)) ch).
    { intro i.
      destruct (ch i) as [t childreni] eqn:Hi.
      destruct (@bottom_shape_dec C t) as [Ht | Ht].
      - dependent destruction Ht; constructor.
      - exfalso; apply Hnone; exists i; rewrite Hi; exact Ht.
    }
    apply Hlub in Hbottom.
    exfalso; eapply mu_le_exposed_not_bottom; eauto.
Qed.

(** Every element of the initial algebra of a finitary pointed container is
    compact.  Structural induction supplies a stage for each child; finite
    enumeration and directedness merge those stages into one stage exposing
    the entire finite tree. *)
Theorem mu_compact (C : finitary_pointed_container)
  (x : mu (pc_container (fpc_pointed C))) :
  @compact (mu (pc_container (fpc_pointed C)))
    (OType_container_mu (fpc_pointed C)) x.
Proof.
  induction x as [s children IH].
  intros ch Hch Hsup.
  destruct (@bottom_shape_dec (fpc_decidable C) s) as [Hs | Hs].
  - dependent destruction Hs.
    exists 0; split.
    + exact ((proj1 Hsup) 0).
    + constructor.
  - destruct
      (supremum_mu_exposed_stage (fpc_decidable C) Hs Hsup)
      as [j [childrenj [Hj Hchildrenj]]].
    assert (Hchild_witness : forall
      p : position (pc_container (fpc_pointed C)) s,
      exists i,
        equ ((mu_child_chain (fpc_decidable C) s p ch) i) (children p)).
    { intro p.
      apply (IH p).
      - apply directed_mu_child_chain; exact Hch.
      - apply supremum_mu_child; exact Hsup.
    }
    pose (index := fun p : position (pc_container (fpc_pointed C)) s =>
      proj1_sig
        (constructive_indefinite_description
          (fun i =>
            equ ((mu_child_chain (fpc_decidable C) s p ch) i)
              (children p))
          (Hchild_witness p))).
    assert (Hindex : forall
      p : position (pc_container (fpc_pointed C)) s,
      equ ((mu_child_chain (fpc_decidable C) s p ch) (index p))
        (children p)).
    { intro p; unfold index.
      destruct
        (constructive_indefinite_description
          (fun i =>
            equ ((mu_child_chain (fpc_decidable C) s p ch) i)
              (children p))
          (Hchild_witness p)) as [i Hi].
      exact Hi.
    }
    destruct
      (@directed_finite_upper _ _ _ ch Hch index
        (@position_enum C s))
      as [k Hk].
    destruct (Hch j k) as [l [Hjl Hkl]].
    exists l; split.
    + exact ((proj1 Hsup) l).
    + rewrite Hj in Hjl.
      destruct (mu_le_exposed_inv (fpc_decidable C) Hs Hjl)
        as [childrenl [Hl Hchildrenl]].
      rewrite Hl; constructor; intro p.
      transitivity
        (mu_child (fpc_decidable C) s p (ch (index p))).
      * exact (proj2 (Hindex p)).
      * transitivity (mu_child (fpc_decidable C) s p (ch k)).
        -- apply mu_child_monotone, Hk.
           apply position_enum_complete.
        -- transitivity (mu_child (fpc_decidable C) s p (ch l)).
           ++ apply mu_child_monotone; exact Hkl.
           ++ rewrite Hl, mu_child_same; reflexivity.
Qed.

#[global]
Instance Compact_finitary_container_mu (C : finitary_pointed_container) :
  @Compact (mu (pc_container (fpc_pointed C)))
    (OType_container_mu (fpc_pointed C)).
Proof. constructor; apply mu_compact. Qed.

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
