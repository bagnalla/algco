(** * Semantic values and their lifted partial completion. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Eqdep
  Program.Equality
.

From algco Require Import
  order
.

From algco.generic Require Import
  container
  container_combinators
  indexed_container
  pointed_container
.

Local Open Scope order_scope.

(** An ordinary container describes fully formed semantic layers; no
    finiteness or pointedness is required at this level. *)
Definition Semantic (C : container) : Type :=
  nu C.

(** A finitary presentation is needed only when the lifted carrier is equipped
    with the existing compact-basis structure.  [finitary_point] adds its
    fresh approximation hole. *)
Definition FinitePartial (C : finitary_container) : Type :=
  Basis (finitary_point C).

Definition Partial (C : finitary_container) : Type :=
  Value (finitary_point C).

Arguments Semantic C : clear implicits.
Arguments FinitePartial C : clear implicits.
Arguments Partial C : clear implicits.

Definition returned_shape {C : container} (s : shape C) :
  shape (pc_container (point_container C)) :=
  @inr unit (shape C) s.

(** Returning every semantic layer gives a structural embedding into the
    lifted carrier.  The lift occurs at every recursive boundary, rather than
    only once outside the final coalgebra. *)
CoFixpoint embed_carrier {C : container} (x : Semantic C) :
  nu (pc_container (point_container C)) :=
  match x with
  | in_nu s children =>
      in_nu (returned_shape s) (fun p => embed_carrier (children p))
  end.

Definition embed {C : finitary_container}
  (x : Semantic (fc_container C)) : Partial C :=
  {| value_carrier := embed_carrier x |}.

Lemma embed_carrier_in {C : container}
  (s : shape C) (children : position C s -> Semantic C) :
  embed_carrier (in_nu s children) =
  in_nu (returned_shape s) (fun p => embed_carrier (children p)).
Proof.
  rewrite unfold_nu_eq; reflexivity.
Qed.

Lemma embed_in {C : finitary_container}
  (s : shape (fc_container C))
  (children : position (fc_container C) s ->
    Semantic (fc_container C)) :
  embed (in_nu s children) =
  in_value (returned_shape s) (fun p => embed (children p)).
Proof.
  unfold embed, in_value.
  rewrite embed_carrier_in; reflexivity.
Qed.

(** ** Totality and realization *)

(** A lifted value is structurally total when every layer has returned a
    semantic shape and all of its recursive children are structurally total.
    This definition is independent of finite-position evidence; finite
    observations will later give an operational characterization of it. *)
CoInductive total_carrier {C : container} :
  nu (pc_container (point_container C)) -> Prop :=
| total_returned : forall
    (d : nu (pc_container (point_container C)))
    (s : shape C)
    (children : position C s ->
      nu (pc_container (point_container C))),
    out_nu d = existT _ (returned_shape s) children ->
    (forall p, total_carrier (children p)) ->
    total_carrier d.

(** A partial value realizes a semantic value exactly when it approximates
    that value's structural embedding.  The existing coinductive [nu_le] is
    already the greatest fixed point of the desired relational action:
    pending makes no claim, while returned layers must have the same semantic
    shape and pointwise-related children. *)
Definition realizes_carrier {C : container}
  (d : nu (pc_container (point_container C)))
  (v : Semantic C) : Prop :=
  nu_le (point_container C) d (embed_carrier v).

(** Descriptor-indexed facades for the algebraic partial carrier. *)
Definition Total {C : finitary_container} (d : Partial C) : Prop :=
  total_carrier (value_carrier d).

Definition Realizes {C : finitary_container}
  (d : Partial C) (v : Semantic (fc_container C)) : Prop :=
  realizes_carrier (value_carrier d) v.

Lemma realizes_carrier_pending {C : container}
  (children : position
    (pc_container (point_container C))
    (bottom_shape (point_container C)) ->
    nu (pc_container (point_container C)))
  (v : Semantic C) :
  realizes_carrier
    (in_nu (bottom_shape (point_container C)) children) v.
Proof. unfold realizes_carrier; constructor. Qed.

Lemma realizes_carrier_returned {C : container}
  (s : shape C)
  (partial_children : position C s ->
    nu (pc_container (point_container C)))
  (semantic_children : position C s -> Semantic C) :
  (forall p,
    realizes_carrier (partial_children p) (semantic_children p)) ->
  realizes_carrier
    (in_nu (returned_shape s) partial_children)
    (in_nu s semantic_children).
Proof.
  unfold realizes_carrier; rewrite embed_carrier_in.
  constructor; auto.
Qed.

Lemma total_carrier_pending_absurd {C : container}
  (children : position
    (pc_container (point_container C))
    (bottom_shape (point_container C)) ->
    nu (pc_container (point_container C))) :
  ~ total_carrier
      (in_nu (bottom_shape (point_container C)) children).
Proof.
  intro Htotal; dependent destruction Htotal.
Qed.

Lemma total_carrier_returned_iff {C : container}
  (s : shape C)
  (children : position C s ->
    nu (pc_container (point_container C))) :
  total_carrier (in_nu (returned_shape s) children) <->
  forall p, total_carrier (children p).
Proof.
  split.
  - intro Htotal.
    remember (in_nu (returned_shape s) children) as d eqn:Hd in Htotal.
    destruct Htotal as [d' s' children' Hout Hchildren].
    subst d'; simpl in Hout; injection Hout.
    intro Hshape; subst s'.
    apply inj_pair2 in Hout; subst children'.
    exact Hchildren.
  - intro Hchildren.
    econstructor; [reflexivity | exact Hchildren].
Qed.

Lemma total_embed_carrier {C : container} (v : Semantic C) :
  total_carrier (embed_carrier v).
Proof.
  revert v; cofix CH; intros [s children].
  rewrite embed_carrier_in.
  refine (@total_returned C
    (in_nu (returned_shape s) (fun p => embed_carrier (children p))) s
    (fun p => embed_carrier (children p)) eq_refl _).
  intro p; apply CH.
Qed.

Lemma realizes_embed_carrier {C : container} (v : Semantic C) :
  realizes_carrier (embed_carrier v) v.
Proof. apply nu_le_refl. Qed.

Lemma total_embed {C : finitary_container}
  (v : Semantic (fc_container C)) :
  Total (embed v).
Proof. apply total_embed_carrier. Qed.

Lemma realizes_embed {C : finitary_container}
  (v : Semantic (fc_container C)) :
  Realizes (embed v) v.
Proof. apply realizes_embed_carrier. Qed.

(** Realization is preserved when information is discarded.  The converse
    is intentionally false: a pending layer realizes every semantic value but
    may refine to a returned layer incompatible with a chosen value. *)
Lemma realizes_carrier_downward {C : container}
  (d1 d2 : nu (pc_container (point_container C)))
  (v : Semantic C) :
  nu_le (point_container C) d1 d2 ->
  realizes_carrier d2 v ->
  realizes_carrier d1 v.
Proof.
  unfold realizes_carrier.
  intros Hle Hrealizes; eapply nu_le_trans; eauto.
Qed.

Lemma realizes_downward {C : finitary_container}
  (d1 d2 : Partial C) (v : Semantic (fc_container C)) :
  d1 ⊑ d2 ->
  Realizes d2 v ->
  Realizes d1 v.
Proof.
  unfold Realizes, realizes_carrier.
  intros Hle Hrealizes.
  change
    (nu_le (point_container (fc_container C))
      (value_carrier d1) (value_carrier d2)) in Hle.
  eapply nu_le_trans; eauto.
Qed.
