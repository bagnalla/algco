(** * Semantic values and their lifted partial completion. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
.

From algco.generic Require Import
  container
  container_combinators
  indexed_container
  pointed_container
.

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
