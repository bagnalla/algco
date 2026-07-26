(** * Indexed capability bridge for composed containers. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From algco.generic Require Import
  container_combinators
  indexed_container
.

(** The descriptor retains [finitary_point C] at its type head.  Capability
    resolution therefore receives [C] directly and never has to reconstruct
    finiteness evidence from the projected container carrier. *)
#[global]
Instance DecidableBottom_finitary_point (C : finitary_container) :
  DecidableBottom (finitary_point C).
Proof.
  constructor; exact (@finitary_point_bottom_dec C).
Defined.

#[global]
Instance FinitePositions_finitary_point (C : finitary_container) :
  FinitePositions (finitary_point C).
Proof.
  exact
    (@Build_FinitePositions (finitary_point C)
      (@finitary_point_position_enumeration C)
      (@finitary_point_position_enumeration_complete C)).
Defined.
