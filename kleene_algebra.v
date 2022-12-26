
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Vector
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
  Nat
  Fin
.
Local Open Scope program_scope.
Local Open Scope equiv_scope.
Import ListNotations.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From algco Require Import aCPO axioms cpo misc order tactics conat colist prod.

Local Open Scope bool_scope.
Local Open Scope order_scope.

Class KleeneAlgebra (A : Type) `{OType A} : Type :=
  { plus : A -> A -> A
  ; mult : A -> A -> A
  ; star : A -> A
  ; zero : A
  ; one : A
  }.

Class KleeneAlgebraLaws (A : Type) `{KleeneAlgebra A} : Prop :=
  { plus_assoc : forall a b c, plus a (plus b c) === plus (plus a b) c
  ; mult_assoc : forall a b c, mult a (mult b c) === mult (mult a b) c
  ; plus_comm : forall a b, plus a b === plus b a
  ; mult_plus_distr_l : forall a b c, mult a (plus b c) === plus (mult a b) (mult a c)
  ; mult_plus_distr_r : forall a b c, mult (plus a b) c === plus (mult a c) (mult b c)
  ; plus_zero_l : forall a, plus zero a === a
  ; plus_zero_r : forall a, plus a zero === a
  ; mult_zero_l : forall a, mult zero a === zero
  ; mult_zero_r : forall a, mult a zero === zero
  ; mult_one_l : forall a, mult one a === a
  ; mult_one_r : forall a, mult a one === a
  ; plus_idempotent : forall a, plus a a === a
  ; star_1 : forall a, plus one (mult a (star a)) ⊑ star a
  ; star_2 : forall a, plus one (mult (star a) a) ⊑ star a
  ; star_3 : forall a x, mult a x ⊑ x -> mult (star a) x ⊑ x
  ; star_4 : forall a x, mult x a ⊑ x -> mult x (star a) ⊑ x
  }.
