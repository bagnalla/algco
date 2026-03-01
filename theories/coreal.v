(** * Stochastic real number.. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
.
Import ListNotations.
Local Open Scope program_scope.
Local Open Scope equiv_scope.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From algco Require Import
  (* aCPO *)
  axioms
  cpo
  misc
  order
  tactics
.

Local Open Scope order_scope.

Create HintDb cotree.

Definition areal : Type := Z * list bool.

Local Open Scope Z_scope.

(* Definition bits_plus (a b : list bool) : Z * list bool *)

(* Definition areal_plus (a b : areal) : areal := *)
(*   let (n, x) := a in *)
(*   let (m, y) := b in *)
(*   match x with *)
(*   | [] => (n + m, y) *)
(*   | b1 :: bs1 => *)
(*       match y with *)
(*       | [] => (n + m, x) *)
(*       | b2 :: bs2 => match b1 with *)
(*                    | false => areal_plus (n, bs1) (m, bs2) *)
(*       end *)
(*   end. *)
