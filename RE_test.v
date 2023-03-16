(** * RE extraction test. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
  Nat
  String
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

From algco Require Import aCPO axioms cpo eR misc order tactics conat colist prod cotrie.

Local Open Scope bool_scope.
Local Open Scope order_scope.

(* (01 + 10)*1 *)
Definition test_lang : RE bool :=
  RE_concat (RE_star (RE_union (RE_concat (RE_single false) (RE_single true))
                        (RE_concat (RE_single true) (RE_single false)))) (RE_single true).

Definition matches (l : list bool) : bool :=
  RE_match test_lang l.

From Coq Require Import ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "extract/re/RE.hs" matches.
