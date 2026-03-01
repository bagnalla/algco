(** * Sieve of Eratosthenes with algebraic coinduction. *)

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

From algco Require Import aCPO axioms misc colist cpo order sieve sieve2 tactics.

Local Open Scope order_scope.

(** One way to prove things like this is by the uniqueness lemma, but
that requires doing an ad hoc continuity proof for the non-comorphism
side which is annoying. *)

Lemma sieve_aux_eq (l : colist nat) :
  sieve.sieve_aux l = sieve_aux l.
Proof with eauto with aCPO colist order.
  unfold sieve_aux, asieve_aux.
  apply alist_eq_colist_eq; intro i.
  rewrite <- sieve_aux_prefix.
  revert l; induction i; intro l; simpl.
  { constructor. }
  destruct l; simpl.
  - rewrite co_fold_nil'; constructor.
  - rewrite co_fold_tau'...
    2: { intro; apply monotone_compose... }
    rewrite IHi; reflexivity.
  - rewrite co_fold_cons'...
    2: { intro; apply continuous_compose... }
    rewrite prefix_cofilter, IHi; reflexivity.
Qed.

Lemma sieve_eq :
  sieve.sieve = sieve2.sieve.
Proof. apply sieve_aux_eq. Qed.
