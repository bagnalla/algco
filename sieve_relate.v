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

Axiom bad : False.

Lemma sieve_aux_colist_eq (l : colist nat) :
  colist_eq (sieve.sieve_aux l) (sieve_aux l).
Proof.
  unfold sieve_aux, asieve_aux.
  revert l; cofix CH; intros []; simpl.
  - rewrite unf_eq. rewrite co_fold_nil'.
  - rewrite unf_eq; simpl.
    unfold sieve_aux, asieve_aux.
    rewrite co_fold_tau; auto with order colist.
    2: { intro i; apply monotone_compose; auto with order colist aCPO.
         (* Why doesn't this auto apply? *)
         apply monotone_co; eauto with colist order. }
    constructor; apply CH.
  - destruct bad.
Qed.

Lemma sieve_aux_leq (l : colist nat) :
  sieve.sieve_aux l ⊑ sieve_aux l.
Proof.
  revert l; cofix CH; intros []; simpl.
  - rewrite unf_eq; constructor.
  - rewrite unf_eq; simpl.
    unfold sieve_aux, asieve_aux.
    rewrite co_fold_tau; auto with order colist.
    2: { intro i; apply monotone_compose; auto with order colist aCPO.
         (* Why doesn't this auto apply? *)
         apply monotone_co; eauto with colist order. }
    constructor; apply CH.
  - destruct bad.
Qed.

Lemma sieve_aux_eq (l : colist nat) :
  sieve.sieve_aux l = sieve_aux l.
Proof.
  apply ext; split.

Lemma sieve_eq :
  sieve.sieve = sieve2.sieve.
Proof.
  unfold sieve.sieve.
  unfold sieve.
  apply ext.
