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

From algco Require Import aCPO axioms misc colist cpo order tactics.

Local Open Scope order_scope.

CoFixpoint nats (n : nat) : colist nat := cocons n (nats (S n)).

Definition asieve_aux' : alist nat -> alist nat :=
  afold anil (@atau nat) (fun n l' => acons n (filter (fun m => negb (m mod n =? O)) l')).

Definition asieve_aux : alist nat -> colist nat :=
  afold conil (@cotau nat) (fun n l' => cocons n (cofilter (fun m => negb (m mod n =? O)) l')).

Lemma asieve_aux_inj_asieve_aux' (l : alist nat) :
  asieve_aux l = inj (asieve_aux' l).
Proof.
  unfold asieve_aux, asieve_aux'.
  induction l; simpl; auto.
  - rewrite IHl; auto.
  - rewrite IHl, cofilter_inj_filter; auto.
Qed.

#[global]
  Instance monotone_asieve_aux : Proper (leq ==> leq) asieve_aux.
Proof with eauto with colist order aCPO.
  apply monotone_afold...
  intro; apply continuous_monotone, continuous_compose...
Qed.
#[global] Hint Resolve monotone_asieve_aux : colist.

Definition sieve_aux : colist nat -> colist nat := co asieve_aux.

(* Bad definition. *)
(* CoFixpoint sieve (n : nat) : colist nat := *)
(*   cocons n (cotau (cofilter (fun m => m mod n =? O) (cotau (sieve (S n))))). *)

Definition sieve : colist nat := sieve_aux (nats 2).
Definition sieve_list (n : nat) : colist nat := asieve_aux (prefix n (nats 2)).

Lemma alists_exists_nats n m k :
  m <= n ->
  n < m + k ->
  alist_exists (eq n) (prefix k (nats m)).
Proof.
  revert n m; induction k; intros n m H0 H1; simpl.
  { lia. }
  destruct (Nat.eqb_spec n m); subst.
  - constructor; auto.
  - apply alist_exists_tl; auto; apply IHk; lia.
Qed.

Lemma nats_exists (n m : nat) :
  m <= n ->
  colist_exists (eq n) (nats m).
Proof with eauto with colist order aCPO.
  intro Hle.
  apply co_intro with (n - m + 1)...
  apply alists_exists_nats; lia.
Qed.

Lemma prime_exists_sieve_aux (n : nat) (l : colist nat) :
  is_prime n ->
  colist_forall (fun m => 1 < m) l ->
  colist_exists (eq n) l ->
  colist_exists (eq n) (sieve_aux l).
Proof with eauto with order colist aCPO.
  intros Hn Hlt Hex.
  apply co_elim in Hex...
  destruct Hex as [k Hex].
  apply co_intro with k...
  apply coop_elim with (i := k) in Hlt...
  revert Hlt Hex.
  unfold ideal; simpl; unfold flip.
  revert Hn; revert n l.
  induction k; simpl; intros n l Hn Hlt Hex.
  { inv Hex. }
  unfold sieve_aux, asieve_aux.
  destruct l; simpl; inv Hex.
  - rewrite co_fold_tau'...
    2: { intro; apply monotone_compose... }
    constructor; auto.
  - rewrite co_fold_cons'...
    2: { intro; apply continuous_compose... }
    constructor; auto.
  - destruct Hlt.
    rewrite co_fold_cons'...
    2: { intro; apply continuous_compose... }
    apply alist_exists_tl; auto.
    rewrite prefix_cofilter.
    apply alist_exists_filter; auto.
    unfold is_prime in Hn.
    destruct Hn as [Hn Hn'].
    apply Hn' in H1; auto.
    destruct (Nat.eqb_spec (n mod n0) O); auto.
Qed.

Lemma prime_exists_sieve_aux_nats (n m : nat) :
  1 < m ->
  m <= n ->
  is_prime n ->
  colist_exists (eq n) (sieve_aux (nats m)).
Proof with eauto with colist order aCPO.
  intros Hlt Hle Hn.
  apply prime_exists_sieve_aux; auto.
  - clear Hle Hn n.
    apply coop_intro...
    intro i; revert Hlt; revert m.
    induction i; intros m Hlt; simpl; unfold flip; simpl.
    { constructor. }
    constructor; auto; apply IHi; lia.
  - apply nats_exists; auto.
Qed.

Lemma is_prime_2_le n :
  is_prime n ->
  2 <= n.
Proof. intros [H ?]; inv H; auto. Qed.

Theorem prime_exists_sieve (n : nat) :
  is_prime n ->
  colist_exists (eq n) sieve.
Proof.
  intro Hn; apply prime_exists_sieve_aux_nats; auto; apply is_prime_2_le; auto.
Qed.

Inductive alist_increasing_from : nat -> alist nat -> Prop :=
| alist_increasing_from_nil : forall n, alist_increasing_from n anil
| alist_increasing_from_tau : forall n l,
    alist_increasing_from n l ->
    alist_increasing_from n (atau l)
| alist_increasing_from_cons : forall n l,
    alist_increasing_from (S n) l ->
    alist_increasing_from n (acons n l).

Lemma alist_forall_sieve_aux_alist l n :
  1 < n ->
  alist_increasing_from n l ->
  alist_forall (fun n0 : nat => n <= n0 /\ (forall m : nat, n <= m -> n0 <> m -> n0 mod m <> 0))
    (asieve_aux' l).
Proof with eauto with colist order aCPO.
  unfold alist_forall; revert n.
  induction l; simpl; intros n Hlt Hl; inv Hl.
  { constructor. }
  { unfold id; auto. }
  split.
  - split; auto; intros n Hle Hneq HC.
    (* a is strictly less than n so can't be a multiple of n. *)
    apply Nat.mod_divides in HC; try lia.
    destruct HC as [c HC]; subst; destruct c; lia.
  - assert (Hlt': 1 < S a) by lia.
    specialize (IHl _ Hlt' H1).
    eapply alist_forall_impl.
    2: { apply alist_forall_afilter; apply IHl. }
    intros n [[H0 H2] H3]; split.
    + apply Bool.negb_true_iff, Nat.eqb_neq in H3; lia.
      (* H3 implies a <> n which together with H0 implies the goal. *)
    + intros m Hle Hneq.
      apply Bool.negb_true_iff, Nat.eqb_neq in H3.
      intro HC; eapply H2.
      2: { eauto. }
      2: { auto. }
      destruct (Nat.eqb_spec a m); subst; lia.
Qed.

Lemma alist_increasing_from_nats n k :
  alist_increasing_from k (prefix n (nats k)).
Proof.
  revert k; induction n; intro k; simpl.
  { constructor. }
  constructor; auto.
Qed.

Lemma prefix_sieve_aux (i : nat) (l : colist nat) :
  prefix i (sieve_aux l) = asieve_aux' (prefix i l).
Proof with eauto with aCPO colist order.
  unfold sieve_aux, asieve_aux, asieve_aux'.
  revert l; induction i; intro l; simpl; auto.
  destruct l; simpl.
  - rewrite co_fold_nil'; auto.
  - rewrite co_fold_tau'...
    2: { intro j; apply monotone_compose... }
    rewrite IHi; auto.
  - rewrite co_fold_cons'...
    2: { intro j; apply continuous_compose... }
    rewrite prefix_cofilter, IHi; auto.
Qed.

Theorem sieve_forall :
  colist_forall is_prime sieve.
Proof with eauto with colist order aCPO.
  apply coop_intro...
  intro n.
  unfold is_prime.
  unfold sieve.
  unfold ideal; simpl; unfold flip.
  rewrite prefix_sieve_aux.
  apply alist_forall_sieve_aux_alist; try lia.
  apply alist_increasing_from_nats.
Qed.
