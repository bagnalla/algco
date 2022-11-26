(** * Sieve of Eratosthenes with algebraic coinduction. *)
(** * Integer (Z) version. *)

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
Local Open Scope Z_scope.
Import ListNotations.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From algco Require Import aCPO axioms misc conat colist cpo inf_primes order tactics.

Local Open Scope order_scope.

Definition is_prime (n : Z) : Prop :=
  1 < n /\ forall m, 1 < m -> n <> m -> n mod m <> 0.

CoFixpoint nats (n : Z) : colist Z := cocons n (nats (n + 1)).

Definition asieve_aux' : alist Z -> alist Z :=
  afold anil (fun n l' => acons n (filter (fun m => negb (Z.eqb (Z.modulo m n) 0)) l')).

Definition asieve_aux : alist Z -> colist Z :=
  afold conil (fun n l' => cocons n (cofilter (fun m => negb (Z.eqb (Z.modulo m n) 0)) l')).

#[global]
  Instance monotone_asieve_aux : Proper (leq ==> leq) asieve_aux.
Proof. apply monotone_afold; eauto with colist order aCPO. Qed.
#[global] Hint Resolve monotone_asieve_aux : colist.

Definition sieve_aux : colist Z -> colist Z := co asieve_aux.

Definition sieve : colist Z := sieve_aux (nats 2).
Definition sieve_list (n : nat) : colist Z := asieve_aux (prefix n (nats 2)).

Lemma alists_exists_nats (n m : Z) k :
  m <= n ->
  n < m + Z.of_nat k ->
  alist_exists (eq n) (prefix k (nats m)).
Proof.
  revert n m; induction k; intros n m H0 H1; simpl.
  { lia. }
  destruct (Z.eqb_spec n m); subst.
  - constructor; auto.
  - right; apply IHk; lia.
Qed.

Lemma nats_exists (n m : Z) :
  m <= n ->
  colist_exists (eq n) (nats m).
Proof with eauto with colist order aCPO.
  intro Hle.
  apply co_intro with (i := Z.to_nat (n - m + 1))...
  apply alists_exists_nats; lia.
Qed.

Lemma alist_exists_prefix_cofilter {A} (P : A -> bool) (a : A) (l : colist A) (i j : nat) :
  (i <= j)%nat ->
  P a = true ->
  alist_exists (eq a) (prefix i l) ->
  alist_exists (eq a) (prefix j (cofilter P l)).
Proof with eauto with order colist aCPO.
  revert a l j; induction i; simpl; intros a l j Hle Ha Hex.
  { destruct Hex. }
  destruct l.
  { destruct Hex. }
  unfold cofilter, filter_f.
  rewrite cofold_cons'...
  destruct Hex as [?|Hex]; subst.
  - rewrite Ha.
    destruct j; try lia.
    left; auto.
  - destruct j; try lia.
    simpl.
    destruct (P a0) eqn:HPa0.
    + right; apply IHi; auto; lia.
    + specialize (IHi a l (S j)).
      simpl in IHi.
      apply IHi; try lia; auto.
Qed.

Lemma prime_exists_sieve_aux (n : Z) (l : colist Z) :
  is_prime n ->
  colist_forall (fun m => 1 < m) l ->
  colist_exists (eq n) l ->
  colist_exists (eq n) (sieve_aux l).
Proof with eauto with order colist aCPO.
  intros Hn Hall Hex.
  unfold sieve_aux.
  apply co_coP...
  { apply continuous_co... }
  apply co_elim in Hex...
  destruct Hex as [i Hex].
  apply co_intro with i.
  { apply monotone_compose...    
    apply continuous_monotone.
    apply continuous_co... }
  unfold compose; simpl in *; unfold flip in *.
  unfold asieve_aux.
  revert Hall Hex Hn.
  revert l n.
  induction i; simpl; intros l n Hall Hex Hn.
  { destruct Hex. }
  destruct l.
  { destruct Hex. }
  simpl.
  destruct Hex; subst.
  - unfold colist_exists, alist_exists.
    apply colist_exists_intro1; auto.
  - unfold colist_forall, alist_forall in Hall.
    apply colist_forall_cons in Hall.
    destruct Hall as [Hlt Hall].
    apply IHi in H; auto.
    apply co_elim in H...
    destruct H as [j Hex]; simpl in Hex; unfold flip in Hex.
    apply co_intro with (S j)...
    simpl; unfold flip; simpl.
    destruct (Z.eqb_spec n z); subst.
    { left; auto. }
    right.
    eapply alist_exists_prefix_cofilter; auto.
    destruct Hn as [Hn Hn'].
    specialize (Hn' z Hlt n0).
    apply Bool.negb_true_iff.
    destruct (Z.eqb_spec (n mod z) 0); lia.
Qed.

Lemma is_prime_2_le n :
  is_prime n ->
  2 <= n.
Proof. intros [H ?]; lia. Qed.

Lemma prime_exists_asieve_aux_nats (n m : Z) :
  1 < m ->
  m <= n ->
  is_prime n ->
  colist_exists (eq n) (sieve_aux (nats m)).
Proof with eauto with colist order aCPO.
  intros Hlt Hle Hprime.
  generalize (nats_exists Hle); intro H.
  apply prime_exists_sieve_aux; auto.
  apply coop_intro...
  intro i; clear Hprime H Hle n.
  simpl; unfold flip.
  revert Hlt; revert m.
  induction i; intros m Hlt; simpl.
  { apply I. }
  split; auto.
  apply IHi; lia.
Qed.

Theorem sieve_complete (n : Z) :
  is_prime n ->
  colist_exists (eq n) sieve.
Proof with eauto with colist order aCPO.
  intro Hn.
  apply prime_exists_asieve_aux_nats; auto; try lia.
  apply is_prime_2_le; auto.
Qed.

Inductive alist_increasing_from : Z -> alist Z -> Prop :=
| alist_increasing_from_nil : forall n, alist_increasing_from n anil
| alist_increasing_from_cons : forall n l,
    alist_increasing_from (n + 1) l ->
    alist_increasing_from n (acons n l).

Lemma colist_forall_asieve_aux l n :
  1 < n ->
  alist_increasing_from n l ->
  colist_forall (fun n0 : Z => n <= n0 /\ (forall m : Z, n <= m -> n0 <> m -> n0 mod m <> 0))
    (asieve_aux l).
Proof with eauto with colist order aCPO.
  unfold asieve_aux.
  unfold colist_forall, alist_forall; revert n.
  induction l; simpl; intros n Hlt Hl; inv Hl.
  { apply colist_forall_nil. }
  apply colist_forall_intro...
  - split; try lia; intros n Hle Hneq HC.
    (* a is strictly less than n so can't be a multiple of n. *)
    apply Zdiv.Zmod_divides in HC; try lia.
    destruct HC as [c HC]; subst.
    destruct (Z.eqb_spec c 0); subst; nia.
  - assert (Hlt': 1 < a + 1) by lia.
    specialize (IHl _ Hlt' H1).
    eapply colist_forall_impl.
    2: { apply colist_forall_cofilter_conj; apply IHl. }
    intros n [[H0 H2] H3]; split.
    + apply Bool.negb_true_iff, Z.eqb_neq in H3; lia.
      (* H3 implies a <> n which together with H0 implies the goal. *)
    + intros m Hle Hneq.
      apply Bool.negb_true_iff, Z.eqb_neq in H3.
      intro HC; eapply H2.
      2: { eauto. }
      2: { auto. }
      destruct (Z.eqb_spec a m); subst; lia.
Qed.

Lemma alist_increasing_from_nats n k :
  alist_increasing_from k (prefix n (nats k)).
Proof.
  revert k; induction n; intro k; simpl.
  { constructor. }
  constructor; auto.
Qed.

Theorem sieve_sound :
  colist_forall is_prime sieve.
Proof with eauto with colist order aCPO.
  unfold sieve, sieve_aux.
  apply co_coopP...
  (* Why won't this automate? works with typeclass_instances... *)
  { apply cocontinuous_coop... }
  unfold compose.
  apply coop_intro...
  (* This should automate... *)
  { intros x y Hxy; eapply antimonotone_coop... }
  intro i.
  generalize (@colist_forall_asieve_aux (ideal (nats 2) i) 2).
  intro H.
  eapply colist_forall_impl.
  2: { apply colist_forall_asieve_aux with (n := 2); try lia.
       apply alist_increasing_from_nats. }
  unfold is_prime.
  intros z [H0 H1]; split; try lia.
  intros m Hlt Hneq HC.
  eapply H1.
  3: { eauto. }
  lia.
  lia.
Qed.

Lemma generative_nats (n : Z) :
  productive (nats n).
Proof.
  intro i; revert n; induction i; intro n; simpl.
  { split.
    - constructor.
    - intro HC; inv HC. }
  split.
  - constructor; apply IHi.
  - intro HC; inv HC.
    specialize (IHi (n + 1)).
    destruct IHi as [H1 H2].
    apply H2; auto.
Qed.

Lemma colist_exists_inj_alist_exists {A} (a : A) (l : alist A) :
  colist_exists (eq a) (inj l) ->
  alist_exists (eq a) l.
Proof.
  revert a; induction l; simpl; intros x Hex.
  { unfold colist_exists, alist_exists in Hex.
    apply colist_exists_nil in Hex; contradiction. }
  apply colist_exists_elim in Hex.
  destruct Hex as [?|Hex]; subst.
  { left; auto. }
  right; apply IHl; auto.
Qed.

Fixpoint alist_max (l : alist Z) : Z :=
  match l with
  | anil => 0
  | acons n l' => Z.max n (alist_max l')
  end.

Lemma lt_mod_neq_0 (n m : Z) :
  0 < m ->
  0 < n ->
  n < m ->
  n mod m <> 0.
Proof.
  intros H0 H1 h2.
  rewrite Z.mod_eq; try lia.
  generalize (Z.div_small_iff n m); lia.
Qed.

Lemma is_prime_Z (p : Z) :
  Znumtheory.prime p ->
  is_prime p.
Proof.
  intros [Hlt Hprime].
  split.
  - lia.
  - intros m Hm Hneq.
    unfold Znumtheory.rel_prime in Hprime.
    destruct (Z.leb_spec m p).
    { assert (Hmp: m < p) by lia.
      assert (H0: (1 <= m < p)%Z) by lia.
      apply Hprime in H0.
      destruct H0.
      unfold Z.divide in *.
      clear H0 H1.
      intro HC.
      apply Z.mod_divide in HC; try lia.
      unfold Z.divide in HC.
      destruct HC as [z Hzm].
      clear H Hneq.
      specialize (H2 m).
      assert (H3: (exists z : Z, m = (z * m)%Z)).
      { exists 1%Z; lia. }
      assert (H4: (exists z : Z, p = (z * m)%Z)).
      { exists z; lia. }
      specialize (H2 H3 H4).
      destruct H2 as [x Hx].
      destruct (2 <=? x)%Z eqn:H0x.
      { apply Zle_bool_imp_le in H0x.
        assert (1 < x * m)%Z.
        { apply Z.lt_1_mul_pos; lia. }
        lia. }
      apply Z.leb_nle in H0x.
      assert (m = 1%Z).
      { destruct (Z.eqb_spec x 1); subst; lia. }
      lia. }
    apply lt_mod_neq_0; lia.
Qed.

Lemma exists_larger_prime (l : list Z) :
  exists n, is_prime n /\ Forall (fun m => m < n) l.
Proof.
  set (n := fold_right Z.max Z0 l).
  generalize (ex_prime_gt n).
  intros [p [Hgt Hprime]].
  exists p; split.
  - apply is_prime_Z; auto.
  - clear Hprime.
    revert Hgt.
    unfold n.
    clear n.
    revert p.
    induction l; intros p Hgt.
    { constructor. }
    simpl in *; constructor.
    + lia.
    + apply IHl; lia.
Qed.

Lemma exists_larger_prime_alist (l : alist Z) :
  exists n, is_prime n /\ alist_forall (fun m => m < n) l.
Proof.
  generalize (@exists_larger_prime (list_of_alist l)).
  intros [n [Hn Hl]].
  exists n; split; auto.
  apply Forall_alist_of_list; auto.
Qed.

Theorem productive_sieve :
  productive'' sieve.
Proof with eauto with colist order aCPO.
  unfold productive''.
  destruct (@conat_finite_or_omega (colist_length sieve)); auto.
  exfalso.
  destruct H as [m H].
  apply colist_length_inj in H.
  destruct H as [al H].
  generalize (exists_larger_prime_alist al); intros [n [Hn Hall]].
  apply sieve_complete in Hn.
  rewrite H in Hn.
  apply colist_exists_inj_alist_exists in Hn.
  clear H m.
  revert Hn Hall; revert n.
  induction al; intros n Hex Hall.
  { destruct Hex. }
  destruct Hex as [?|Hex]; subst.
  { destruct Hall; lia. }
  destruct Hall as [H0 H1].
  eapply IHal; eauto.
Qed.

(* Definition sorted : colist Z -> Prop := ordered Z.le. *)
Definition increasing : colist Z -> Prop := ordered Z.lt.

Lemma alist_forall_colist_forall_asieve_aux P l :
  alist_forall P l ->
  colist_forall P (asieve_aux l).
Proof.
  unfold asieve_aux.
  induction l; intros Hall; simpl.
  { apply colist_forall_nil. }
  inv Hall.
  apply colist_forall_cons; split; auto.
  apply colist_forall_cofilter'; auto.
Qed.

Lemma ordered_asieve_aux (R : Z -> Z -> Prop) l :
  alist_ordered R l ->
  ordered R (asieve_aux l).
Proof.
  unfold asieve_aux.
  induction l; simpl; intros Hord.
  { apply ordered_nil. }
  inv Hord.
  apply ordered_cons; split.
  - apply colist_forall_cofilter'.
    apply alist_forall_colist_forall_asieve_aux; auto.
  - apply ordered_cofilter; auto.
Qed.

Lemma alist_increasing_asieve_aux (R : Z -> Z -> Prop) (l : alist Z) :
  alist_ordered R l ->
  ordered R (asieve_aux l).
Proof.
  induction l; intro Hord; simpl.
  { apply ordered_nil. }
  inv Hord.
  apply ordered_cons; split.
  - apply colist_forall_cofilter'.
    apply alist_forall_colist_forall_asieve_aux; auto.
  - apply ordered_cofilter.
    apply ordered_asieve_aux; auto.
Qed.

Lemma increasing_sieve_aux (l : colist Z) :
  increasing l ->
  increasing (sieve_aux l).
Proof with eauto with colist order aCPO.
  intro Hinc.
  unfold sieve_aux.
  apply co_coopP...
  { apply cocontinuous_coop... }
  apply coop_intro...
  { apply monotone_antimonotone_compose...
    apply cocontinuous_antimonotone.
    apply cocontinuous_coop... }
  intro i; unfold compose.
  apply coop_elim with (i:=i) in Hinc...
  apply alist_increasing_asieve_aux; auto.
Qed.

Lemma alist_increasing_from_alist_forall_lt n l :
  alist_increasing_from (n + 1) l ->
  alist_forall (Z.lt n) l.
Proof.
  revert n; induction l; intros n Hinc.
  { constructor. }
  inv Hinc; constructor; try lia.
  apply IHl in H1.
  eapply alist_forall_impl.
  2: { eauto. }
  intro x; lia.
Qed.

Lemma alist_increasing_from_increasing n l :
  alist_increasing_from n l ->
  alist_ordered Z.lt l.
Proof.
  revert n; induction l; intros n Hinc.
  { constructor. }
  inv Hinc.
  constructor; eauto.
  apply alist_increasing_from_alist_forall_lt; auto.
Qed.

Lemma increasing_nats (n : Z) :
  increasing (nats n).
Proof with eauto with colist order aCPO.
  apply coop_intro...
  intro i.
  eapply alist_increasing_from_increasing.
  apply alist_increasing_from_nats.
Qed.

Lemma increasing_sieve :
  increasing sieve.
Proof. apply increasing_sieve_aux, increasing_nats. Qed.

Lemma alist_ordered_impl {A} (R1 R2 : A -> A -> Prop) (l : alist A) :
  (forall x y, R1 x y -> R2 x y) ->
  alist_ordered R1 l ->
  alist_ordered R2 l.
Proof.
  induction l; intros HR Hl.
  { constructor. }
  inv Hl; constructor; auto.
  eapply alist_forall_impl.
  - intro x; apply HR.
  - assumption.
Qed.

Lemma ordered_impl {A} (R1 R2 : A -> A -> Prop) (l : colist A) :
  (forall x y, R1 x y -> R2 x y) ->
  ordered R1 l ->
  ordered R2 l.
Proof with eauto with colist order.
  intros HR Hl.
  apply coop_intro...
  intro i; apply coop_elim with (i:=i) in Hl...
  eapply alist_ordered_impl; eauto.
Qed.

Theorem sorted_sieve :
  sorted sieve.
Proof.
  eapply ordered_impl.
  2: { apply increasing_sieve. }
  unfold leq; simpl; lia.
Qed.

Theorem nodup_sieve :
  nodup sieve.
Proof.
  eapply ordered_impl.
  2: { apply increasing_sieve. }
  lia.
Qed.

Definition sieve_f : Z -> colist Z -> colist Z :=
  fun n l' => cocons n (cofilter (fun m => negb (Z.eqb (Z.modulo m n) 0)) l').

Definition sieve' : colist Z -> colist Z :=
  cofold sieve_f.

Definition sieve'' : colist Z := sieve' (nats 2).

Lemma sieve_sieve'' : sieve = sieve''.
Proof. reflexivity. Qed.

From Coq Require Import ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "extract/sieve/Sieve.hs" sieve''.

Lemma sieve_cons a l :
  sieve' (cocons a l) = sieve_f a (sieve' l).
Proof with eauto with colist order aCPO.
  unfold sieve'.
  rewrite cofold_cons'; auto.
  intro x; unfold sieve_f.
  apply continuous_compose...
Qed.

Corollary sieve_correct :
  (forall n, is_prime n -> colist_exists (eq n) sieve) /\
    colist_forall is_prime sieve /\
    sorted sieve /\
    nodup sieve /\
    productive'' sieve.
Proof.
  repeat split.
  - intros n Hn'; apply sieve_complete; auto.
  - apply sieve_sound.
  - apply sorted_sieve.
  - apply nodup_sieve.
  - apply productive_sieve.
Qed.

Print Assumptions sieve_correct.
