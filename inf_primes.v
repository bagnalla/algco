(** Taken from https://gist.github.com/poizan42/c7017e66f921783c0e52
    with minor modifications. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.PArith.BinPos.
From Coq Require Import Lia.

Definition Z_ens := Ensemble Z.
(* Print Finite. *)
(* Print Empty_set. *)
Definition is_empty_set U A := forall x, ~(In U A x).
Inductive Finite' (U : Type) : Ensemble U -> Prop :=
    Empty_is_finite' : forall A : Ensemble U, 
                      is_empty_set U A -> Finite' U A
  | Union_is_finite' : forall A : Ensemble U,
                      Finite' U A ->
                      forall x : U, ~ In U A x -> Finite' U (Add U A x).

Lemma finite_to_finite' : forall (U: Type) (A: Ensemble U),
  Finite U A -> Finite' U A.
Proof.
  intros.
  induction H.
  apply Empty_is_finite'.
  unfold is_empty_set.
  intros.
  firstorder.
  apply Union_is_finite'.
  firstorder.
  exact H0.
Qed.

Lemma finite'_empty_cases : forall (U: Type) (A: Ensemble U),
  Finite' U A -> is_empty_set U A \/ ~(is_empty_set U A).
Proof.
  intros.
  induction H.
  left.
  exact H.
  right.
  unfold not; intros.
  absurd (In U (Add U A x) x).
  firstorder.
  intuition.
Qed.

Lemma finite'_ne_inhabited : forall (U: Type) (A: Ensemble U),
  Finite' U A -> ~(is_empty_set U A) -> exists x, In U A x.
Proof.
  intros U A A_finite A_nonempty.
  induction A_finite.
  firstorder.
  exists x.
  intuition.
Qed.

Lemma Zdivide_Zabs_r a b : (a | b) -> (a | Z.abs b).
Proof.
  intros.
  elim Z.abs_eq_or_opp with (n := b).
  intros.
  rewrite H0.
  exact H.
  intros.
  rewrite H0.
  apply Zdivide_opp_r.
  exact H.
Qed.

Lemma Zdivide_Zabs_inv_r a b : (a | Z.abs b) -> (a | b).
Proof.
  intros.
  elim Z.abs_eq_or_opp with (n := b).
  intros.
  rewrite <- H0.
  exact H.
  intros.
  apply Zdivide_opp_r_rev.
  rewrite <- H0.
  exact H.
Qed.

Lemma mul_fin_set_divides : forall A:Z_ens,
  Finite' Z A -> (forall m:Z, In Z A m -> m <> 0) ->
    exists n:Z, n > 0 /\ forall m:Z, (In Z A m -> (m | n)).
Proof.
  intros A A_finite.
  apply Finite'_ind with (P := fun U =>
    (forall m:Z, In Z U m -> m <> 0) ->
    exists n:Z, n > 0 /\ forall m : Z, In Z U m -> (m | n)).
  (* Induction start *)
  intros A0 A0_empty _.
  exists 1.
  split.
  firstorder.
  intros m H.
  absurd (In Z A0 m).
  apply A0_empty.
  exact H.
  (* Induction step *)
  intros A0 A0_finite IH n_add n0_nin_A0 A0_nonzero.
  elim IH.
  intros n_mul IHdivides.
  clear IH.
  exists (n_mul * Z.abs n_add).
  split.
  apply Z.lt_gt.
  apply Z.mul_pos_pos.
  intuition.
  apply Z.abs_pos.
  { apply A0_nonzero; right; constructor. }
  intros.
  compare m n_add.
    (* m = n_add *)
    intros m_eq_n_mul.
    rewrite m_eq_n_mul.
    apply Z.divide_mul_r.
    apply Zdivide_Zabs_r.
    intuition.
    (* m <> n_add *)
    intros.
    apply Z.divide_mul_l.
    inversion H.
    apply IHdivides.
    exact H0.
    inversion H0.
    { apply IHdivides.
      inversion H; subst; auto.
      intuition. }
    apply Pos.eq_dec.
    apply Pos.eq_dec.
  intros m m_in_A0.
  apply A0_nonzero.
  intuition.
  exact A_finite.
Qed.

Lemma ex_rel_prime : forall P:Z_ens,
  (Finite' Z P /\ forall p:Z, In Z P p -> prime p) ->
  exists n:Z, n > 1 /\ (forall p:Z, In Z P p -> rel_prime p n).
Proof.
  intros P H.
  inversion H as [P_finite P_primes].
  clear H.
  elim finite'_empty_cases with (A := P).
  intros P_empty.
  exists 2.
  { split; try lia.
    intros p Hp.
    apply rel_prime_le_prime.
    { apply prime_2. }
    firstorder. }
  intros P_inhabited.
  apply finite'_ne_inhabited in P_inhabited.
  elim mul_fin_set_divides with (A := P).
  intros n all_divides'.
  inversion all_divides' as [n_pos all_divides]; clear all_divides'.
  exists (n+1).
  split.
  intuition.
  
  intros p p_in_P.
  pose proof p_in_P as prime_p.
  apply P_primes in prime_p.
  (* Show that p is positive *)
  pose proof prime_p as prime_p'.
  apply prime_alt in prime_p'.
  unfold prime' in prime_p'.
  inversion prime_p' as [p_geq_1 _].
  clear prime_p'.

  assert (n mod p = 0) as n_mod_p_eq_0.
    apply Zdivide_mod; apply all_divides; apply p_in_P.
  assert ((n+1) mod p = 1) as np1_mod_p_eq_1.
    assert (1 mod p = 1) as one_mod_p_eq_1.
    apply Zmod_1_l; exact p_geq_1.
    rewrite <- one_mod_p_eq_1 at 2; clear one_mod_p_eq_1.
    rewrite Zplus_mod.
    rewrite n_mod_p_eq_0.
    rewrite Z.add_0_l.
    rewrite Zmod_mod.
    apply eq_refl.
  apply rel_prime_sym.
  apply rel_prime_mod_rev.
  { lia. }
  rewrite np1_mod_p_eq_1.
  apply rel_prime_1.
  exact P_finite.
  intros p p_in_P.
  { intuition; subst.
    apply P_primes in p_in_P.
    apply not_prime_0; auto. }
  exact P_finite.
  exact P_finite.
Qed.

Lemma ex_maximal_element : forall (A : Ensemble Z), Finite' Z A ->
  (exists m, In Z A m) ->
  exists N, In Z A N /\ (forall n, In Z A n -> n <= N).

Proof.
  intros A A_is_finite.
  (* Check Finite'_ind. *)
  apply Finite'_ind with (P :=
    fun A => (exists m, In Z A m) ->
      exists N : Z, In Z A N /\ (forall n : Z, In Z A n -> n <= N)).
  (* Induction start, A0: empty set *)
  clear A A_is_finite; intros.
  firstorder.
  (* Induction step *)
  clear A A_is_finite;
    intros A0 A0_finite A0_ME_exists' n_add n_add_new add_non_empty.
  clear add_non_empty.
  
  (* - A0 is either empty or non-empty - *)
  inversion A0_finite as [A0_empty | A1 A1_finite n' n'_nin_A1 A1_A0_rel].
  (* A0 is empty, the new element must be the maximal element, as it's
   * the only element. *)
  exists n_add.
  split.
  apply Union_intror.
  firstorder.
  intros n0 n0_in_Znew.
  inversion n0_in_Znew.
  unfold is_empty_set in H.
  firstorder.
  inversion H1.
  intuition.
  (* A0 is non-empty, it contains n' *)
  assert (exists m : Z, In Z A0 m) as A0_non_empty.
  exists n'.
  inversion A1_A0_rel.
  apply Union_intror.
  apply In_singleton.
  (* Get rid of the knowledge of the extra element *)
  rewrite A1_A0_rel.
  clear A1 n' A1_finite n'_nin_A1 A1_A0_rel.

  (* Use our knowledge to get a useful induction hypothesis. *)
  apply A0_ME_exists' in A0_non_empty.
  rename A0_non_empty into A0_ME_exists.
  clear A0_ME_exists'.
  elim A0_ME_exists.
  clear A0_ME_exists.
  intros n0 n0_is_ME.

  inversion n0_is_ME as [n0_in_A0 n0_is_UB]; clear n0_is_ME.
  (* The actual element we claim is the maximal element is max(n_add, n0)*)
  exists (Z.max n_add n0).
  split.

  (** Show that the element is in A **)
  elim Z.lt_total with (n := n_add) (m := n0).
  (* n_add < n0 *)
  intros.
  rewrite Z.max_r.
  apply Union_introl.
  exact n0_in_A0.
  intuition.
  (* n_add = n0 \/ n0 < n_add *)
  intros.
  elim H; clear H.
  (* n_add = n0 *)
  intros.
  rewrite <- H in n0_in_A0.
  contradiction.
  (* n0 < n_add *)
  intros.
  rewrite Z.max_l.
  apply Union_intror.
  firstorder.
  intuition.
  
  (** Show that the element is an upper bound **)
  intros n n_in_Anew.
  elim Z.lt_total with (n := n_add) (m := n0).
  (* n_add < n0 *)
  intros.
  compare n n_add.
  (* n = n_add *)
  intros n_eq_n_add.
  rewrite Z.max_r.
  intuition.
  intuition.
  (* n <> n_add *)
  intros n_neq_n_add.
  rewrite Z.max_r.
  apply n0_is_UB.
  inversion n_in_Anew.
  trivial.
  inversion H0.
  exfalso.
  firstorder.
  intuition.
  apply Pos.eq_dec.
  apply Pos.eq_dec.
  (* n_add = n0 \/ n0 < n_add  *)
  intros.
  elim H.
  (* n_add = n0 *)
  clear H.
  intros.
  rewrite <- H in n0_in_A0.
  contradiction.
  (* n0 < n_add *)
  clear H.
  intros.
  rewrite Z.max_l.
  inversion n_in_Anew; clear x H1.
  { apply n0_is_UB in H0; lia. }
  inversion H0.
  intuition.
  intuition.
  (* Finally A is finite *)
  exact A_is_finite.
Qed.

Definition all_primes_leq (ub: Z) : Ensemble Z :=
  fun p: Z => p <= ub /\ prime p.

Lemma all_primes_leq_finite : forall ub, Finite' Z (all_primes_leq ub).

Proof.
  assert (forall p:Z, p <= 1 -> Finite' Z (all_primes_leq p)) as
    no_primes_finite.
  intros.
  apply Empty_is_finite'.
  unfold is_empty_set; intros n.
  unfold not; intros n_in_apleq_p.
  inversion n_in_apleq_p as [n_leq_p n_prime].
  inversion n_prime as [n_geq_1 _].
  intuition.

  intros.
  induction ub.
  (* n = 0 *)
  apply no_primes_finite.
  intuition.
  (* n > 0 *)
  apply Pos.peano_ind with (P :=
    fun n => Finite' Z (all_primes_leq (Z.pos n))).
  (* n = 1 *)
  apply no_primes_finite.
  intuition.
  (* n > 1, induction step *)
  intros n0 IH.
  set (n := Z.pos (Pos.succ n0)).
  assert (n = Z.succ (Z.pos n0)) as n_eq_succ_n0.
    rewrite <- Pos2Z.inj_succ.
    trivial.
  assert (n > Z.pos n0) as n_geq_n0.
    rewrite n_eq_succ_n0.
    apply Z.lt_gt.
    apply Z.lt_succ_diag_r.

  elim prime_dec with (p := n).
  (* n is prime *)
  intros n_prime.
  replace (all_primes_leq n) with (Add Z (all_primes_leq (Z.pos n0)) n).
  apply Union_is_finite'.
  assumption.
  unfold not, In; intros H.
  inversion H as [n_leq_n0 _].
  firstorder.
  apply Extensionality_Ensembles.
  split.
  split.
  (* inclusion new set -> all_primes_leq *)
  (* Proof that x <= n *)
    inversion H as [_1 x_in_apl _2 | _1 x_is_n _2].
    clear _1 _2 H.
    (* Case In Z (all_primes_leq (Z.pos n0)) x *)
    inversion x_in_apl as [x_leq_n0 _].
    apply Zgt_asym.
    apply Zgt_le_trans with (m := Z.pos n0).
    exact n_geq_n0.
    exact x_leq_n0.
    clear _1 _2 H.
    (* Case In Z (Singleton Z n) x *)
    inversion x_is_n as [n_eq_x].
    apply Z.le_refl.
  (* Proof that x is prime *)
    inversion H as [_1 x_in_apl _2 | _1 x_is_n _2].
    clear _1 _2 H.
    inversion x_in_apl as [_ x_is_prime].
    exact x_is_prime.
    clear _1 _2 H.
    inversion x_is_n.
    exact n_prime.
  (* inclusion all_primes_leq -> new set *)
  unfold Included.
  intros x x_in_apl.
  inversion x_in_apl as [x_leq_n x_prime].
  clear x_in_apl.
  compare x n.
    (* x = n *)
    intros x_eq_n.
    apply Union_intror.
    rewrite x_eq_n.
    apply In_singleton.
    (* x <> n *)
    intros x_neq_n.
    apply Union_introl.
    split.
    (* Show x <= Z.pos n0 *)
    apply Zgt_succ_le.
    rewrite <- n_eq_succ_n0.
    apply Z.lt_gt.
    elim not_Zeq with (n := x) (m := n).
    trivial.
    intros n_lt_x.
    apply Z.lt_gt in n_lt_x.
    contradiction.
    exact x_neq_n.
    (* show x is prime *)
    exact x_prime.
    apply Pos.eq_dec.
    apply Pos.eq_dec.

  (* n is not prime *)
  intros n_neq_prime.
  replace (all_primes_leq n) with (all_primes_leq (Z.pos n0)).
  exact IH.
  apply Extensionality_Ensembles. 
  split.
  (* In Z (all_primes_leq (Z.pos n0)) x -> In Z (all_primes_leq n) *)
  split.
  inversion H as [x_leq_n0 _].
  apply Zgt_asym.
  apply Zgt_le_trans with (m := Z.pos n0).
  exact n_geq_n0.
  exact x_leq_n0.
  inversion H as [_ x_prime].
  exact x_prime.
  (* In Z (all_primes_leq n) -> In Z (all_primes_leq (Z.pos n0)) x *)
  split.
  inversion H as [x_leq_n x_prime].
  compare x (Z.pos n0).
  intros x_eq_n0.
  apply Z.eq_le_incl.
  exact x_eq_n0.
  intros x_neq_n0.
  apply Zgt_succ_le.
  rewrite <- n_eq_succ_n0.
  elim Zle_lt_or_eq with (n := x) (m := n).
  apply Z.lt_gt.
  intros x_eq_n.
  rewrite x_eq_n in x_prime.
  contradiction.
  exact x_leq_n.
  apply Pos.eq_dec.
  apply Pos.eq_dec.
  apply H.

  (* At last show that the set of negative primes is finite
    (because it's empty...)*)
  apply no_primes_finite.
  apply Z.lt_le_incl.
  apply Z.lt_trans with (m := 0).
  apply Zlt_neg_0.
  apply Z.lt_0_1.
Qed.

Lemma ex_prime_divisor : forall n, n > 1 -> exists p, prime p /\ (p | n).

Proof.
  intros n n_pos.
  induction n.
  absurd (0 > 1).
  intuition.
  assumption.
  (* Z.pos p > 0 *)
  (* A suffienctly strong IH (total induction) *)
  cut (forall n1, 1 < n1 <= Z.pos p -> exists p, prime p /\ (p | n1)).
  intros.
  apply H.
  split.
  apply Z.gt_lt.
  exact n_pos.
  apply Z.le_refl.
  apply Pos.peano_ind with (P := fun np =>
    forall n1, 1 < n1 <= Z.pos np -> exists p, prime p /\ (p | n1)).
  intros.
  exfalso.
  intuition.

  (* Induction "step" *)
  intros p0 IH n1 n1_n2_rel.
  set (n0 := Z.pos p0).
  set (n2 := Z.pos (Pos.succ p0)).
  fold n0 in IH.
  fold n2 in n1_n2_rel.
  elim prime_dec with (p := n1).
  (* n1 is prime *)
  intros n1_prime.
  exists n1.
  split.
  exact n1_prime.
  apply Z.divide_refl.
  (* n1 is not prime *)
  intros n1_nprime.
  cut (exists n, 1 < n < n1 /\ (n | n1)).
  intros.
  elim H; clear H.
  intros n n_div_of_n1.
  cut (exists p1, prime p1 /\ (p1 | n)).
  intros H.
  elim H; clear H.
  intros p2 p2_pf_of_n.
  exists p2.
  split.
  apply p2_pf_of_n.
  apply Z.divide_trans with (m := n).
  apply p2_pf_of_n.
  apply n_div_of_n1.
  apply IH.
  split.
  firstorder.
  assert (n2 = Z.succ n0) as n2_eq_n0p1.
  unfold n2, n0.
  rewrite Pos2Z.inj_succ. 
  apply eq_refl.
  rewrite n2_eq_n0p1 in n1_n2_rel; clear n2_eq_n0p1 n2.
  elim Z.le_succ_r with (n := n1) (m := n0).
  intros H _.
  inversion n1_n2_rel as [_ H0].
  apply H in H0; clear H.
  elim H0; clear H0.
  (* case n1 <= n0 *)
  intros n1_leq_n0.
  apply Z.lt_le_incl.
  apply Z.lt_le_trans with (m := n1).
  apply n_div_of_n1.
  exact n1_leq_n0.
  (* case n1 = n0 + 1 *)
  intros n1_eq_n0p1.
  rewrite n1_eq_n0p1 in n_div_of_n1; clear n1_eq_n0p1.
  apply Z.lt_succ_r.
  apply n_div_of_n1.

  apply not_prime_divide.
  apply n1_n2_rel.
  exact n1_nprime.

  (* Negative numbers (contradiction) *)
  absurd (Z.neg p > 0).
  apply Pos2Z.neg_is_nonpos.
  firstorder.
Qed.

(*** There is an infinite number of primes ***)
(* Formulation 1: Given the set of all prime number <= an integer,
 *   then we can find a prime not in the set. *)
Theorem ex_prime_gt_ens : forall n, exists p,
  prime p /\ ~(In Z (all_primes_leq n) p).

Proof.
  intros n.
  elim ex_rel_prime with (P := all_primes_leq n).
  intros n2 H.
  inversion H as [n2_gt_1 n2_rel_prime]; clear H.
  elim ex_prime_divisor with (n := n2).
  intros p p_pf.
  exists p.
  split.
  apply p_pf.
  unfold not; intros p_in_apl.
  absurd (rel_prime p p).
  unfold rel_prime, not.
  intros p_rel_prime_self.
  elim Z.eq_dec with (x := p) (y := 1).
  intros p_eq_1.
  { subst. destruct p_pf as [HC ?].
    apply not_prime_1; auto. }
  intros p_neq_1.
  elim Zis_gcd_unique with (a := p) (b := p) (c := p) (d := 1).
  trivial.
  { intro; subst.
    destruct p_pf as [[] ?]; lia. }
  apply Zis_gcd_refl.
  exact p_rel_prime_self.
  cut (rel_prime p n2).
  intros p_n2_rp.
  apply rel_prime_sym in p_n2_rp.
  apply rel_prime_div with (p := n2).
  exact p_n2_rp.
  apply p_pf.
  apply n2_rel_prime.
  exact p_in_apl.
  apply n2_gt_1.

  split.
  apply all_primes_leq_finite.
  firstorder.
Qed.

(* Formulation 2: For every integer n there exists a prime larger than n.*)
Theorem ex_prime_gt : forall n,
  exists p, p > n /\ prime p.

Proof.
  intros n.
  (*cut (forall p, ~(In Z (all_primes_leq n) p) -> p > n).*)
  elim ex_prime_gt_ens with (n := n).
  intros.
  inversion H as [x_prime x_nin_apl]; clear H.
  exists x.
  split.
  unfold In, all_primes_leq in x_nin_apl.
  elim Z.lt_ge_cases with (n := n) (m := x).
  intros.
  apply Z.lt_gt.
  exact H.
  intros.
  absurd (x <= n /\ prime x).
  exact x_nin_apl.
  firstorder.
  exact x_prime.
Qed.

(* Formulation 3: For every set of prime numbers there exists a prime
     not in the set. *)
Theorem ex_other_prime : forall P:Z_ens,
  (Finite' Z P /\ forall p:Z, In Z P p -> prime p) ->
  exists q:Z, prime q /\ ~(In Z P q).

Proof.
  intros.
  inversion H as [P_finite P_primes]; clear H.
  (* - P is either empty or non-empty - *)
  inversion P_finite as [P_empty | P1 P1_finite p' p'_nin_P1 P1_P_rel].
  (* P is empty, 2 is prime.. *)
  exists 2.
  split.
  exact prime_2.
  firstorder.
  (* P is nonempty. *)
  assert (exists m : Z, In Z P m) as P_nonempty.
  exists p'.
  inversion P1_P_rel.
  intuition.
  (* Get a maximal element *)
  assert (exists N, In Z P N /\ (forall n, In Z P n -> n <= N))
    as ex_maximal_element'.
  apply ex_maximal_element.
  exact P_finite.
  exact P_nonempty.

  elim ex_maximal_element'.
  rewrite P1_P_rel.
  clear p' p'_nin_P1 P1_P_rel P1 P1_finite ex_maximal_element'.

  (* Introduce the maximal element *)
  intros p_max H.
  inversion H as [p_max_in_P p_max_ME]; clear H.
  elim ex_prime_gt with (n := p_max).
  intros q q_max_prime.
  exists q.
  split.
  apply q_max_prime.
  unfold not; intros q_in_P.
  absurd (q <= p_max).
  firstorder.
  firstorder.
Qed.
