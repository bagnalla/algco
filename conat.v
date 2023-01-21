(** * Coinductive nats (conats) algebraic CPO. *)

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

From algco Require Import aCPO axioms cpo misc order tactics.

Local Open Scope order_scope.

Create HintDb conat.

CoInductive conat : Type :=
| cozero : conat
| cosucc : conat -> conat.

CoFixpoint omega : conat := cosucc omega.

Definition unf (n : conat) :=
  match n with
  | cozero => cozero
  | cosucc m => cosucc m
  end.

Lemma unf_eq (n : conat) : n = unf n.
Proof. destruct n; auto. Qed.

CoInductive conat_le : conat -> conat -> Prop :=
| conat_le_zero : forall n, conat_le cozero n
| conat_le_succ : forall n m,
    conat_le n m ->
    conat_le (cosucc n) (cosucc m).
#[global] Hint Constructors conat_le : conat.

#[global]
  Instance Reflexive_conat_le : Reflexive conat_le.
Proof. cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Transitive_conat_le : Transitive conat_le.
Proof.
  cofix CH; intros x y z Hxy Hyz; inv Hxy.
  - constructor.
  - inv Hyz; constructor; eauto.
Qed.

#[global]
  Instance PreOrder_conat_le : PreOrder conat_le.
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_conat : OType conat :=
  { leq := conat_le }.

Lemma cozero_le (n : conat) :
  cozero ⊑ n.
Proof. constructor. Qed.
#[global] Hint Resolve cozero_le : conat.

Lemma le_omega (n : conat) :
  n ⊑ omega.
Proof.
  revert n; cofix CH; intro n.
  destruct n.
  { constructor. }
  rewrite (@unf_eq omega); constructor; apply CH.
Qed.
#[global] Hint Resolve le_omega : conat.

CoInductive conat_eq : conat -> conat -> Prop :=
| conat_eq_zero : conat_eq cozero cozero
| conat_eq_succ : forall n m,
    conat_eq n m ->
    conat_eq (cosucc n) (cosucc m).

(** Extensionality axiom for conats. *)
Axiom conat_ext : forall (n m : conat), conat_eq n m -> n = m.

Lemma conat_eq_refl (n : conat) :
  conat_eq n n.
Proof. revert n; cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Reflexive_conat_eq : Reflexive conat_eq.
Proof. intro; apply conat_eq_refl. Qed.

Lemma conat_eq_equ (a b : conat) :
  conat_eq a b -> a === b.
Proof.
  intro Hab; split; revert Hab; revert a b; cofix CH;
    intros a b Hab; inv Hab; constructor; apply CH; auto.
Qed.

Lemma equ_conat_eq (a b : conat) :
  a === b -> conat_eq a b.
Proof.
  revert a b; cofix CH; intros a b [Hab Hba].
  inv Hab; inv Hba; constructor; apply CH; split; auto.
Qed.

#[global]
  Instance ExtType_conat : ExtType conat.
Proof. constructor; intros a b Hab; apply conat_ext, equ_conat_eq; auto. Qed.

Fixpoint conat_prefix (i : nat) (n : conat) : nat :=
  match i with
  | O => O
  | S i' => match n with
           | cozero => O
           | cosucc n' => S (conat_prefix i' n')
           end
  end.

Fixpoint coconat_prefix (i : nat) (n : conat) : conat :=
  match i with
  | O => cozero
  | S i' => match n with
           | cozero => cozero
           | cosucc n' => cosucc (coconat_prefix i' n')
           end
  end.

#[global]
  Instance Proper_conat_le : Proper (equ ==> equ ==> flip impl) conat_le.
Proof.
  intros a b [Hab Hba] c d [Hcd Hdc] Hle.
  etransitivity; eauto; etransitivity; eauto.
Qed.

#[global]
  Instance Proper_conat_le'
  : Proper (conat_eq ==> conat_eq ==> flip impl) conat_le.
Proof.
  intros a b Hab c d Hcd Hle.
  apply conat_eq_equ in Hab; destruct Hab.
  apply conat_eq_equ in Hcd; destruct Hcd.
  etransitivity; eauto; etransitivity; eauto.
Qed.

Lemma continuous_cosucc : continuous cosucc.
Proof.
  intros ch Hch s Hs; split.
  - intro i; constructor; apply Hs.
  - intros x Hx.
    destruct x; try solve [specialize (Hx (S O)); inv Hx].
    pose proof Hx as Hx'.
    specialize (Hx' (S O)).
    inv Hx'.
    constructor; apply Hs.
    intro i; specialize (Hx i); inv Hx; auto.
Qed.
#[global] Hint Resolve continuous_cosucc : conat.

(* Inductive alist_le {A} : alist A -> alist A -> Prop := *)
(* | alist_le_conil : forall l, alist_le anil l *)
(* | alist_le_cocons : forall x l1 l2, *)
(*     alist_le l1 l2 -> *)
(*     alist_le (acons x l1) (acons x l2). *)
(* #[global] Hint Constructors alist_le : colist. *)

(* #[global] *)
(*   Instance Reflexive_nat_le : Reflexive le. *)
(* Proof. intro l; induction l; constructor; auto. Qed. *)

(* #[global] *)
(*   Instance Transitive_nat_le : Transitive le. *)
(* Proof. intros a b c Hab Hbc; lia. Qed. *)

(* #[global] *)
(*   Instance PreOrder_alist_le : PreOrder le. *)
(* Proof. constructor; typeclasses eauto. Qed. *)

(* #[global] *)
(*   Instance OType_nat {A} : OType (alist A) := *)
(*   { leq := alist_le }. *)

Lemma O_le (n : nat) :
  O ⊑ n.
Proof. simpl; lia. Qed.
#[global] Hint Resolve O_le : conat.

Lemma le_succ (n m : nat) :
  n ⊑ m -> S n ⊑ S m.
Proof. simpl; lia. Qed.

Lemma conat_prefix_monotone (i : nat) :
  monotone (conat_prefix i).
Proof.
  induction i; intros a b Hab; simpl; try constructor.
  destruct a; inv Hab; try lia. 
  apply le_succ; auto.
Qed.

Lemma conat_prefix_monotone' (n : conat) :
  monotone (fun i => conat_prefix i n).
Proof.
  intro i; revert n; induction i; intros n j Hij; simpl.
  - lia.
  - destruct n.
    + lia.
    + destruct j; simpl.
      * inv Hij.
      * apply le_succ; apply IHi; inv Hij.
        { reflexivity. }
        simpl; lia.
Qed.

Lemma chain_conat_prefix (n : conat) :
  chain (fun i : nat => conat_prefix i n).
Proof.
  apply monotone_chain.
  - apply conat_prefix_monotone'.
  - intro i; simpl; lia.
Qed.

Lemma supremum_cozero (ch : nat -> conat) :
  supremum cozero ch ->
  ch = const cozero.
Proof.
  intros [Hub Hlub]; ext i; unfold const.
  specialize (Hub i); inv Hub; reflexivity.
Qed.

Definition not_cozero (n : conat) : Prop :=
  match n with
  | cozero => False
  | _ => True
  end.

Definition not_O (n : nat) : Prop :=
  match n with
  | O => False
  | _ => True
  end.

Lemma not_cozero_dec (n : conat) : { not_cozero n } + { ~ not_cozero n }.
Proof.
  destruct n.
  - right; intro HC; inv HC.
  - left; constructor.
Qed.

Lemma not_O_dec (n : nat) : { not_O n } + { ~ not_O n }.
Proof.
  destruct n.
  - right; intro HC; inv HC.
  - left; constructor.
Qed.

Definition copred (n : conat) : conat :=
  match n with
  | cozero => cozero
  | cosucc n' => n'
  end.

(** The supremum of a chain of conats. Uses strong LPO. *)
CoFixpoint conat_sup (ch : nat -> conat) : conat :=
  match LPO_option (fun i => not_cozero_dec (ch i)) with
  | Some i => match ch i with
             | cozero => cozero
             | cosucc n => cosucc (conat_sup (copred ∘ ch))
             end
  | None => cozero
  end.

Lemma chain_copred (ch : nat -> conat) :
  chain ch ->
  chain (copred ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try constructor.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
Qed.

#[global]
  Instance monotone_copred : Proper (leq ==> leq) copred.
Proof.
  intro a; revert a; cofix CH; intros x b Hab; inv Hab; auto; constructor.
Qed.

#[global]
  Instance monotone_pred : Proper (leq ==> leq) pred.
Proof.
  intro a; induction a; intros b Hab; inv Hab; simpl; auto; lia.
Qed.

Lemma directed_copred (ch : nat -> conat) :
  directed ch ->
  directed (copred ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_copred; auto.
Qed.

Lemma directed_pred (ch : nat -> nat) :
  directed ch ->
  directed (pred ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_pred; auto.
Qed.

Lemma chain_pred (ch : nat -> nat) :
  chain ch ->
  chain (pred ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try lia.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; lia.
Qed.

Lemma conat_sup_ub (ch : nat -> conat) :
  directed ch ->
  upper_bound (conat_sup ch) ch.
Proof.
  revert ch.
  cofix CH; intros ch Hch i.
  simpl.
  replace (conat_sup ch) with (unf (conat_sup ch)).
  2: { rewrite <- unf_eq; reflexivity. }
  simpl.
  destruct (LPO_option (fun n : nat => not_cozero_dec (ch n))) eqn:Ho.
  - apply LPO_option_some in Ho.
    destruct (ch n) eqn:Hchn.
    + inv Ho.
    + clear Ho.
      destruct (ch i) eqn:Hchi.
      * constructor.
      * constructor.
        replace c0 with ((copred ∘ ch) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        apply CH, directed_copred; auto.
  - apply LPO_option_none with (n:=i) in Ho.
    destruct (ch i); try constructor; exfalso; apply Ho; constructor.
Qed.

Lemma upper_bound_copred_succ (n : conat) (ch : nat -> conat) :
  upper_bound (cosucc n) ch ->
  upper_bound n (copred ∘ ch).
Proof.
  intros Hub i; specialize (Hub i); unfold compose.
  destruct (ch i) eqn:Hchi.
  - constructor.
  - inv Hub; auto.
Qed.

Lemma conat_sup_const (l : conat) :
  conat_eq (conat_sup (fun _ : nat => l)) l.
Proof.
  revert l; cofix CH; intro l.
  rewrite unf_eq; simpl.
  destruct (LPO_option (fun _ : nat => not_cozero_dec l)) eqn:H.
  - apply LPO_option_some in H.
    destruct l; constructor; unfold compose; apply CH.
  - apply LPO_option_none with (n:=O) in H.
    destruct l; try constructor; exfalso; apply H; constructor.
Qed.

Lemma conat_sup_lub (ch : nat -> conat) (ub : conat) :
  directed ch ->
  upper_bound ub ch ->
  conat_sup ch ⊑ ub.
Proof.
  revert ch ub.
  cofix CH; intros ch ub Hch Hub.
  destruct ub.
  - replace ch with (fun _ : nat => cozero).
    + rewrite conat_sup_const; reflexivity.
    + ext i; specialize (Hub i); destruct (ch i); auto; inv Hub.
  - rewrite unf_eq; simpl.
    destruct (LPO_option (fun n : nat => not_cozero_dec (ch n))) eqn:Ho.
    2: { constructor. }
    destruct (ch n) eqn:Hchn.
    + constructor.
    + pose proof Hub as Hub'.
      specialize (Hub n); rewrite Hchn in Hub; inv Hub.
      constructor; apply CH; auto.
      * apply directed_copred; auto.
      * eapply upper_bound_copred_succ; eauto.
Qed.

Lemma conat_sup_supremum (ch : nat -> conat) :
  directed ch ->
  supremum (conat_sup ch) ch.
Proof.
  intro Hch; split.
  - apply conat_sup_ub; auto.
  - intros; apply conat_sup_lub; auto.
Qed.

#[global]
  Instance dCPO_conat : dCPO conat.
Proof.
  constructor; intros ch Hch.
  exists (conat_sup ch); apply conat_sup_supremum; auto.
Qed.
#[global] Hint Resolve dCPO_conat : conat.

Fixpoint nat_inj (n : nat) : conat :=
  match n with
  | O => cozero
  | S n' => cosucc (nat_inj n')
  end.

Lemma nat_inj_conat_prefix_coconat_prefix (n : conat) (i : nat) :
  nat_inj (conat_prefix i n) = coconat_prefix i n.
Proof.
  revert n; induction i; intro n; simpl; auto.
  destruct n; simpl; auto; rewrite IHi; auto.
Qed.

Lemma equ_nat (a b : nat) :
  a === b -> a = b.
Proof. unfold equiv, equ; simpl; lia. Qed.

Lemma supremum_pred_S (n : nat) (ch : nat -> nat) :
  supremum (S n) ch ->
  supremum n (pred ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; lia.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (S y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor; lia.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub.
        apply le_succ; auto; lia. }
    apply Hlub in H; inv H; auto; simpl; lia.
Qed.

Lemma supremum_S' (n : nat) (ch : nat -> nat) :
  supremum (S n) ch ->
  exists i n', ch i = S n' /\ n' ⊑ n.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_O_dec (ch n))).
  - destruct e as [m H].
    specialize (Hub m).
    destruct (ch m) eqn:Hchm.
    + inv H.
    + exists m, n0; split; auto; simpl in *; lia.
  - assert (H: upper_bound O ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n0; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_cosucc' (n : conat) (ch : nat -> conat) :
  supremum (cosucc n) ch ->
  exists i n', ch i = cosucc n' /\ n' ⊑ n.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_cozero_dec (ch n))).
  - destruct e as [m H].
    specialize (Hub m).
    inv Hub.
    + rewrite <- H1 in H; inv H.
    + exists m, n0; auto.
  - assert (H: upper_bound cozero ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n0; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma nat_compact (n : nat) (ch : nat -> nat) :
  directed ch ->
  supremum n ch ->
  exists i, ch i = n.
Proof.
  revert ch; induction n; intros ch Hch Hn.
  - exists O; apply equ_nat; split.
    + apply Hn.
    + simpl; lia.
  - pose proof Hn as Hn'.
    apply supremum_pred_S in Hn.
    apply IHn in Hn; clear IHn.
    2: { apply directed_pred; auto. }
    destruct Hn as [j Hj].
    unfold compose in Hj.
    unfold pred in Hj.
    destruct (ch j) eqn:Hchj; subst.
    + apply supremum_S' in Hn'.
      destruct Hn' as [i [n' [Hi Hn']]]; inv Hn'; exists i; auto.
    + destruct Hn' as [H0 H1]; specialize (H0 j).
      rewrite Hchj in H0; inv H0; exists j; auto.
Qed.

Lemma nat_eq_conat_eq (a b : conat) :
  (forall i, conat_prefix i a = conat_prefix i b) ->
  a = b.
Proof.
  intro H; apply conat_ext.
  revert a b H; cofix CH; intros a b H.
  destruct a.
  - destruct b.
    + constructor.
    + specialize (H (S O)); inv H.
  - destruct b.
    + specialize (H (S O)); inv H.
    + pose proof H as H'.
      specialize (H' (S O)); inv H'.
      constructor; apply CH; intro i; specialize (H (S i)); inv H; auto.
Qed.

Lemma nat_le_conat_le (a b : nat) :
  a ⊑ b ->
  nat_inj a ⊑ nat_inj b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor; apply IHa; auto; simpl; lia.
Qed.

#[global]
  Instance monotone_nat_inj : Proper (leq ==> leq) nat_inj.
Proof. intros a b Hab; apply nat_le_conat_le; auto. Qed.

Lemma conat_le_nat_le (a b : nat) :
  nat_inj a ⊑ nat_inj b ->
  a ⊑ b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - lia.
  - destruct b; inv Hab; apply IHa in H1; simpl in *; lia.
Qed.

Lemma supremum_copred_succ (n : conat) (ch : nat -> conat) :
  supremum (cosucc n) ch ->
  supremum n (copred ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (cosucc y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma conat_prefix_continuous (n : nat) :
  continuous (conat_prefix n).
Proof.
  induction n; intros ch Hch x Hx; unfold compose; simpl.
  { apply supremum_const. }
  destruct x.
  - apply supremum_cozero in Hx.
    apply supremum_const'.
    apply equ_arrow; intro i; rewrite Hx; reflexivity.
  - assert (Hc: supremum x (copred ∘ ch)).
    { eapply supremum_copred_succ; eauto. }
    split.
    + intro i; destruct (ch i) eqn:Hchi; simpl.
      * lia.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i).
        rewrite Hchi in Hub.
        inv Hub.
        apply le_succ.
        apply conat_prefix_monotone; auto.
    + intros ub Hub; destruct ub.
      * assert (H: forall i, ch i = cozero).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); auto; inv Hub. }
        assert (supremum cozero ch).
        { apply supremum_const'; apply equ_arrow; intro i.
          unfold const; rewrite H; reflexivity. }
        eapply supremum_unique in Hx; eauto.
        apply equ_conat_eq in Hx; inv Hx.
      * pose proof Hx as Hx'.
        apply supremum_cosucc' in Hx'.
        destruct Hx' as [i [l' [Hx' Hx'']]].
        pose proof Hub as Hub'.
        specialize (Hub' i).
        simpl in Hub'.
        rewrite Hx' in Hub'.
        clear Hx' i.
        apply le_succ.
        eapply IHn.
        2: { eauto. }
        { apply directed_copred; auto. }
        intro i; specialize (Hub i); simpl in Hub.
        unfold compose.
        destruct (ch i) eqn:Hchi; simpl.
        { destruct n; simpl; lia. }
        { lia. }
Qed.

Lemma coconat_prefix_le (n : conat) (i : nat) :
  coconat_prefix i n ⊑ n.
Proof.
  revert n; induction i; intro n; simpl; try constructor.
  destruct n; constructor; apply IHi.
Qed.

Lemma coconat_prefix_supremum (n : conat) :
  supremum n (fun i => coconat_prefix i n).
Proof.
  split.
  - intro i. apply coconat_prefix_le.
  - revert n; cofix CH; intros n ub Hub.
    destruct ub.
    + specialize (Hub (S O)).
      destruct n; inv Hub; constructor.
    + destruct n.
      * constructor.
      * pose proof Hub as Hub'.
        specialize (Hub' (S O)).
        inv Hub'.
        constructor; apply CH.
        intro i.
        specialize (Hub (S i)); simpl in Hub.
        inv Hub; auto.
Qed.

#[global]
  Instance Compact_nat : Compact nat.
Proof.
  constructor; intros a f Hf Ha.
  apply nat_compact in Ha; auto.
  destruct Ha as [i Ha]; subst; exists i; reflexivity.
Qed.

#[global]
  Instance Dense_conat : Dense conat nat :=
  { incl := nat_inj
  ; ideal := flip conat_prefix }.

#[global]
  Instance aCPO_conat : aCPO conat nat.
Proof.
  constructor.
  - intros a b; split.
    + apply nat_le_conat_le.
    + apply conat_le_nat_le.
  - apply chain_conat_prefix.
  - intros a b Hab i; apply conat_prefix_monotone; auto.
  - apply conat_prefix_continuous.
  - intro a; simpl; unfold compose, flip.
    replace (fun i => nat_inj (conat_prefix i a)) with (fun i => coconat_prefix i a).
    + apply coconat_prefix_supremum.
    + ext i; rewrite nat_inj_conat_prefix_coconat_prefix; reflexivity.
Qed.

Lemma neq_nat_inj_omega (n : conat) :
  (forall m, n <> nat_inj m) ->
  n = omega.
Proof.
  intro H.
  apply ext; split.
  { apply le_omega. }
  revert n H; cofix CH; intros n H.
  destruct n.
  { exfalso; specialize (H O); apply H; reflexivity. }
  rewrite unf_eq; simpl.
  constructor.
  apply CH.
  intros m HC.
  specialize (H (S m)).
  apply H; simpl.
  rewrite HC; reflexivity.
Qed.

Lemma conat_finite_or_omega (n : conat) :
  (exists m, n = nat_inj m) \/ n = omega.
Proof.
  destruct (classic (exists m : nat, n = nat_inj m)); auto.
  right; apply neq_nat_inj_omega.
  intros m HC; subst; apply H; exists m; reflexivity.
Qed.

(* Fixpoint fold {A B} (z : B) (f : A -> B -> B) (l : list A) : B := *)
(*   match l with *)
(*   | [] => z *)
(*   | x :: xs => f x (fold z f xs) *)
(*   end. *)

Fixpoint nat_iter {A} (z : A) (f : A -> A) (n : nat) : A :=
  match n with
  | O => z
  | S n' => f (nat_iter z f n')
  end.

(* Fixpoint iter' {A} (z : A) (f : A -> A) (n : nat) : A := *)
(*   match n with *)
(*   | O => z *)
(*   | S n' => iter' (f z) f n' *)
(*   end. *)

(* Fixpoint iter {A} (z : A) (f : A -> A) (n : nat) : A := *)
(*   match n with *)
(*   | O => z *)
(*   | S n' => iter (f z) f n' *)
(*   end. *)

#[global]
  Instance monotone_nat_iter {A} `{OType A} (z : A) (f : A -> A)
  {Hz : forall n, z ⊑ nat_iter z f n}
  {Hf: Proper (leq ==> leq) f}
  : Proper (leq ==> leq) (nat_iter z f).
Proof.
  intro n; revert Hz Hf; revert z f; induction n;
    intros z f Hz Hf m Hnm; simpl; auto.
  - destruct m; simpl in *; try lia.
    apply Hf.
    apply IHn; auto; lia.
Qed.
#[global] Hint Resolve monotone_nat_iter : conat.

#[global]
 Instance antimonotone_nat_iter {A} `{OType A} (z : A) (f : A -> A)
 {Hz : forall n, nat_iter z f n ⊑ z}
 {Hf: Proper (leq ==> leq) f}
  : Proper (leq ==> flip leq) (nat_iter z f).
Proof.
  unfold flip.
  intro n; revert Hz Hf; revert z f; induction n;
    intros z f Hz Hf m Hnm; simpl; auto.
  - destruct m; simpl in *; try lia.
    apply Hf, IHn; auto; lia.
Qed.
#[global] Hint Resolve antimonotone_nat_iter : conat.

(* #[global] *)
(*   Instance monotone_iter' {A} `{OType A} (z : A) (f : A -> A) *)
(*   {Hz : forall n, z ⊑ iter' z f n} *)
(*   {Hf: forall x i, x ⊑ iter' x f i} *)
(*   : Proper (leq ==> leq) (iter' z f). *)
(* Proof. *)
(*   intro n; revert Hz Hf; revert z f; induction n; *)
(*     intros z f Hz Hf m Hnm; simpl; auto. *)
(*   - destruct m; simpl in *; try lia. *)
(*     apply IHn; auto; try lia. *)
(* Qed. *)
(* #[global] Hint Resolve monotone_iter' : conat. *)

Definition coiter {A} `{PType A} (f : A -> A) : conat -> A :=
  co (nat_iter ⊥ f).

Definition coopiter {A} `{TType A} (z : A) (f : A -> A) : conat -> A :=
  coop (nat_iter ⊤ f).

(** Computation lemmas for coiters. *)

Lemma co_iter_zero {A} `{dCPO A} (z : A) (f : A -> A) :
  co (nat_iter z f) cozero === z.
Proof.
  apply supremum_sup, supremum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma co_iter_succ {A} `{dCPO A} (z : A) (f : A -> A) (n : conat) :
  z ⊑ f z ->
  ( forall n, z ⊑ nat_iter z f n) ->
  continuous f ->
  co (nat_iter z f) (cosucc n) === f (co (nat_iter z f) n).
Proof.
  intros Hz Hfz Hf.
  apply supremum_sup.
  apply shift_supremum'' with (f := fun i => f (nat_iter z f (ideal n i))); auto.
  { apply Hf.
    { apply monotone_directed; auto with conat order.
      apply chain_directed, chain_ideal. }
    { apply dsup_spec.
      { apply monotone_directed; auto with conat order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma co_iter_zero' {A} {o : OType A} `{@ExtType A o} `{@dCPO A o}
  (z : A) (f : A -> A) :
  co (nat_iter z f) cozero = z.
Proof. apply ext, co_iter_zero. Qed.

Lemma co_iter_succ' {A} {o : OType A} `{@ExtType A o} `{@dCPO A o}
  (z : A) (f : A -> A) (n : conat) :
  z ⊑ f z ->
  ( forall n, z ⊑ nat_iter z f n) ->
  continuous f ->
  co (nat_iter z f) (cosucc n) = f (co (nat_iter z f) n).
Proof. intros Hz Hfz Hf; apply ext, co_iter_succ; auto. Qed.

Lemma coiter_succ {A} `{oA: OType A} `{@PType _ oA} `{@dCPO _ oA}
  (f : A -> A) (n : conat) :
  continuous f ->
  coiter f (cosucc n) === f (coiter f n).
Proof.
  intro Hf; apply co_iter_succ; auto.
  - apply bot_le.
  - intro; apply bot_le.
Qed.

Lemma coiter_succ' {A} `{oA: OType A} `{@PType _ oA} `{@dCPO _ oA} `{@ExtType _ oA}
  (f : A -> A) (n : conat) :
  continuous f ->
  coiter f (cosucc n) = f (coiter f n).
Proof. intro Hf; apply ext, coiter_succ; auto. Qed.

CoInductive infinite : conat -> Prop :=
| infinite_succ : forall n, infinite n -> infinite (cosucc n).

Lemma infinite_iff_omega (n : conat) :
  infinite n <-> n = omega.
Proof.
  split.
  - intro Hn.
    destruct (@conat_finite_or_omega n); auto.
    exfalso; destruct H as [m Hm]; subst.
    revert Hn; induction m; intro HC; inv HC; auto.
  - intros ->; cofix CH; rewrite unf_eq; constructor; auto.
Qed.

Extract Constant coiter => "
  \ o p f n ->
    case n of
      Cozero -> bot o p
      Cosucc n' -> f (coiter o p f n')
".

Lemma conat_prefix_omega (i : nat) :
  conat_prefix i omega = i.
Proof. induction i; simpl; auto. Qed.
