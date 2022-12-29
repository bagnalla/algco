(** * Coinductive lists (colists) algebraic CPO. *)

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
Local Open Scope bool_scope.
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

From algco Require Import aCPO axioms conat cpo eR misc order tactics.

Local Open Scope order_scope.

Create HintDb colist.

(* Inductive list (A : Type) : Type := *)
(* | [] : list A *)
(* | acons : A -> list A -> list A. *)

CoInductive colist (A : Type) : Type :=
| conil : colist A (* bottom / divergence *)
| cocons : A -> colist A -> colist A.

Definition unf {A} (l : colist A) :=
  match l with
  | conil => conil
  | cocons x xs => cocons x xs
  end.

Lemma unf_eq {A} (l : colist A) : l = unf l.
Proof. destruct l; auto. Qed.

CoInductive colist_le {A} : colist A -> colist A -> Prop :=
| colist_le_nil : forall l, colist_le conil l
| colist_le_cons : forall x l1 l2,
    colist_le l1 l2 ->
    colist_le (cocons x l1) (cocons x l2).
#[global] Hint Constructors colist_le : colist.

#[global]
  Instance Reflexive_colist_le {A} : Reflexive (@colist_le A).
Proof. cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Transitive_colist_le {A} : Transitive (@colist_le A).
Proof.
  cofix CH; intros x y z Hxy Hyz; inv Hxy.
  - constructor.
  - inv Hyz; constructor; eauto.
Qed.

#[global]
  Instance PreOrder_colist_le {A} : PreOrder (@colist_le A).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_colist {A} : OType (colist A) :=
  { leq := colist_le }.

Lemma conil_le {A} (l : colist A) :
  conil ⊑ l.
Proof. constructor. Qed.
#[global] Hint Resolve conil_le : colist.

#[global]
  Program
  Instance PType_colist {A} : PType (colist A) :=
  { bot := conil }.
Next Obligation. apply conil_le. Qed.

CoInductive colist_eq {A} : colist A -> colist A -> Prop :=
| colist_eq_nil : colist_eq conil conil
| colist_eq_cons : forall x l l',
    colist_eq l l' ->
    colist_eq (cocons x l) (cocons x l').

(** Extensionality axiom for colists. *)
Axiom colist_ext : forall {A} (a b : colist A), colist_eq a b -> a = b.

Lemma colist_eq_refl {A} (t : colist A) :
  colist_eq t t.
Proof. revert t; cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Reflexive_colist_eq {A} : Reflexive (@colist_eq A).
Proof. intro t; apply colist_eq_refl. Qed.

Lemma colist_eq_equ {A} (a b : colist A) :
  colist_eq a b -> a === b.
Proof.
  intro Hab; split; revert Hab; revert a b; cofix CH;
    intros a b Hab; inv Hab; constructor; apply CH; auto.
Qed.

Lemma equ_colist_eq {A} (a b : colist A) :
  a === b -> colist_eq a b.
Proof.
  revert a b; cofix CH; intros a b [Hab Hba].
  inv Hab; inv Hba; constructor; apply CH; split; auto.
Qed.

#[global]
  Instance ExtType_colist {A} : ExtType (colist A).
Proof.
  constructor; intros a b Hab; apply colist_ext, equ_colist_eq; auto.
Qed.

Fixpoint prefix {A} (n : nat) (l : colist A) : list A :=
  match n with
  | O => []
  | S n' => match l with
           | conil => []
           | cocons x xs => x :: prefix n' xs
           end
  end.

Fixpoint coprefix {A} (n : nat) (l : colist A) : colist A :=
  match n with
  | O => conil
  | S n' => match l with
           | conil => conil
           | cocons x xs => cocons x (coprefix n' xs)
           end
  end.

#[global]
  Instance Proper_colist_le {A} : Proper (equ ==> equ ==> flip impl) (@colist_le A).
Proof.
  intros a b [Hab Hba] c d [Hcd Hdc] Hle.
  etransitivity; eauto; etransitivity; eauto.
Qed.

#[global]
  Instance Proper_colist_le' {A}
  : Proper (colist_eq ==> colist_eq ==> flip impl) (@colist_le A).
Proof.
  intros a b Hab c d Hcd Hle.
  apply colist_eq_equ in Hab; destruct Hab.
  apply colist_eq_equ in Hcd; destruct Hcd.
  etransitivity; eauto; etransitivity; eauto.
Qed.

Lemma continuous_cocons {A} (a : A) : continuous (cocons a).
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
#[global] Hint Resolve continuous_cocons : colist.

Inductive list_le {A} : list A -> list A -> Prop :=
| list_le_nil : forall l, list_le [] l
| list_le_cons : forall x l1 l2,
    list_le l1 l2 ->
    list_le (x :: l1) (x :: l2).
#[global] Hint Constructors list_le : colist.

#[global]
  Instance Reflexive_list_le {A} : Reflexive (@list_le A).
Proof. intro l; induction l; constructor; auto. Qed.

#[global]
  Instance Transitive_list_le {A} : Transitive (@list_le A).
Proof.
  intro a; induction a; intros b c Hab Hbc.
  - constructor.
  - inv Hab; inv Hbc; constructor; eapply IHa; eauto.
Qed.

#[global]
  Instance PreOrder_list_le {A} : PreOrder (@list_le A).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_list {A} : OType (list A) :=
  { leq := list_le }.

Lemma nil_le {A} (l : list A) :
  [] ⊑ l.
Proof. constructor. Qed.
#[global] Hint Resolve nil_le : colist.

#[global]
  Program
  Instance PType_list {A} : PType (list A) :=
  { bot := [] }.
Next Obligation. apply nil_le. Qed.

#[global]
  Instance ExtType_list {A} : ExtType (list A).
Proof.
  constructor; intro a; induction a; intros b [H0 H1]; inv H0; inv H1; auto.
  - f_equal; apply IHa; split; auto.
Qed.

Lemma prefix_monotone {A} (n : nat) :
  monotone (@prefix A n).
Proof.
  induction n; intros a b Hab; simpl; try constructor.
  destruct a; inv Hab; constructor; apply IHn; auto.
Qed.

Lemma prefix_monotone' {A} (l : colist A) :
  monotone (fun n => prefix n l).
Proof.
  intro i; revert l; induction i; intros l j Hij; simpl.
  - constructor.
  - destruct l.
    + constructor.
    + destruct j; simpl.
      * inv Hij.
      * constructor; apply IHi; inv Hij.
        { reflexivity. }
        simpl; lia.
Qed.

Lemma chain_prefix {A} (l : colist A) :
  chain (fun n : nat => prefix n l).
Proof.
  apply monotone_chain.
  - apply prefix_monotone'.
  - intro i; simpl; lia.
Qed.

Lemma supremum_conil {A} (ch : nat -> colist A) :
  supremum conil ch ->
  ch = const conil.
Proof.
  intros [Hub Hlub]; ext i; unfold const.
  specialize (Hub i); inv Hub; reflexivity.
Qed.

Definition not_conil {A} (l : colist A) : Prop :=
  match l with
  | conil => False
  | _ => True
  end.

Definition not_nil {A} (l : list A) : Prop :=
  match l with
  | [] => False
  | _ => True
  end.

Lemma not_conil_dec {A} (t : colist A) : { not_conil t } + { ~ not_conil t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
Qed.

Lemma not_nil_dec {A} (t : list A) : { not_nil t } + { ~ not_nil t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
Qed.

Definition step {A} (l : colist A) : colist A :=
  match l with
  | conil => conil
  | cocons _ xs => xs
  end.

Definition lstep {A} (l : list A) : list A :=
  match l with
  | [] => []
  | _ :: xs => xs
  end.

(** The supremum of a chain of colists. Uses strong LPO. *)
CoFixpoint colist_sup {A} (ch : nat -> colist A) : colist A :=
  match LPO_option (fun n => not_conil_dec (ch n)) with
  | Some n => match ch n with
             | conil => conil
             | cocons x xs => cocons x (colist_sup (step ∘ ch))
             end
  | None => conil
  end.

Lemma chain_step {A} (ch : nat -> colist A) :
  chain ch ->
  chain (step ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try constructor.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
Qed.

#[global]
  Instance monotone_step {A} : Proper (leq ==> leq) (@step A).
Proof.
  intro a; revert a; cofix CH; intros x b Hab; inv Hab; auto; constructor.
Qed.

#[global]
  Instance monotone_lstep {A} : Proper (leq ==> leq) (@lstep A).
Proof.
  intro a; induction a; intros b Hab; inv Hab; simpl; auto; constructor.
Qed.

Lemma directed_step {A} (ch : nat -> colist A) :
  directed ch ->
  directed (step ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_step; auto.
Qed.

Lemma directed_lstep {A} (ch : nat -> list A) :
  directed ch ->
  directed (lstep ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_lstep; auto.
Qed.

Lemma chain_lstep {A} (ch : nat -> list A) :
  chain ch ->
  chain (lstep ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try constructor.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
Qed.

Lemma colist_sup_ub {A} (ch : nat -> colist A) :
  directed ch ->
  upper_bound (colist_sup ch) ch.
Proof.
  revert ch.
  cofix CH; intros ch Hch i.
  simpl.
  replace (colist_sup ch) with (unf (colist_sup ch)).
  2: { rewrite <- unf_eq; reflexivity. }
  simpl.
  destruct (LPO_option (fun n : nat => not_conil_dec (ch n))) eqn:Ho.
  - apply LPO_option_some in Ho.
    destruct (ch n) eqn:Hchn.
    + inv Ho.
    + clear Ho.
      destruct (ch i) eqn:Hchi.
      { constructor. }
      { pose proof Hch as Hch'.
        specialize (Hch n i); destruct Hch as [k [H0 H1]].
        rewrite Hchn in H0; inv H0.
        rewrite Hchi in H1; inv H1.
        rewrite <- H4 in H5; inv H5.
        constructor.
        replace c0 with ((step ∘ ch) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        apply CH, directed_step; auto. }
  - apply LPO_option_none with (n:=i) in Ho.
    destruct (ch i); try constructor; exfalso; apply Ho; constructor.
Qed.

Lemma upper_bound_step_cons {A} (x : A) (l : colist A) (ch : nat -> colist A) :
  upper_bound (cocons x l) ch ->
  upper_bound l (step ∘ ch).
Proof.
  intros Hub i; specialize (Hub i); unfold compose.
  destruct (ch i) eqn:Hchi.
  - constructor.
  - inv Hub; auto.
Qed.

Lemma colist_sup_const {A} (l : colist A) :
  colist_eq (colist_sup (fun _ : nat => l)) l.
Proof.
  revert l; cofix CH; intro l.
  rewrite unf_eq; simpl.
  destruct (LPO_option (fun _ : nat => not_conil_dec l)) eqn:H.
  - apply LPO_option_some in H.
    destruct l; constructor; unfold compose; apply CH.
  - apply LPO_option_none with (n:=O) in H.
    destruct l; try constructor; exfalso; apply H; constructor.
Qed.

Lemma colist_sup_lub {A} (ch : nat -> colist A) (ub : colist A) :
  directed ch ->
  upper_bound ub ch ->
  colist_sup ch ⊑ ub.
Proof.
  revert ch ub.
  cofix CH; intros ch ub Hch Hub.
  destruct ub.
  - replace ch with (fun _ : nat => @conil A).
    + rewrite colist_sup_const; reflexivity.
    + ext i; specialize (Hub i); destruct (ch i); auto; inv Hub.
  - rewrite unf_eq; simpl.
    destruct (LPO_option (fun n : nat => not_conil_dec (ch n))) eqn:Ho.
    2: { constructor. }
    destruct (ch n) eqn:Hchn.
    + constructor.
    + pose proof Hub as Hub'.
      specialize (Hub n); rewrite Hchn in Hub; inv Hub.
      constructor; apply CH; auto.
      * apply directed_step; auto.
      * eapply upper_bound_step_cons; eauto.
Qed.

Lemma colist_sup_supremum {A} (ch : nat -> colist A) :
  directed ch ->
  supremum (colist_sup ch) ch.
Proof.
  intro Hch; split.
  - apply colist_sup_ub; auto.
  - intros; apply colist_sup_lub; auto.
Qed.

#[global]
  Instance dCPO_colist {A} : dCPO (@colist A).
Proof.
  constructor; intros ch Hch.
  exists (colist_sup ch); apply colist_sup_supremum; auto.
Qed.
#[global] Hint Resolve dCPO_colist : colist.

Fixpoint inj {A} (l : list A) : colist A :=
  match l with
  | [] => conil
  | x :: xs => cocons x (inj xs)
  end.

Lemma inj_prefix_coprefix {A} (t : colist A) (n : nat) :
  inj (prefix n t) = coprefix n t.
Proof.
  revert t; induction n; intro t; simpl; auto.
  destruct t; simpl; auto; rewrite IHn; auto.
Qed.

Lemma list_le_antisym {A} (a b : list A) :
  a ⊑ b ->
  b ⊑ a ->
  a = b.
Proof.
  intro H; induction H; intro Hle; inv Hle; auto; rewrite IHlist_le; auto.
Qed.

Lemma equ_list {A} (a b : list A) :
  a === b -> a = b.
Proof. intro Heq; apply list_le_antisym; apply Heq. Qed.

Lemma supremum_lstep_cons {A} (a : A) (l : list A) (ch : nat -> list A) :
  supremum (a :: l) ch ->
  supremum l (lstep ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (a :: y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma supremum_acons' {A} (a : A) (l : list A) (ch : nat -> list A) :
  supremum (a :: l) ch ->
  exists i l', ch i = a :: l' /\ l' ⊑ l.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_nil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    inv Hub.
    + rewrite <- H1 in H; inv H.
    + exists n, l1; auto.
  - assert (H: upper_bound [] ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_cocons' {A} (a : A) (l : colist A) (ch : nat -> colist A) :
  supremum (cocons a l) ch ->
  exists i l', ch i = cocons a l' /\ l' ⊑ l.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_conil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    inv Hub.
    + rewrite <- H1 in H; inv H.
    + exists n, l1; auto.
  - assert (H: upper_bound conil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma list_compact {A} (l : list A) (ch : nat -> list A) :
  directed ch ->
  supremum l ch ->
  exists i, ch i = l.
Proof.
  revert ch; induction l; intros ch Hch Hl.
  - exists O; apply equ_list; split; try constructor; apply Hl.
  - pose proof Hl as Hl'.
    apply supremum_lstep_cons in Hl.
    apply IHl in Hl; clear IHl.
    2: { apply directed_lstep; auto. }
    destruct Hl as [j Hj].
    unfold compose in Hj.
    unfold lstep in Hj.
    destruct (ch j) eqn:Hchj; subst.
    + apply supremum_acons' in Hl'.
      destruct Hl' as [i [l' [Hi Hl']]]; inv Hl'; exists i; auto.
    + destruct Hl' as [H0 H1]; specialize (H0 j).
      rewrite Hchj in H0; inv H0; exists j; auto.
Qed.

Lemma list_eq_colist_eq {A} (a b : colist A) :
  (forall i, prefix i a = prefix i b) ->
  a = b.
Proof.
  intro H; apply colist_ext.
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

Lemma list_le_colist_le {A} (a b : list A) :
  a ⊑ b ->
  inj a ⊑ inj b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor; apply IHa; auto.
Qed.

#[global]
  Instance monotone_inj {A} : Proper (leq ==> leq) (@inj A).
Proof. intros a b Hab; apply list_le_colist_le; auto. Qed.

Lemma colist_le_list_le {A} (a b : list A) :
  inj a ⊑ inj b ->
  a ⊑ b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor; apply IHa; auto.
Qed.

Lemma supremum_step_cons {A} (a : A) (l : colist A) (ch : nat -> colist A) :
  supremum (cocons a l) ch ->
  supremum l (step ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (cocons a y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma prefix_continuous {A} (n : nat) :
  continuous (@prefix A n).
Proof.
  induction n; intros ch Hch x Hx; unfold compose; simpl.
  { apply supremum_const. }
  destruct x.
  - apply supremum_conil in Hx.
    apply supremum_const'.
    apply equ_arrow; intro i; rewrite Hx; reflexivity.
  - assert (Hc: supremum x (step ∘ ch)).
    { eapply supremum_step_cons; eauto. }
    split.
    + intro i; destruct (ch i) eqn:Hchi; simpl.
      * constructor.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i).
        rewrite Hchi in Hub.
        inv Hub.
        constructor.
        apply prefix_monotone; auto.
    + intros ub Hub; destruct ub.
      * assert (H: forall i, ch i = conil).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); auto; inv Hub. }
        assert (supremum conil ch).
        { apply supremum_const'; apply equ_arrow; intro i.
          unfold const; rewrite H; reflexivity. }
        eapply supremum_unique in Hx; eauto.
        apply equ_colist_eq in Hx; inv Hx.
      * pose proof Hx as Hx'.
        apply supremum_cocons' in Hx'.
        destruct Hx' as [i [l' [Hx' Hx'']]].
        pose proof Hub as Hub'.
        specialize (Hub' i).
        simpl in Hub'.
        rewrite Hx' in Hub'.
        inv Hub'.
        clear Hx' i.
        constructor.
        eapply IHn.
        2: { eauto. }
        { apply directed_step; auto. }
        intro i; specialize (Hub i); simpl in Hub.
        unfold compose.
        destruct (ch i) eqn:Hchi; simpl.
        { destruct n; constructor. }
        { inv Hub; auto. }
Qed.

Lemma coprefix_le {A} (l : colist A) (n : nat) :
  coprefix n l ⊑ l.
Proof.
  revert l; induction n; intro l; simpl; try constructor.
  destruct l; constructor; apply IHn.
Qed.

Lemma coprefix_supremum {A} (l : colist A) :
  supremum l (fun n => coprefix n l).
Proof.
  split.
  - intro i. apply coprefix_le.
  - revert l; cofix CH; intros l ub Hub.
    destruct ub.
    + specialize (Hub (S O)).
      destruct l; inv Hub; constructor.
    + destruct l.
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
  Instance Compact_list {A} : Compact (list A).
Proof.
  constructor; intros a f Hf Ha.
  apply list_compact in Ha; auto.
  destruct Ha as [i Ha]; subst; exists i; reflexivity.
Qed.
(* #[global] Hint Resolve Compact_list : colist. *)

#[global]
  Instance Dense_colist {A} : Dense (colist A) (list A) :=
  { incl := inj
  ; ideal := flip prefix }.
(* #[global] Hint Resolve Dense_colist : colist. *)

#[global]
  Instance aCPO_colist {A} : aCPO (colist A) (list A).
Proof.
  constructor.
  - intros a b; split.
    + apply list_le_colist_le.
    + apply colist_le_list_le.
  - apply chain_prefix.
  - intros a b Hab i; apply prefix_monotone; auto.
  - apply prefix_continuous.
  - intro a; simpl; unfold compose, flip.
    replace (fun i => inj (prefix i a)) with (fun i => coprefix i a).
    + apply coprefix_supremum.
    + ext i; rewrite inj_prefix_coprefix; reflexivity.
Qed.
(* #[global] Hint Resolve aCPO_colist : colist. *)

Fixpoint fold {A B} (z : B) (f : A -> B -> B) (l : list A) : B :=
  match l with
  | [] => z
  | x :: xs => f x (fold z f xs)
  end.

Fixpoint foldl {A B} (f : B -> A -> B) (z : B) (l : list A) : B :=
  match l with
  | [] => z
  | x :: xs => foldl f (f z x) xs
  end.

(* Definition para {A B} (z : B) (f : A -> colist A -> B -> B) (l : list A) : B := *)
(*   snd (fold (conil, z) (fun a lx => let (l', x) := lx in *)
(*                               (cocons a l', f a l' x)) l). *)

Fixpoint para {A B} (z : B) (f : A -> colist A -> B -> B) (l : list A) : B :=
  match l with
  | [] => z
  | x :: xs => f x (inj xs) (para z f xs)
  end.

(* Lemma para_para' {A B} (z : B) (f : A -> colist A -> B -> B) (l : list A) : *)
(*   para z f l = para' z f l. *)
(* Proof. *)
(*   unfold para. *)
(*   revert z f; induction l; intros z f; simpl; auto. *)
(*   specialize (IHl z f). *)
(*   destruct (fold (conil, z) *)
(*               (fun (a0 : A) (lx : colist A * B) => *)
(*                  let (l0, x) := lx in (cocons a0 l0, f a0 l0 x)) l). *)
(*   simpl in *; subst. *)
(*   f_equal. *)
  

#[global]
  Instance monotone_fold {A B} `{OType B} (z : B) (f : A -> B -> B)
  {Hz : forall b, z ⊑ fold z f b}
  {Hf : forall a, Proper (leq ==> leq) (f a)}
  : Proper (leq ==> leq) (fold z f).
Proof.
  intro a; revert Hz Hf; revert f;
    induction a; intros f Hz Hf b Hab; inv Hab; simpl.
  - apply Hz.
  - apply Hf, IHa; auto.
Qed.
#[global] Hint Resolve monotone_fold : colist.

#[global]
  Instance monotone_para {A B} `{OType B} (z : B) (f : A -> colist A -> B -> B)
  {Hz : forall b, z ⊑ para z f b}
  {Hf : forall a, Proper (leq ==> leq ==> leq) (f a)}
  : Proper (leq ==> leq) (para z f).
Proof.
  intro a; revert Hz Hf; revert f;
    induction a; intros f Hz Hf b Hab; inv Hab; simpl.
  - apply Hz.
  - apply Hf; auto.
    apply monotone_inj; auto.
Qed.
#[global] Hint Resolve monotone_para : colist.

Definition copara {A B} `{OType B} (z : B) (f : A -> colist A -> B -> B) : colist A -> B :=
  co (para z f).

#[global]
  Instance antimonotone_fold {A B} `{OType B} (z : B) (f : A -> B -> B)
  {Hz : forall b, fold z f b ⊑ z}
  {Hf : forall a, Proper (leq ==> leq) (f a)}
  : Proper (leq ==> flip leq) (fold z f).
Proof.
  intro a; revert Hz Hf; revert f;
    induction a; intros f Hz Hf b Hab; inv Hab; simpl.
  - apply Hz.
  - apply Hf, IHa; auto.
Qed.
#[global] Hint Resolve antimonotone_fold : colist.

(** Computation lemmas for cofolds. *)

Lemma co_fold_nil {A B} `{dCPO B} (z : B) (f : A -> B -> B) :
  co (fold z f) conil === z.
Proof.
  apply supremum_sup, supremum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma co_fold_cons {A B} `{dCPO B}
  (z : B) (f : A -> B -> B) (a : A) (l : colist A) :
  (forall b, z ⊑ fold z f b) ->
  (forall a, continuous (f a)) ->
  z ⊑ f a z ->
  co (fold z f) (cocons a l) === f a (co (fold z f) l).
Proof.
  intros Hz Hf Hfaz.
  apply supremum_sup.
  apply shift_supremum'' with (f := fun i => f a (fold z f (ideal l i))); auto.
  { apply Hf.
    { apply monotone_directed; auto with colist order.
      apply chain_directed, chain_ideal. }
    { apply dsup_spec.
      { apply monotone_directed; auto with colist order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

(** Equality computaton lemmas for cofolds. *)

Lemma co_fold_nil' {A B} {o : OType B} `{@ExtType B o} `{@dCPO B o}
  (z : B) (f : A -> B -> B) :
  co (fold z f) conil = z.
Proof. apply ext, co_fold_nil. Qed.

Lemma co_fold_cons' {A B} {o : OType B} `{@ExtType B o} `{@dCPO B o}
  (z : B) (f : A -> B -> B) (a : A) (l : colist A) :
  (forall b, z ⊑ fold z f b) ->
  (forall a, continuous (f a)) ->
  z ⊑ f a z ->
  co (fold z f) (cocons a l) = f a (co (fold z f) l).
Proof. intros Hz Hf Hfaz; apply ext, co_fold_cons; auto. Qed.

Lemma coop_fold_nil {A B} `{ldCPO B} (z : B) (f : A -> B -> B) :
  coop (fold z f) conil === z.
Proof.
  apply infimum_inf, infimum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma coop_fold_cons {A B} `{ldCPO B}
  (z : B) (f : A -> B -> B) (a : A) (l : colist A) :
  (forall b, fold z f b ⊑ z) ->
  (forall a, dec_continuous (f a)) ->
  f a z ⊑ z ->
  coop (fold z f) (cocons a l) === f a (coop (fold z f) l).
Proof with eauto with colist order.
  intros Hz Hf Hfaz.
  apply infimum_inf.
  apply shift_infimum'' with (f := fun i => f a (fold z f (ideal l i))); auto.
  { apply Hf.
    { apply antimonotone_downward_directed...
      apply chain_directed, chain_ideal. }
    { apply dinf_spec.
      { apply antimonotone_downward_directed...
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma coop_fold_nil' {A B} {o : OType B} `{@ExtType B o} `{@ldCPO B o}
  (z : B) (f : A -> B -> B) :
  coop (fold z f) conil = z.
Proof. apply ext, coop_fold_nil. Qed.

Lemma coop_fold_cons' {A B} {o : OType B} `{@ExtType B o} `{@ldCPO B o}
  (z : B) (f : A -> B -> B) (a : A) (l : colist A) :
  (forall b, fold z f b ⊑ z) ->
  (forall a, dec_continuous (f a)) ->
  f a z ⊑ z ->
  coop (fold z f) (cocons a l) = f a (coop (fold z f) l).
Proof. intros Hz Hf Hgz; apply ext, coop_fold_cons; auto. Qed.

Lemma forall_False_impl {A} (f : A -> Prop) :
  forall x : A, False ⊑ f x.
Proof. intros ? []. Qed.
#[global] Hint Resolve forall_False_impl : colist.

Lemma forall_impl_True {A} (f : A -> Prop) :
  forall x : A, f x ⊑ True.
Proof. intros ? ?; apply I. Qed.
#[global] Hint Resolve forall_impl_True : colist.

Lemma forall_monotone_P_disj {A} (P : A -> Prop) :
  forall a : A, Proper (leq ==> leq) (fun x : Prop => P a \/ x).
Proof. intros a x y; simpl; unfold impl; intros H0 [H1|H1]; auto. Qed.
#[global] Hint Resolve forall_monotone_P_disj : colist.

Lemma forall_monotone_P_conj {A} (P : A -> Prop) :
  forall a : A, Proper (leq ==> leq) (fun x : Prop => P a /\ x).
Proof. intros a x y; simpl; unfold impl; intros H0 [H1 H2]; auto. Qed.
#[global] Hint Resolve forall_monotone_P_conj : colist.

Lemma forall_dec_continuous_P_conj {A} (P : A -> Prop) :
  forall a : A, dec_continuous (fun x : Prop => P a /\ x).
Proof. intro a; apply dec_continuous_conj. Qed.
#[global] Hint Resolve forall_dec_continuous_P_conj : colist.

(* #[global] *)
(*   Instance antimonotone_list_forall {A} (P : A -> Prop) *)
(*   : Proper (leq ==> flip leq) (list_forall P). *)
(* Proof. *)
(*   intro a; induction a; intros b Hab Hex; inv Hab; inv Hex; *)
(*     constructor; auto; eapply IHa; eauto. *)
(* Qed. *)
(* #[global] Hint Resolve antimonotone_list_forall : colist. *)

Definition list_exists {A} (P : A -> Prop) : list A -> Prop :=
  fold False (fun a x => P a \/ x).

Definition colist_exists {A} (P : A -> Prop) : colist A -> Prop :=
  co (list_exists P).

Definition list_forall {A} (P : A -> Prop) : list A -> Prop :=
  fold True (fun a x => P a /\ x).

Definition colist_forall {A} (P : A -> Prop) : colist A -> Prop :=
  coop (list_forall P).

#[global]
  Instance monotone_list_exists {A} (P : A -> Prop)
: Proper (leq ==> leq) (list_exists P).
Proof. eauto with order colist. Qed.
#[global] Hint Resolve monotone_list_exists : colist.

#[global]
  Instance antimonotone_list_forall {A} (P : A -> Prop)
  : Proper (leq ==> flip leq) (list_forall P).
Proof. eauto with order colist. Qed.
#[global] Hint Resolve antimonotone_list_forall : colist.

(** Introduction rule 1 for colist_exists. *)
Lemma colist_exists_intro1 {A} (P : A -> Prop) (a : A) (l : colist A) :
  P a ->
  colist_exists P (cocons a l).
Proof with eauto with order colist.
  unfold colist_exists, list_exists.
  rewrite co_fold_cons...
  intro; apply continuous_disj.
Qed.

(** Introduction rule 2 for colist_exists. *)
Lemma colist_exists_intro2 {A} (P : A -> Prop) (a : A) (l : colist A) :
  colist_exists P l ->
  colist_exists P (cocons a l).
Proof with eauto with order colist.
  unfold colist_exists, list_exists.
  rewrite co_fold_cons...
  intro; apply continuous_disj.
Qed.

Lemma colist_exists_nil {A} (P : A -> Prop) :
  ~ colist_exists P conil.
Proof with eauto with order colist.
  intro HC; apply co_elim in HC...
  destruct HC as [[] HC]; inv HC.
Qed.

(** Elimination rule for colist_exists. *)
Lemma colist_exists_elim {A} (P : A -> Prop) (a : A) (l : colist A) :
  colist_exists P (cocons a l) ->
  P a \/ colist_exists P l.
Proof with eauto with order colist.
  unfold colist_exists, list_exists.
  rewrite co_fold_cons...
  intro; apply continuous_disj.
Qed.

Lemma colist_forall_nil {A} (P : A -> Prop) :
  colist_forall P conil.
Proof with eauto with order colist.
  apply coop_intro...
  intros []; constructor.
Qed.

(** Introduction rule for colist_forall. *)
Lemma colist_forall_intro {A} (P : A -> Prop) (a : A) (l : colist A) :
  P a ->
  colist_forall P l ->
  colist_forall P (cocons a l).
Proof with eauto with order colist.
  intros H0 H1.
  apply coop_intro...
  intros [|i]; simpl; unfold flip; simpl.
  { constructor. }
  apply coop_elim with (i:=i) in H1...
  constructor; auto.
Qed.

(** Elimination rule 1 for colist_forall. *)
Lemma colist_forall_elim1 {A} (P : A -> Prop) (a : A) (l : colist A) :
  colist_forall P (cocons a l) -> P a.
Proof with eauto with order colist.
  unfold colist_forall, list_forall.
  rewrite coop_fold_cons...
  intros []; auto.
Qed.

(** Elimination rule 2 for colist_forall. *)
Lemma colist_forall_elim2 {A} (P : A -> Prop) (a : A) (l : colist A) :
  colist_forall P (cocons a l) -> colist_forall P l.
Proof with eauto with order colist.
  unfold colist_forall, list_forall.
  rewrite coop_fold_cons...
  intros []; auto.
Qed.

(** Computation rule for colist_forall. *)
Lemma colist_forall_cons {A} (P : A -> Prop) (a : A) (l : colist A) :
  colist_forall P (cocons a l) <-> P a /\ colist_forall P l.
Proof with eauto with order colist.
  split.
  - intro H; pose proof H as H'.
    apply colist_forall_elim1 in H.
    apply colist_forall_elim2 in H'; split; auto.
  - intros [H0 H1].
    apply coop_intro...
    intros [|i]; simpl; unfold flip; simpl.
    { constructor. }
    apply coop_elim with (i:=i) in H1...
    constructor; auto.
Qed.

Definition filter {A} (f : A -> bool) : list A -> list A :=
  fold [] (fun a l' => if f a then a :: l' else l').

Lemma list_exists_filter {A} (a : A) (l : list A) (P : A -> bool) :
  P a = true ->
  list_exists (eq a) l ->
  list_exists (eq a) (filter P l).
Proof.
  unfold filter, list_exists.
  revert a P; induction l; simpl; intros x P HPx Hex; unfold id; auto.
  destruct Hex as [Hex|Hex]; subst.
  - rewrite HPx; left; auto.
  - destruct (P a) eqn:Hpa; simpl; auto.
Qed.

(* Lemma list_exists_filter {A} (a : A) (l : list A) (P : A -> bool) : *)
(*   P a = true -> *)
(*   list_exists (eq a) l -> *)
(*   list_exists (eq a) (filter P l). *)
(* Proof. *)
(*   unfold filter. *)
(*   revert a P; induction l; intros x P HPx Hex; inv Hex; simpl. *)
(*   - constructor; auto. *)
(*   - rewrite HPx; constructor; auto. *)
(*   - destruct (P a) eqn:HPa. *)
(*     + apply list_exists_tl; auto. *)
(*     + constructor; auto. *)
(* Qed. *)

(** Filtering colists. *)

Lemma prefix_inj_le {A} (l : list A) (i : nat) :
  list_le (prefix i (inj l)) l.
Proof.
  revert l; induction i; simpl; intro l.
  { constructor. }
  destruct l; simpl.
  - constructor.
  - constructor; auto.
Qed.

Lemma list_forall_impl {A} (P Q : A -> Prop) (l : list A) :
  (forall x, P x -> Q x) ->
  list_forall P l ->
  list_forall Q l.
Proof.
  unfold list_forall; induction l; intros HPQ HP; simpl; auto.
  destruct HP; split; auto.
Qed.

Lemma colist_forall_impl {A} (P Q : A -> Prop) (l : colist A) :
  (forall x, P x -> Q x) ->
  colist_forall P l ->
  colist_forall Q l.
Proof with eauto with colist order aCPO.
  intros HPQ HP.
  apply coop_intro...
  intro i; apply coop_elim with (i:=i)in HP...
  eapply list_forall_impl; eauto.
Qed.

Lemma list_forall_afilter {A} (P : A -> Prop) (Q : A -> bool) (l : list A) :
  list_forall P l ->
  list_forall (fun x => P x /\ Q x = true) (filter Q l).
Proof.
  unfold list_forall, filter; induction l; intro Hl; simpl; unfold id; auto.
  destruct Hl; destruct (Q a) eqn:HQa; simpl; auto.
Qed.

(* Inductive list_colist_le {A} : list A -> colist A -> Prop := *)
(* | list_colist_le_nil : forall l, list_colist_le [] l *)
(* | list_colist_le_cons : forall x l1 l2, *)
(*     list_colist_le l1 l2 -> *)
(*     list_colist_le (acons x l1) (cocons x l2). *)
(* #[global] Hint Constructors list_colist_le : colist. *)

(* #[global] *)
(*   Instance antimonotone_list_colist_le {A} : Proper (leq ==> flip leq) (@list_colist_le A). *)
(* Proof. *)
(*   intro a; induction a; intros b Hab l Hl. *)
(*   { constructor. } *)
(*   inv Hab; inv Hl. *)
(*   constructor; eapply IHa; eauto. *)
(* Qed. *)
(* #[global] Hint Resolve antimonotone_list_colist_le : colist. *)

(* note: this can be generalized by list_colist_R. *)
Definition list_colist_le {A} : list A ->  colist A -> Prop :=
  fold (const True) (fun a f l => match l with
                             | conil => False
                             | cocons b l' => a = b /\ f l'
                             end).

#[global]
  Instance antimonotone_list_colist_le {A} : Proper (leq ==> flip leq) (@list_colist_le A).
Proof.
  apply antimonotone_fold.
  - intros ? ? ?; apply I.
  - intros a f g Hfg l Hl; destruct l; auto.
    destruct Hl; subst; split; auto.
    apply Hfg; auto.
Qed.
#[global] Hint Resolve antimonotone_list_colist_le : colist.

Definition colist_le' {A} : colist A -> colist A -> Prop :=
  coop list_colist_le.

Lemma colist_le'_nil {A} (l : colist A) :
  colist_le' conil l.
Proof with eauto with colist order aCPO.
  unfold colist_le', list_colist_le.
  apply coop_intro2...
  intros []; apply I.
Qed.

Lemma list_colist_le_prefix {A} (l1 l2 : colist A) (i : nat) :
  l1 ⊑ l2 ->
  list_colist_le (prefix i l1) l2.
Proof.
  revert l1 l2; induction i; intros l1 l2 Hle; simpl.
  { constructor. }
  destruct l1; inv Hle.
  { constructor. }
  constructor; auto; apply IHi; auto.
Qed.

Lemma colist_le'_inv_cons {A} (a : A) (l1 l2 : colist A) :
  colist_le' (cocons a l1) l2 ->
  exists l2', l2 = cocons a l2' /\ colist_le' l1 l2'.
Proof with eauto with colist order aCPO.
  intro Hle.
  destruct l2; try solve [apply coop_elim2 with (i := S O) in Hle;
                          eauto with colist order; inv Hle].
  assert (a = a0).
  { apply coop_elim2 with (i := S O) in Hle...
    destruct Hle; auto. }
  subst.
  exists l2; split; auto.
  apply coop_intro2...
  intro i.
  apply coop_elim2 with (i := S i) in Hle...
  apply Hle.
Qed.

Lemma colist_le_colist_le' {A} (l1 l2 : colist A) :
  l1 ⊑ l2 <-> colist_le' l1 l2.
Proof with eauto with colist order aCPO.
  split.
  - intro Hle.
    unfold colist_le'.
    apply coop_intro2...
    intro i; apply list_colist_le_prefix; auto.
  - revert l1 l2; cofix CH; intros l1 l2 Hle.
    destruct l1.
    { constructor. }
    apply colist_le'_inv_cons in Hle.
    destruct Hle as [l2' [? Hle]]; subst; constructor; apply CH; auto.
Qed.

Lemma list_forall_filter {A} (P : A -> bool) (l : list A) :
  list_forall (fun x => P x = true) (filter P l).
Proof.
  unfold filter.
  induction l; simpl.
  { constructor. }
  destruct (P a) eqn:Pa.
  - split; auto.
  - auto.
Qed.

Inductive list_nth {A} (P : A -> Prop) : nat -> list A -> Prop :=
| list_nth_here : forall a l,
    P a ->
    list_nth P O (a :: l)
| list_nth_there : forall n a l,
    list_nth P n l ->
    list_nth P (S n) (a :: l).

Inductive nth' {A} (P : A -> Prop) : nat -> colist A -> Prop :=
| nth'_here : forall a l,
    P a ->
    nth' P O (cocons a l)
| nth'_there : forall n a l,
    nth' P n l ->
    nth' P (S n) (cocons a l).

Inductive nth {A} (P : A -> Prop) : nat -> colist A -> Prop :=
| nth_here : forall a l,
    P a ->
    nth P O (cocons a l)
| nth_there : forall n a l,
    ~ P a ->
    nth P n l ->
    nth P (S n) (cocons a l).

Lemma nth_list_exists_prefix {A} (P : A -> Prop) (l : colist A) (n : nat) :
  nth P n l ->
  list_exists P (prefix (S n) l).
Proof.
  revert l; induction n; intros m Hm; inv Hm; simpl.
  { left; auto. }
  right; apply IHn; auto.
Qed.

Lemma forall_not_nth_colist_forall {A} (P : A -> Prop) (l : colist A) :
  (forall n, ~ nth P n l) -> 
  colist_forall (fun x => ~ P x) l.
Proof with eauto with colist order aCPO.
  intro Hl.
  apply coop_intro...
  intro i.
  revert Hl; revert l; induction i; intros l Hl.
  { constructor. }
  simpl in *; unfold flip in *; simpl.
  destruct l.
  { constructor. }
  constructor.
  - specialize (Hl O); intro HC; apply Hl; constructor; auto.
  - apply IHi.
    pose proof Hl as Hl'.
    specialize (Hl' O).
    intro n; specialize (Hl (S n)).
    intro HC; apply Hl.
    constructor; auto.
    intro HP; apply Hl'; constructor; auto.
Qed.

Lemma list_forall_conj {A} (P Q : A -> Prop) (l : list A) :
  list_forall P l ->
  list_forall Q l ->
  list_forall (fun x => P x /\ Q x) l.
Proof.
  induction l; intros HP HQ; inv HP; inv HQ; constructor; auto.
  apply IHl; auto.
Qed.

Lemma colist_forall_conj {A} (P Q : A -> Prop) (l : colist A) :
  colist_forall P l ->
  colist_forall Q l ->
  colist_forall (fun x => P x /\ Q x) l.
Proof with eauto with colist order aCPO.
  intros HP HQ.
  apply coop_intro...
  intro i.
  apply coop_elim with (i:=i) in HP...
  apply coop_elim with (i:=i) in HQ...
  apply list_forall_conj; auto.
Qed.

Lemma list_forall_filter' {A} (P : A -> Prop) (Q : A -> bool) (l : list A) :
  list_forall P l ->
  list_forall P (filter Q l).
Proof.
  unfold filter.
  induction l; intro Hl; inv Hl; simpl.
  { constructor. }
  destruct (Q a); auto; constructor; auto.
  apply IHl; auto.
Qed.

Definition list_length {A} : list A -> conat :=
  fold cozero (fun _ => cosucc).

Definition list_length' {A} : list A -> nat :=
  fold O (fun _ => S).

#[global]
  Instance monotone_list_length {A} : Proper (leq ==> leq) (@list_length A).
Proof.
  apply monotone_fold.
  { intro; constructor. }
  intros _; apply continuous_monotone, continuous_cosucc.
Qed.

Definition colist_length {A} : colist A -> conat :=
  co list_length.

Definition cofold {A B} `{o: PType B} (f : A -> B -> B) : colist A -> B :=
  co (fold ⊥ f).

Definition coopfold {A B} `{o: TType B} (f : A -> B -> B) : colist A -> B :=
  coop (fold ⊤ f).

Lemma cofold_nil {A B} `{o : OType B} `{@PType B o} `{@dCPO B o} (f : A -> B -> B) :
   cofold f conil === ⊥.
Proof. apply co_fold_nil. Qed.

Lemma cofold_cons {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  (f : A -> B -> B) (a : A) (l : colist A) :
  (forall x, continuous (f x)) ->
  cofold f (cocons a l) === f a (cofold f l).
Proof. intro Hf; apply co_fold_cons; auto; try intro; apply bot_le. Qed.

Lemma cofold_nil' {A B} `{o : OType B} `{@ExtType _ o} `{@PType B o} `{@dCPO B o}
  (f : A -> B -> B) :
  cofold f conil = ⊥.
Proof. apply ext, co_fold_nil. Qed.

Lemma cofold_cons' {A B} `{o : OType B} `{@ExtType _ o} `{@PType B o} `{@dCPO B o}
  (f : A -> B -> B) (a : A) (l : colist A) :
  (forall x, continuous (f x)) ->
  cofold f (cocons a l) = f a (cofold f l).
Proof. intro Hf; apply ext, co_fold_cons; auto; try intro; apply bot_le. Qed.

Lemma coopfold_nil {A B} `{o : OType B} `{@TType B o} `{@lCPO B o} (f : A -> B -> B) :
   coopfold f conil === ⊤.
Proof. apply coop_fold_nil. Qed.

Lemma coopfold_cons {A B} `{o : OType B} `{@TType B o} `{@ldCPO B o}
  (f : A -> B -> B) (a : A) (l : colist A) :
  (forall x, dec_continuous (f x)) ->
  coopfold f (cocons a l) === f a (coopfold f l).
Proof. intro Hf; apply coop_fold_cons; auto; try intro; apply le_top. Qed.

Lemma coopfold_nil' {A B} `{o : OType B} `{@ExtType _ o} `{@TType B o} `{@ldCPO B o}
  (f : A -> B -> B) :
  coopfold f conil = ⊤.
Proof. apply ext, coop_fold_nil. Qed.

Lemma coopfold_cons' {A B} `{o : OType B} `{@ExtType _ o} `{@TType B o} `{@ldCPO B o}
  (f : A -> B -> B) (a : A) (l : colist A) :
  (forall x, dec_continuous (f x)) ->
  coopfold f (cocons a l) = f a (coopfold f l).
Proof. intro Hf; apply ext, coop_fold_cons; auto; try intro; apply le_top. Qed.

(** These are all be equivalent. *)

(* Definition productive {A} (l : colist A) : Prop := *)
(*   forall i, prefix i l ⊏ prefix (S i) l. *)

CoInductive productive {A} : colist A -> Prop :=
| productive_cons : forall a l,
    productive l ->
    productive (cocons a l).

Definition productive' {A} (l : colist A) : Prop :=
  forall n, nth' (const True) n l.

Definition productive'' {A} (l : colist A) : Prop :=
  colist_length l = omega.

Definition productive''' {A} (l : colist A) : Prop :=
  omega ⊑ colist_length l.

(** Only safe for productive colists (no occurrences of nil). *)
Extract Constant cofold => "
  \ o p f l ->
    case l of
      Cobot -> bot o p
      Cocons a l' -> f a (cofold o p f l')
".

Lemma colist_length_inj {A} (l : colist A) (n : nat) :
  colist_length l = nat_inj n ->
  exists al, l = inj al.
Proof with eauto with colist conat order aCPO.
  revert l; induction n; simpl; intros l Hl.
  { exists []; destruct l.
    - reflexivity.
    - unfold colist_length, list_length in Hl.
      rewrite co_fold_cons' in Hl...
      inv Hl. }
  destruct l.
  - exists []; reflexivity.
  - unfold colist_length, list_length in Hl.
    rewrite co_fold_cons' in Hl...
    inv Hl.
    apply IHn in H0.
    destruct H0 as [al ?]; subst.
    exists (a :: al); auto.
Qed.

Lemma not_list_nth_list_length {A} (P : A -> Prop) (l : list A) :
  ~ list_nth P (list_length' l) l.
Proof.
  unfold list_length'.
  induction l; simpl; intro HC; inv HC.
  apply IHl; auto.
Qed.

Lemma nth'_inj_list_nth {A} (P : A -> Prop) (n : nat) (l : list A) :
  nth' P n (inj l) ->
  list_nth P n l.
Proof.
  revert n; induction l; intros n Hn; inv Hn; constructor; auto.
Qed.

Lemma productive'_productive {A} (l : colist A) :
  productive' l <-> productive l.
Proof.
  unfold productive'.
  split.
  - revert l; cofix CH; intros l Hl.
    destruct l.
    + specialize (Hl O); inv Hl.
    + constructor; apply CH; intro i.
      specialize (Hl (S i)); inv Hl; auto.
  - intros Hl i.
    revert l Hl; induction i; intros l Hl.
    + destruct l; inv Hl.
      constructor; apply I.
    + destruct l; inv Hl.
      constructor; apply IHi; auto.
Qed.

Lemma productive'_productive'' {A} (l : colist A) :
  productive' l <-> productive'' l.
Proof with eauto with colist conat order aCPO.
  unfold productive', productive''; split; intro H.
  - destruct (@conat_finite_or_omega (colist_length l)); auto.
    destruct H0 as [m Hm].
    exfalso.
    apply colist_length_inj in Hm.
    destruct Hm as [al Hal]; subst.
    specialize (H (list_length' al)).
    apply nth'_inj_list_nth in H.
    eapply not_list_nth_list_length; eauto.
  - intro n; revert H; revert l.
    unfold colist_length, list_length.
    induction n; intros l Hl.
    { destruct l.
      - rewrite co_fold_nil', (@conat.unf_eq omega) in Hl; inv Hl.
      - constructor; apply I. }
    destruct l.
    + rewrite co_fold_nil', (@conat.unf_eq omega) in Hl; inv Hl.
    + constructor.
      apply IHn.
      rewrite co_fold_cons' in Hl...
      rewrite (@conat.unf_eq omega) in Hl.
      inv Hl; auto.
Qed.

Lemma productive''_productive''' {A} (l : colist A) :
  productive'' l <-> productive''' l.
Proof.
  unfold productive'', productive'''.
  split.
  - intro Heq; rewrite Heq; reflexivity.
  - intro Hle.
    apply ext; split; auto.
    apply le_omega.
Qed.

Lemma not_productive_conil {A} :
  ~ productive'' (@conil A).
Proof.
  unfold productive''.
  unfold colist_length, list_length.
  rewrite co_fold_nil'; intro HC.
  rewrite (@conat.unf_eq omega) in HC; inv HC.
Qed.

Lemma productive''_cons {A} (a : A) (l : colist A) :
  productive'' (cocons a l) -> productive'' l.
Proof with eauto with colist conat order aCPO.
  unfold productive''.
  intro Hgen.
  rewrite (@conat.unf_eq omega) in Hgen.
  unfold colist_length, list_length in Hgen.
  rewrite co_fold_cons' in Hgen...
  inv Hgen; auto.
Qed.

Definition list_R {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
  fold (const True) (fun a f l => match l with
                             | [] => False
                             | b :: l' => R a b /\ f l'
                             end).

Definition list_colist_R {A B} (R : A -> B -> Prop) : list A -> colist B -> Prop :=
  fold (const True) (fun a f l => match l with
                             | conil => False
                             | cocons b l' => R a b /\ f l'
                             end).

#[global]
  Instance antimonotone_list_colist_R {A B} (R : A -> B -> Prop)
  : Proper (leq ==> flip leq) (list_colist_R R).
Proof.
  apply antimonotone_fold.
  { intro; constructor. }
  intros a f g Hfg l Hl; destruct l; auto.
  destruct Hl; subst; split; auto.
  apply Hfg; auto.
Qed.
#[global] Hint Resolve antimonotone_list_colist_R : colist.

Definition colist_R {A B} (R : A -> B -> Prop) : colist A -> colist B -> Prop :=
  coop (list_colist_R R).

Lemma colist_R_cons_nil {A B} (R : A -> B -> Prop) (a : A) (l1 : colist A) :
  ~ colist_R R (cocons a l1) conil.
Proof with eauto with colist order aCPO.
  intro HC; apply coop_elim2 with (i := S O) in HC...
Qed.

Lemma colist_R_cons {A B} (R : A -> B -> Prop) (a : A) (l1 : colist A) (b : B) (l2 : colist B) :
  colist_R R (cocons a l1) (cocons b l2) <-> R a b /\ colist_R R l1 l2.
Proof with eauto with colist order aCPO.
  split.
  - intro HR; split.
    + apply coop_elim2 with (i := S O) in HR...
      destruct HR; auto.
    + apply coop_intro2...
      intro i; apply coop_elim2 with (i := S i) in HR...
      destruct HR; auto.
  - intros [H0 H1].
    apply coop_intro2...
    intros []; simpl; unfold flip; simpl.
    { constructor. }
    constructor; auto.
    apply coop_elim2 with (i:=n) in H1...
Qed.

Fixpoint list_of_list {A} (l : list A) : list A :=
  match l with
  | [] => []
  | a :: l' => a :: list_of_list l'
  end.

Lemma Forall_list_of_list {A} (P : A -> Prop) (l : list A) :
  Forall P (list_of_list l) ->
  list_forall P l.
Proof.
  induction l; intro Hall.
  { constructor. }
  inv Hall.
  split; auto; apply IHl; auto.
Qed.

Lemma colist_forall_inj {A} (P : A -> Prop) (l : list A) :
  list_forall P l <-> colist_forall P (inj l).
Proof with eauto with colist order.
  split.
  { induction l; intro Hl; simpl.
    - apply colist_forall_nil.
    - apply colist_forall_intro; destruct Hl; auto. }
  { induction l; intro Hl.
    - constructor.
    - apply colist_forall_cons in Hl; destruct Hl.
      constructor; auto; apply IHl; auto. }
Qed.

(** Is it possible to write this as a fold? Don't think so. UPDATE:
    YES, as a parafold. *)
Inductive list_ordered {A} (R : A -> A -> Prop) : list A -> Prop :=
| list_ordered_nil : list_ordered R []
| list_ordered_cons : forall a l,
    list_forall (R a) l ->
    list_ordered R l ->
    list_ordered R (a :: l).

Definition list_ordered' {A} (R : A -> A -> Prop) : list A -> Prop :=
  para True (fun a l P => colist_forall (R a) l /\ P).

Lemma list_ordered_list_ordered' {A} (R : A -> A -> Prop) (l : list A) :
  list_ordered R l <-> list_ordered' R l.
Proof.
  split; induction l; intro H.
  - apply I.
  - inv H; split; auto.
    + apply colist_forall_inj; auto.
    + apply IHl; auto.
  - constructor.
  - destruct H; constructor; auto.
    apply colist_forall_inj; auto.
Qed.

#[global]
  Instance antimonotone_list_ordered {A} (R : A -> A -> Prop)
  : Proper (leq ==> flip leq) (list_ordered R).
Proof.
  intro a; induction a; intros b Hab Hordered.
  { constructor. }
  inv Hab; inv Hordered.
  constructor.
  - eapply antimonotone_list_forall; eauto.
  - eapply IHa; eauto.
Qed.
#[global] Hint Resolve antimonotone_list_ordered : colist.

Definition ordered {A} (R : A -> A -> Prop) : colist A -> Prop :=
  coop (list_ordered R).

Lemma ordered_nil {A} (R : A -> A -> Prop) :
  ordered R conil.
Proof with eauto with order colist aCPO.
  apply coop_intro...
  intros []; constructor.
Qed.

Lemma ordered_cons {A} (R : A -> A -> Prop) (a : A) (l : colist A) :
  ordered R (cocons a l) <-> colist_forall (R a) l /\ ordered R l.
Proof with eauto with order colist aCPO.
  split.
  - intro Hord; split.
    + apply coop_intro...
      intro i; apply coop_elim with (i := S i) in Hord...
      inv Hord; auto.
    + apply coop_intro...
      intro i; apply coop_elim with (i := S i) in Hord...
      inv Hord; auto.
  - intros [Hall Hord].
    apply coop_intro...
    simpl; unfold flip.
    intros []; simpl.
    + constructor.
    + constructor.
      * apply coop_elim with (i:=n) in Hall...
      * apply coop_elim with (i:=n) in Hord...
Qed.

Definition sorted {A} `{OType A} : colist A -> Prop := ordered leq.
Definition nodup {A} : colist A -> Prop := ordered (fun a b => a <> b).

(*** Cofilter *)

Definition filter_f {A} (f : A -> bool) : A -> colist A -> colist A :=
  fun a l' => if f a then cocons a l' else l'.

(** Monotone basis function for filter. *)
Definition afilter {A} (f : A -> bool) : list A -> colist A :=
  fold ⊥ (filter_f f).

(** Filter comorphism. *)
Definition cofilter {A} (f : A -> bool) : colist A -> colist A :=
  cofold (filter_f f).    

(** Filter computation rule. *)
Lemma cofilter_cons {A} (f : A -> bool) (a : A) (l : colist A) :
  cofilter f (cocons a l) = if f a then cocons a (cofilter f l) else cofilter f l.
Proof.
  unfold cofilter; rewrite cofold_cons'; auto.
  intro x; apply continuous_ite; eauto with colist order.
Qed.

#[global]
  Instance monotone_afilter {A} (f : A -> bool) : Proper (leq ==> leq) (afilter f).
Proof.
  apply monotone_fold; eauto with order colist; intro; apply bot_le.
Qed.
#[global] Hint Resolve monotone_afilter : colist.

Lemma continuous_cofilter {A} (f : A -> bool) :
  continuous (cofilter f).
Proof.
  apply continuous_co, monotone_fold; eauto with order colist.
Qed.
#[global] Hint Resolve continuous_cofilter : colist.

Lemma cofilter_comm {A} (P Q : A -> bool) (l : colist A) :
  cofilter P (cofilter Q l) = cofilter Q (cofilter P l).
Proof with eauto with colist order aCPO.
  unfold cofilter, cofold.
  rewrite co_co_ext with (x:=l)...
  rewrite co_co_ext with (f:=afilter P)...
  unfold afilter.
  apply Proper_co_ext...
  clear l. ext l.
  unfold filter_f, compose; simpl.
  induction l; simpl.
  { rewrite 2!co_fold_nil'; auto. }
  destruct (P a) eqn:HPa, (Q a) eqn:HQa; auto.
  - rewrite 2!co_fold_cons'...
    rewrite HPa, HQa, IHl; auto.
  - rewrite co_fold_cons'...
    rewrite HQa; auto.
  - rewrite co_fold_cons'...
    rewrite HPa; auto.
Qed.

Lemma cofilter_inj_filter {A} (P : A -> bool) (l : list A) :
  cofilter P (inj l) = inj (filter P l).
Proof with eauto with colist order.
  unfold cofilter, filter_f, filter.
  induction l; simpl.
  - rewrite cofold_nil'; auto.
  - rewrite cofold_cons', IHl...
    destruct (P a); auto.
Qed.

Lemma list_forall_colist_le'_afilter {A} (P : A -> bool) (l : list A) :
  list_forall (fun x : A => P x <> true) l ->
  colist_le' (afilter P l) conil.
Proof with eauto with colist order.
  unfold colist_le', list_colist_le, afilter, filter_f.
  induction l; intro Hl; simpl.
  { apply coop_intro2...
    intros []; apply I. }
  destruct Hl.
  destruct (P a); try congruence; clear H; auto.
Qed.

Lemma cofilter_all_neq_true_nil {A} (P : A -> bool) (l : colist A) :
  colist_forall (fun x : A => P x <> true) l ->
  cofilter P l = conil.
Proof with eauto with colist order aCPO.
  intro Hl.
  apply ext.
  split.
  - apply colist_le_colist_le'.
    unfold cofilter, cofold.
    apply co_coopP...
    { intros ch Hch a Ha; unfold compose.
      apply apply_infimum, cocontinuous_coop... }
    apply coop_intro.
    { apply monotone_antimonotone_compose...
      eapply cocontinuous_antimonotone.
      intros ch Hch a Ha; unfold compose.
      apply apply_infimum, cocontinuous_coop... }
    intro i.
    apply coop_elim with (i:=i) in Hl...
    apply list_forall_colist_le'_afilter; auto.
  - constructor.
Qed.

Lemma prefix_cofilter {A} (P : A -> bool) (l : colist A) (i : nat) :
  exists j, prefix i (cofilter P l) = filter P (prefix j l).
Proof with eauto with colist order aCPO.
  revert l; induction i; intro l; simpl.
  { exists O; reflexivity. }
  destruct (classic (exists k, nth (fun x => P x = true) k l)) as [[k Hk]|Hk].
  - revert Hk. revert l.
    induction k; intros l Hk; inv Hk.
    + specialize (IHi l0); destruct IHi as [j Hj].
      unfold cofilter, filter_f, filter.
      rewrite cofold_cons'...
      exists (S j); simpl.
      rewrite H.
      f_equal; eauto.
    + apply IHk in H1.
      unfold cofilter, filter_f, filter.
      rewrite cofold_cons'...
      destruct (P a) eqn:HPa; try congruence.
      clear H0.
      destruct H1 as [j Hj].
      exists (S j).
      unfold cofilter, filter_f in Hj.
      rewrite Hj.
      unfold filter.
      simpl. rewrite HPa. reflexivity.
  - assert (H: forall k, ~ nth (fun x => P x = true) k l).
    { intros k HC; apply Hk; exists k; auto. }
    apply forall_not_nth_colist_forall in H.
    apply cofilter_all_neq_true_nil in H; rewrite H; exists O; reflexivity.
Qed.

Lemma colist_forall_cofilter {A} (P : A -> bool) (l : colist A) :
  colist_forall (fun x => P x = true) (cofilter P l).
Proof with eauto with colist order aCPO.
  apply coop_intro...
  simpl; unfold flip.  
  intro i.
  generalize (prefix_cofilter P l i).
  intros [j Hj].
  rewrite Hj.
  apply list_forall_filter.
Qed.

Lemma list_forall_colist_forall_afilter {A} (P : A -> Prop) Q l :
  list_forall P l ->
  colist_forall P (afilter Q l).
Proof.
  unfold afilter, filter_f.
  induction l; simpl; intros Hall.
  { apply colist_forall_nil. }
  inv Hall.
  destruct (Q a) eqn:HQa; auto.
  apply colist_forall_cons; auto.
Qed.

Lemma list_ordered_ordered_afilter {A} (R : A -> A -> Prop) P l :
  list_ordered R l ->
  ordered R (afilter P l).
Proof.
  unfold afilter, filter_f.
  induction l; intro Hord; simpl.
  { apply ordered_nil. }
  inv Hord.
  destruct (P a) eqn:HPa; auto.
  apply ordered_cons; split; auto.
  apply list_forall_colist_forall_afilter; auto.
Qed.

Lemma ordered_cofilter {A} (R : A -> A -> Prop) (P : A -> bool) (l : colist A) :
  ordered R l ->
  ordered R (cofilter P l).
Proof with eauto with colist order aCPO.
  intro Hord.
  unfold cofilter, cofold.
  apply co_coopP...
  (* { apply cocontinuous_coop... } *)
  apply coop_intro.
  { apply monotone_antimonotone_compose... }
  intro i; simpl; unfold flip, compose.
  apply list_ordered_ordered_afilter.
  apply coop_elim with (i:=i) in Hord...
Qed.

Lemma colist_forall_cofilter' {A} (P : A -> Prop) (Q : A -> bool) (l : colist A) :
  colist_forall P l ->
  colist_forall P (cofilter Q l).
Proof with eauto with colist order aCPO.
  intro Hl.
  apply coop_intro...
  intro i.
  generalize (prefix_cofilter Q l i).
  intros [j Hj].
  simpl; unfold flip.
  rewrite Hj.
  apply coop_elim with (i:=j) in Hl...
  apply list_forall_filter'; auto.
Qed.

Lemma colist_forall_cofilter_conj {A} (P : A -> Prop) (Q : A -> bool) (l : colist A) :
  colist_forall P l ->
  colist_forall (fun x => P x /\ Q x = true) (cofilter Q l).
Proof with eauto with colist order aCPO.
  intro Hl.
  apply colist_forall_conj.
  - apply colist_forall_cofilter'; auto.
  - apply colist_forall_cofilter.
Qed.

(*** comap *)

Definition map_f {A B} (f : A -> B) : A -> colist B -> colist B :=
  fun a l => cocons (f a) l.

(** Monotone basis function for map. *)
Definition amap {A B} (f : A -> B) : list A -> colist B :=
  fold (@conil B) (map_f f).

#[global]
  Instance monotone_amap {A B} (f : A -> B) : Proper (leq ==> leq) (amap f).
Proof.
  apply monotone_fold; eauto with order colist; intro; apply bot_le.
Qed.
#[global] Hint Resolve monotone_amap : colist.

(** Map comorphism. *)
Definition comap {A B} (f : A -> B) : colist A -> colist B :=
  cofold (map_f f).

Lemma continuous_comap {A B} (f : A -> B) :
  continuous (comap f).
Proof. apply continuous_co, monotone_amap. Qed.

(** Computation rule for map. *)
Lemma comap_cons {A B} (f : A -> B) (a : A) (l : colist A) :
  comap f (cocons a l) = cocons (f a) (comap f l).
Proof.
  unfold comap; rewrite cofold_cons'; auto.
  intro x; apply continuous_cocons.
Qed.

(*** cosum *)

(** Monotone basis function for sum. *)
Definition sum : list eR -> eR :=
  fold 0 eRplus.

#[global]
  Instance monotone_sum : Proper (leq ==> leq) sum.
Proof. apply monotone_fold; eauto with eR order colist. Qed.
#[global] Hint Resolve monotone_sum : colist.

(** Map comorphism. *)
Definition cosum : colist eR -> eR :=
  cofold eRplus.

Lemma continuous_cosum :
  continuous cosum.
Proof. apply continuous_co, monotone_sum. Qed.

(** Computation rule for sum. *)
Lemma cosum_cons (a : eR) (l : colist eR) :
  cosum (cocons a l) = a + cosum l.
Proof.
  unfold cosum, cofold.
  rewrite co_fold_cons'; auto with eR.
  apply continuous_eRplus.
Qed.

Lemma cofilter_false_nil {A} (f : A -> bool) (l : colist A) :
  colist_forall (fun x => f x = false) l ->
  cofilter f l = conil.
Proof with eauto with colist order aCPO.
  intro Hall.
  apply ext; split; try constructor.
  apply colist_le_colist_le'.
  apply coop_intro2...
  intro i.
  simpl; unfold flip.
  generalize (prefix_cofilter f l i); intros [j Hj].
  rewrite Hj; clear Hj i.
  apply coop_elim with (i:=j) in Hall...
  simpl in Hall; unfold flip in Hall.
  revert Hall.
  generalize (prefix j l) as l'.
  clear l j.
  unfold filter.
  intro l; induction l; simpl; intro Hall.
  { constructor. }
  destruct Hall as [H0 H1].
  rewrite H0.
  apply IHl; auto.
Qed.

CoFixpoint const_colist {A} (a : A) : colist A := cocons a (const_colist a).

CoFixpoint nats (n : nat) : colist nat := cocons n (nats (S n)).

Lemma prefix_nats (n i : nat) :
  prefix i (nats n) = seq n i.
Proof. revert n; induction i; intro n; simpl; auto; rewrite IHi; auto. Qed.

Lemma fold_app {A B} (z : B) (f : A -> B -> B) (l l' : list A) :
  fold z f (l ++ l') = fold (fold z f l') f l.
Proof.
  revert z f l'; induction l; intros z f l'; simpl; auto.
  rewrite IHl; reflexivity.
Qed.

Lemma list_le_app {A} (a b : list A) :
  a ⊑ a ++ b.
Proof.
  revert b; induction a; intro b; simpl; constructor; apply IHa.
Qed.

Lemma chain_seq_prefix {A} (f : nat -> A) :
  chain (seq_prefix f).
Proof.
  unfold seq_prefix.
  intro i; revert f; induction i; simpl; intro f.
  { constructor. }
  apply list_le_app.
Qed.

(** Divergent colist that is "productive" by computing elements via
    divergent computation (e.g., big disjunction of all falses) *)

(* Definition list_existsb {A} (P : A -> bool) : list A -> bool := *)
(*   fold false (fun a x => P a || x). *)

Definition colist_existsb {A} (P : A -> bool) : colist A -> bool :=
  cofold (fun a x => P a || x).

Definition bad_bool : bool := colist_existsb (const false) (nats O).

CoFixpoint bad_stream : colist bool := cocons bad_bool bad_stream.

Lemma bad_stream_productive :
  productive (bad_stream).
Proof. cofix CH; rewrite unf_eq; constructor; auto. Qed.

Lemma bad_bool_false {A} (l : colist A) :
  colist_existsb (const false) l = false.
Proof.
  unfold colist_existsb, co; simpl; unfold compose, flip.
  apply ext, supremum_sup, supremum_const', eq_equ.
  ext i; unfold const.
  revert l; induction i; simpl; intro l; auto.
  unfold compose, flip.
  destruct l; simpl; auto; apply IHi.
Qed.

Lemma bad_stream_spec :
  bad_stream = const_colist false.
Proof.
  apply colist_ext.
  cofix CH.
  rewrite unf_eq, (@unf_eq _ (const_colist _)); simpl.
  unfold bad_bool; rewrite bad_bool_false.
  constructor; apply CH.
Qed.
