(** * Coinductive trees (cotrees) algebraic CPO. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
.
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
  aCPO
  axioms
  cpo
  misc
  order
  tactics
.

Local Open Scope order_scope.

Create HintDb cotree.

(** This is just to match the paper. In Coq, we use the Inductive and
    CoInductive mechanisms to define the actual types rather than
    taking the lfp and gfp of this functor explicitly (although the
    latter could be done but I believe it still requires the use of
    Inductive and CoInductive). *)
Variant cotreeF (X I A : Type) : Type :=
  | cobotF : cotreeF X I A
  | coleafF : A -> cotreeF X I A
  | conodeF : (I -> X) -> cotreeF X I A.

(** The type of cotrees. *)
CoInductive cotree (I A : Type) : Type :=
| cobot : cotree I A
| coleaf : A -> cotree I A
| conode : (I -> cotree I A) -> cotree I A.

(** The canonical divergent cotree. *)
CoFixpoint omega {I A} : cotree I A := conode (fun _ => omega).

Definition unf {I A} (t : cotree I A) :=
  match t with
  | cobot => cobot
  | coleaf x => coleaf x
  | conode k => conode k
  end.

Lemma unf_eq {I A} (t : cotree I A) : t = unf t.
Proof. destruct t; auto. Qed.

(** Cotrees with finite index type form an algebraic CPO, meaning that
  there is a basis of compact elements that can be used to approximate
  cotrees (see, e.g., chapter 5 of the Gunter book). We obtain the
  basis by taking the least fixed point of the tree functor rather
  than the greatest. *)

(** Finite trees. The finite trees serve as a compact basis for the
  cotrees when the index type I is finite. *)
Inductive atree (I A : Type) : Type :=
| abot : atree I A
| aleaf : A -> atree I A
| anode : (I -> atree I A) -> atree I A.

Definition bintree (A : Type) : Type := atree bool A.

Fixpoint atree_map {I A B} (f : A -> B) (t : atree I A) : atree I B :=
  match t with
  | abot => abot
  | aleaf x => aleaf (f x)
  | anode k => anode (atree_map f ∘ k)
  end.

Inductive atree_le {I A} : atree I A -> atree I A -> Prop :=
| atree_le_bot : forall t, atree_le abot t
| atree_le_leaf : forall x, atree_le (aleaf x) (aleaf x)
| atree_le_node : forall f g,
    (forall x, atree_le (f x) (g x)) ->
    atree_le (anode f) (anode g).

#[global]
  Instance Reflexive_atree_le {I A} : Reflexive (@atree_le I A).
Proof. intro t; induction t; constructor; auto. Qed.

#[global]
  Instance Transitive_atree_le {I A} : Transitive (@atree_le I A).
Proof.
  intro x; induction x; intros y z Hxy Hyz.
  - constructor.
  - inv Hxy; auto.
  - inv Hxy; inv Hyz; constructor; eauto.
Qed.

#[global]
  Instance PreOrder_atree_le {I A} : PreOrder (@atree_le I A).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_atree {I A} : OType (atree I A) :=
  { leq := atree_le }.

#[global]
  Program
  Instance PType_atree {I A} : PType (atree I A) :=
  { bot := abot }.
Next Obligation. constructor. Qed.

Lemma atree_le_antisym {I A} (a b : atree I A) :
  a ⊑ b ->
  b ⊑ a ->
  a = b.
Proof.
  intro H; induction H; intro Hle; inv Hle; auto.
  replace g with f; auto; ext x; apply H0, H3.
Qed.

Lemma equ_atree {I A} (a b : atree I A) :
  a === b -> a = b.
Proof. intro Heq; apply atree_le_antisym; apply Heq. Qed.

Fixpoint tprefix {I A} (n : nat) (t : cotree I A) : atree I A :=
  match n with
  | O => abot
  | S n' => match t with
            | cobot => abot
            | coleaf x => aleaf x
            | conode k => anode (tprefix n' ∘ k)
            end
  end.

Fixpoint coprefix {I A} (n : nat) (t : cotree I A) : cotree I A :=
  match n with
  | O => cobot
  | S n' => match t with
            | cobot => cobot
            | coleaf x => coleaf x
            | conode k => conode (coprefix n' ∘ k)
            end
  end.

Fixpoint tinj {I A} (t : atree I A) : cotree I A :=
  match t with
  | abot => cobot
  | aleaf x => coleaf x
  | anode f => conode (tinj ∘ f)
  end.

Lemma tinj_tprefix_coprefix {I A} (t : cotree I A) (n : nat) :
  tinj (tprefix n t) = coprefix n t.
Proof.
  revert t; induction n; intro t; simpl; auto.
  destruct t; simpl; auto.
  - unfold compose; f_equal; ext i; apply IHn.
Qed.

CoInductive cotree_le {I A} : cotree I A -> cotree I A -> Prop :=
| cotree_le_bot : forall t, cotree_le cobot t
| cotree_le_leaf : forall x, cotree_le (coleaf x) (coleaf x)
| cotree_le_node : forall f g,
    (forall x, cotree_le (f x) (g x)) ->
    cotree_le (conode f) (conode g).

#[global]
  Instance Reflexive_cotree_le {I A} : Reflexive (@cotree_le I A).
Proof. cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Transitive_cotree_le {I A} : Transitive (@cotree_le I A).
Proof.
  unfold Transitive.
  cofix CH; intros x y z Hxy Hyz.
  inv Hxy.
  - constructor.
  - inv Hyz; constructor.
  - inv Hyz; constructor; eauto.
Qed.

#[global]
  Instance PreOrder_cotree_le {I A} : PreOrder (@cotree_le I A).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_cotree {I A} : OType (cotree I A) :=
  { leq := cotree_le }.

#[global]
  Program
  Instance PType_cotree {I A} : PType (cotree I A) :=
  { bot := cobot }.
Next Obligation. constructor. Qed.

#[global]
  Instance monotone_conode {I A} : Proper (leq ==> leq) (@conode I A).
Proof. intros a b Hab; constructor; auto. Qed.
#[global] Hint Resolve monotone_conode : cotree.

Lemma continuous_conode {I A} :
  continuous (@conode I A).
Proof.
  intros ch Hch s Hs; split.
  - intro i; constructor; apply Hs.
  - intros x Hx.
    destruct x; try solve [specialize (Hx (S O)); inv Hx].
    constructor; apply Hs.
    intro i; specialize (Hx i); inv Hx; auto.
Qed.
#[global] Hint Resolve continuous_conode : cotree.

Lemma leq_cotree_le {I A} (a b : cotree I A) :
  a ⊑ b ->
  cotree_le a b.
Proof. auto. Qed.

CoInductive cotree_eq {I A} : cotree I A -> cotree I A -> Prop :=
| cotree_eq_bot : cotree_eq cobot cobot
| cotree_eq_leaf : forall x, cotree_eq (coleaf x) (coleaf x)
| cotree_eq_node : forall f g,
    (forall x, cotree_eq (f x) (g x)) ->
    cotree_eq (conode f) (conode g).

(** Extensionality axiom for cotrees. *)
Axiom cotree_ext : forall {I A} (a b : cotree I A), cotree_eq a b -> a = b.

Lemma cotree_eq_refl {I A} (t : cotree I A) :
  cotree_eq t t.
Proof. revert t; cofix CH; intros []; constructor; eauto. Qed.

#[global]
  Instance Reflexive_cotree_eq {I A} : Reflexive (@cotree_eq I A).
Proof. intro t; apply cotree_eq_refl. Qed.

Lemma cotree_eq_equ {I A} (a b : cotree I A) :
  cotree_eq a b -> a === b.
Proof.
  intro Hab; split; revert Hab; revert a b; cofix CH;
    intros a b Hab; inv Hab; try constructor; try intro x; apply CH; auto.
Qed.

Lemma equ_cotree_eq {I A} (a b : cotree I A) :
  a === b -> cotree_eq a b.
Proof.
  revert a b; cofix CH; intros a b [Hab Hba].
  inv Hab; inv Hba; constructor; try intro x;
    apply CH; split; try apply H; apply H2.
Qed.

Lemma cotree_equ_eq {I A} (a b : cotree I A) :
  a === b -> a = b.
Proof. intro H; apply cotree_ext, equ_cotree_eq; auto. Qed.

#[global]
  Instance ExtType_cotree {I A} : ExtType (cotree I A).
Proof.
  constructor; intros a b Hab; apply cotree_ext, equ_cotree_eq; auto.
Qed.

#[global]
  Instance Proper_cotree_le' {I A}
  : Proper (cotree_eq ==> cotree_eq ==> flip impl) (@cotree_le I A).
Proof.
  intros a b Hab c d Hcd Hle.
  apply cotree_eq_equ in Hab; destruct Hab.
  apply cotree_eq_equ in Hcd; destruct Hcd.
  etransitivity; eauto; etransitivity; eauto.
Qed.

Definition bstep_node {I A} (i : I) (t : atree I A) : atree I A :=
  match t with
  | anode k => k i
  | _ => abot
  end.

Definition step_node {I A} (i : I) (t : cotree I A) : cotree I A :=
  match t with
  | conode k => k i
  | _ => cobot
  end.

Definition not_cobot {I A} (t : cotree I A) : Prop :=
  match t with
  | cobot => False
  | _ => True
  end.

Definition not_abot {I A} (t : atree I A) : Prop :=
  match t with
  | abot => False
  | _ => True
  end.

Definition is_abotb {I A} (t : atree I A) : bool :=
  match t with
  | abot => true
  | _ => false
  end.

Lemma not_cobot_dec {I A} (t : cotree I A) : { not_cobot t } + { ~ not_cobot t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
  - left; constructor.
Qed.

Lemma not_abot_dec {I A} (t : atree I A) : { not_abot t } + { ~ not_abot t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
  - left; constructor.
Qed.

(* The supremum of a chain of cotrees. Uses strong LPO. *)
CoFixpoint cotree_sup {I A} (ch : nat -> cotree I A) : cotree I A :=
  match LPO_option (fun n => not_cobot_dec (ch n)) with
  | Some n => match ch n with
             | cobot => cobot
             | coleaf x => coleaf x
             | conode _ => conode (fun x => cotree_sup (step_node x ∘ ch))
             end
  | None => cobot
  end.

Lemma directed_step_node {I A} (ch : nat -> cotree I A) (x : I) :
  directed ch ->
  directed (step_node x ∘ ch).
Proof.
  intros Hch i j; specialize (Hch i j); destruct Hch as [k [Hk Hk']].
  unfold bstep_node, compose.
  exists k; split.
  - destruct (ch i) eqn:Hchi; try constructor; inv Hk; apply H1.
  - destruct (ch j) eqn:Hchj; try constructor; inv Hk'; apply H1.
Qed.

Lemma directed_bstep_node {I A} (ch : nat -> atree I A) (x : I) :
  directed ch ->
  directed (bstep_node x ∘ ch).
Proof.
  intros Hch i j; specialize (Hch i j); destruct Hch as [k [Hk Hk']].
  unfold bstep_node, compose.
  exists k; split.
  - destruct (ch i) eqn:Hchi; try constructor; inv Hk; apply H1.
  - destruct (ch j) eqn:Hchj; try constructor; inv Hk'; apply H1.
Qed.

Lemma directed_leaf_node {I A} (ch : nat -> cotree I A) i j x k :
  directed ch ->
  ch i = coleaf x ->
  ch j = conode k ->
  False.
Proof.
  intros Hch Hi Hj.
  specialize (Hch i j); destruct Hch as [l [Hl Hl']].
  rewrite Hi in Hl; rewrite Hj in Hl'.
  inv Hl; rewrite <- H in Hl'; inv Hl'.
Qed.

Lemma cotree_sup_ub {I A} (ch : nat -> cotree I A) :
  directed ch ->
  upper_bound (cotree_sup ch) ch.
Proof.
  revert ch.
  cofix CH; intros ch Hch i.
  simpl.
  replace (cotree_sup ch) with (unf (cotree_sup ch)).
  2: { rewrite <- unf_eq; reflexivity. }
  simpl.
  destruct (LPO_option (fun n : nat => not_cobot_dec (ch n))) eqn:Ho.
  - apply LPO_option_some in Ho.
    destruct (ch n) eqn:Hchn.
    + inv Ho.
    + clear Ho.
      specialize (Hch i n); destruct Hch as [k [Hk Hk']].
      rewrite Hchn in Hk'; inv Hk'.
      rewrite <- H in Hk.
      inv Hk; constructor.
    + clear Ho.
      destruct (ch i) eqn:Hchi.
      { constructor. }
      { eapply directed_leaf_node in Hchi; eauto; contradiction. }
      { constructor; intro x.
        replace (c0 x) with ((step_node x ∘ ch) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        apply CH, directed_step_node; auto. }
  - apply LPO_option_none with (n:=i) in Ho.
    destruct (ch i); try constructor; exfalso; apply Ho; constructor.
Qed.

Lemma upper_bound_step_node {I A} (k : I -> cotree I A) (ch : nat -> cotree I A) (x : I) :
  upper_bound (conode k) ch ->
  upper_bound (k x) (step_node x ∘ ch).
Proof.
  intros Hub i; specialize (Hub i); unfold compose.
  destruct (ch i) eqn:Hchi; inv Hub; simpl; auto; constructor.
Qed.

Lemma cotree_sup_const {I A} (t : cotree I A) :
  cotree_eq (cotree_sup (fun _ : nat => t)) t.
Proof.
  revert t; cofix CH; intro t.
  rewrite unf_eq; simpl.
  destruct (LPO_option (fun _ : nat => not_cobot_dec t)) eqn:H.
  - apply LPO_option_some in H.
    destruct t; constructor; intro i; unfold compose; apply CH.
  - apply LPO_option_none with (n:=O) in H.
    destruct t; try constructor; exfalso; apply H; constructor.
Qed.

Lemma upper_bound_coleaf_cotree_sup {I A} (ch : nat -> cotree I A) (a : A) :
  upper_bound (coleaf a) ch ->
  cotree_sup ch ⊑ coleaf a.
Proof.
  revert ch a; cofix CH; intros ch a Ha.
  rewrite unf_eq; simpl.
  destruct (LPO_option (fun n : nat => not_cobot_dec (ch n))) eqn:Ho.
  2: { constructor. }
  destruct (ch n) eqn:Hchn.
  - constructor.
  - specialize (Ha n); rewrite Hchn in Ha; auto.
  - specialize (Ha n); rewrite Hchn in Ha; inv Ha.
Qed.

Lemma cotree_sup_lub {I A} (ch : nat -> cotree I A) (ub : cotree I A) :
  directed ch ->
  upper_bound ub ch ->
  cotree_sup ch ⊑ ub.
Proof.
  revert ch ub.
  cofix CH; intros ch ub Hch Hub.
  destruct ub.
  - replace ch with (fun _ : nat => @cobot I A).
    + rewrite cotree_sup_const; reflexivity.
    + ext i; specialize (Hub i); destruct (ch i); auto; inv Hub.
  - apply upper_bound_coleaf_cotree_sup; auto.
  - rewrite unf_eq; simpl.
    destruct (LPO_option (fun n : nat => not_cobot_dec (ch n))) eqn:Ho.
    2: { constructor. }
    destruct (ch n) eqn:Hchn.
    + constructor.
    + specialize (Hub n); rewrite Hchn in Hub; inv Hub.
    + constructor; intro i; apply CH.
      * apply directed_step_node; auto.
      * eapply upper_bound_step_node; eauto.
Qed.

Lemma cotree_sup_supremum {I A} (ch : nat -> cotree I A) :
  directed ch ->
  supremum (cotree_sup ch) ch.
Proof.
  intro Hch; split.
  - apply cotree_sup_ub; auto.
  - intros; apply cotree_sup_lub; auto.
Qed.

#[global]
  Instance dCPO_cotree {I A} : dCPO (@cotree I A).
Proof.
  constructor; intros ch Hch.
  exists (cotree_sup ch); apply cotree_sup_supremum; auto.
Qed.
#[global] Hint Resolve dCPO_cotree : cotree.

Lemma supremum_coleaf {I A} (x : A) (ch : nat -> cotree I A) :
  supremum (coleaf x) ch ->
  exists i, ch i = coleaf x.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_cobot_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn.
    + inv H.
    + inv Hub; exists n; auto.
    + inv Hub.
  - assert (H: upper_bound cobot ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor.
      + inv Hub. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_aleaf {I A} (x : A) (ch : nat -> atree I A) :
  supremum (aleaf x) ch ->
  exists i, ch i = aleaf x.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_abot_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn.
    + inv H.
    + inv Hub; exists n; auto.
    + inv Hub.
  - assert (H: upper_bound abot ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor.
      + inv Hub. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_conode {I A} (f : I -> cotree I A) (ch : nat -> cotree I A) :
  supremum (conode f) ch ->
  exists i g, ch i = conode g.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_cobot_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn.
    + inv H.
    + inv Hub.
    + exists n, c; auto.
  - assert (H: upper_bound cobot ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + inv Hub.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_anode' {I A} (f : I -> atree I A) (ch : nat -> atree I A) :
  supremum (anode f) ch ->
  exists i g, ch i = anode g /\ g ⊑ f.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_abot_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn; inv H; inv Hub; exists n, a; auto.
  - assert (H: upper_bound abot ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + inv Hub.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_step_node {I A} (k : I -> cotree I A) (ch : nat -> cotree I A) (x : I) :
  supremum (conode k) ch ->
  supremum (k x) (step_node x ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (conode (fun z => if classicT (z = x) then y else k z)) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; intro z.
        destruct_classic; subst; auto. }
    apply Hlub in H; inv H.
    specialize (H2 x).
    destruct_classic; auto; congruence.
Qed.

Lemma supremum_bstep_node {I A} (k : I -> atree I A) (ch : nat -> atree I A) (x : I) :
  supremum (anode k) ch ->
  supremum (k x) (bstep_node x ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (anode (fun z => if classicT (z = x) then y else k z)) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; intro z.
        destruct_classic; subst; auto. }
    apply Hlub in H; inv H.
    specialize (H2 x).
    destruct_classic; auto; congruence.
Qed.

Lemma supremum_cobot {I A} (ch : nat -> cotree I A) :
  supremum cobot ch ->
  ch = const cobot.
Proof.
  intros [Hub Hlub]; ext i; unfold const.
  specialize (Hub i); inv Hub; reflexivity.
Qed.

Lemma conode_supremum {I A} (k : I -> cotree I A) (ch : nat -> I -> cotree I A) :
  (forall i, supremum (k i) (flip ch i)) ->
  supremum (conode k) (fun i => conode (ch i)).
Proof.
  intro Hsup; split.
  - intro i; constructor; intro x; apply Hsup.
  - intros x Hx; destruct x; try solve [specialize (Hx (S O)); inv Hx].
    constructor; intro x; apply Hsup.
    intro i; specialize (Hx i); inv Hx; apply H1.
Qed.

Lemma tprefix_monotone {I A} (n : nat) :
  monotone (@tprefix I A n).
Proof.
  induction n; intros a b Hab; simpl; try constructor.
  destruct a; inv Hab; constructor; intro i; apply IHn; simpl; auto.
Qed.

Lemma tprefix_monotone' {I A} (t : cotree I A) :
  monotone (fun n => tprefix n t).
Proof.
  intro i; revert t; induction i; intros t j Hij; simpl.
  - apply atree_le_bot.
  - destruct t.
    + apply atree_le_bot.
    + destruct j; simpl.
      * inv Hij.
      * constructor.
    + destruct j; simpl.
      * inv Hij.
      * constructor.
        intro x; eapply IHi; simpl in *; lia.
Qed.

Lemma tprefix_continuous {I A} (n : nat) :
  continuous (@tprefix I A n).
Proof.
  induction n; intros ch Hch x Hx; unfold compose; simpl.
  { apply supremum_const. }
  destruct x.
  - apply supremum_cobot in Hx.
    apply supremum_const'.
    apply equ_arrow; intro i; rewrite Hx; reflexivity.
  - apply supremum_coleaf in Hx.
    destruct Hx as [i Hi].
    apply const_supremum''.
    + intro j; specialize (Hch i j); destruct Hch as [k [Hk Hk']].
      rewrite Hi in Hk; inv Hk.
      rewrite <- H in Hk'; inv Hk'; constructor.
    + exists i; rewrite Hi; reflexivity.
  - assert (Hc: forall x, supremum (c x) (step_node x ∘ ch)).
    { intro i; apply supremum_step_node; auto. }
    split.
    + intro i; destruct (ch i) eqn:Hchi; simpl.
      * constructor.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i); rewrite Hchi in Hub; inv Hub.
      * constructor; intro x.
        replace ((tprefix n ∘ c0) x) with ((tprefix n ∘ (step_node x ∘ ch)) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        specialize (Hc x).
        apply IHn; auto.
        apply directed_step_node; auto.
    + intros ub Hub; destruct ub.
      * assert (H: forall i, ch i = cobot).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); auto; inv Hub. }
        assert (supremum cobot ch).
        { apply supremum_const'; apply equ_arrow; intro i.
          unfold const; rewrite H; reflexivity. }
        eapply supremum_unique in Hx; eauto.
        apply equ_cotree_eq in Hx; inv Hx.
      * assert (H: upper_bound (coleaf a) ch).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); inv Hub; constructor. }
        apply Hx in H; inv H.
      * constructor; intro x.
        eapply IHn.
        2: { eauto. }
        { apply directed_step_node; auto. }
        intro i; unfold compose.
        specialize (Hub i); simpl in Hub.
        destruct (ch i) eqn:Hchi; simpl.
        { destruct n; constructor. }
        { destruct n; constructor. }
        inv Hub; apply H1.
Qed.

Lemma cotree_le_atree_le {I A} (a b : atree I A) :
  cotree_le (tinj a) (tinj b) ->
  atree_le a b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor.
  - destruct b; inv Hab; constructor; intro i; apply H, H2.
Qed.

Lemma atree_le_cotree_le {I A} (a b : atree I A) :
  atree_le a b ->
  cotree_le (tinj a) (tinj b).
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor.
  - destruct b; inv Hab; constructor; intro i; apply H, H2.
Qed.

Lemma chain_tprefix {I A} (t : cotree I A) :
  chain (fun n : nat => tprefix n t).
Proof.
  apply monotone_chain.
  - apply tprefix_monotone'.
  - intro i; simpl; lia.
Qed.

Lemma bintree_compact {A} (t : bintree A) (ch : nat -> bintree A) :
  directed ch ->
  supremum t ch ->
  exists i, ch i = t.
Proof.
  revert ch; induction t; intros ch Hch Ht.
  - exists O; apply equ_atree; split; try constructor; apply Ht.
  - apply supremum_aleaf in Ht; auto.
  - destruct (is_abotb (a false)) eqn:H'.
    { destruct (a false) eqn:Hal; inv H'.
      destruct (is_abotb (a true)) eqn:H'.
      - destruct (a true) eqn:Har; inv H'.
        apply supremum_anode' in Ht.
        destruct Ht as [i [g [Hi Hg]]].
        exists i; rewrite Hi; f_equal; ext b; destruct b.
        + specialize (Hg true); rewrite Har in Hg; inv Hg; auto.
        + specialize (Hg false); rewrite Hal in Hg; inv Hg; auto.
      - pose proof Ht as Hr.
        apply supremum_bstep_node with (x:=true) in Hr.
        apply H in Hr; clear H.
        2: { apply directed_bstep_node; auto. }
        destruct Hr as [j Hr]; exists j.
        unfold bstep_node, compose in Hr.
        destruct (ch j) eqn:Hchj; try solve [rewrite <- Hr in H'; inv H'].
        f_equal; ext b; destruct b; auto; rewrite Hal.
        destruct Ht as [Hub Hlub].
        specialize (Hub j); rewrite Hchj in Hub; inv Hub.
        specialize (H1 false); rewrite Hal in H1.
        inv H1; auto. }
    { destruct (is_abotb (a true)) eqn:H''.
      - destruct (a true) eqn:Har; inv H''.
        pose proof Ht as Hr.
        apply supremum_bstep_node with (x:=false) in Hr.
        apply H in Hr; clear H.
        2: { apply directed_bstep_node; auto. }
        destruct Hr as [j Hr]; exists j.
        unfold bstep_node, compose in Hr.
        destruct (ch j) eqn:Hchj; try solve [rewrite <- Hr in H'; inv H'].
        f_equal; ext b; destruct b; auto; rewrite Har.
        destruct Ht as [Hub Hlub].
        specialize (Hub j); rewrite Hchj in Hub; inv Hub.
        specialize (H1 true); rewrite Har in H1.
        inv H1; auto.
      - pose proof Ht as Hl.
        apply supremum_bstep_node with (x:=false) in Hl.
        pose proof Ht as Hr.
        apply supremum_bstep_node with (x:=true) in Hr.
        apply H in Hl.
        2: { apply directed_bstep_node; auto. }
        apply H in Hr.
        2: { apply directed_bstep_node; auto. }
        clear H.
        destruct Hl as [i Hi].
        destruct Hr as [j Hj].
        specialize (Hch i j); destruct Hch as [k [Hk Hk']]; exists k.
        unfold bstep_node, compose in *.
        destruct (ch k) eqn:Hchk.
        + inv Hk; rewrite <- H0 in Hi; rewrite <- Hi in H'; inv H'.
        + inv Hk; rewrite <- H0 in Hi; rewrite <- Hi in H'; inv H'.
        + inv Hk.
          { rewrite <- H0 in Hi; rewrite <- Hi in H'; inv H'. }
          rewrite <- H in Hi.
          inv Hk'.
          { rewrite <- H2 in Hj; rewrite <- Hj in H''; inv H''. }
          rewrite <- H0 in Hj.
          destruct Ht as [Hub Hlub].
          specialize (Hub k); rewrite Hchk in Hub; inv Hub.
          f_equal; ext b; destruct b.
          * apply equ_atree; split.
            { apply H5. }
            { rewrite <- Hj; apply H3. }
          * apply equ_atree; split.
            { apply H5. }
            { rewrite <- Hi; apply H1. } }
Qed.

Lemma coprefix_le {I A} (t : cotree I A) (n : nat) :
  coprefix n t ⊑ t.
Proof.
  revert t; induction n; intro t; simpl; try constructor.
  destruct t; constructor; intro x; apply IHn.
Qed.

Lemma coprefix_supremum {I A} (t : cotree I A) :
  supremum t (fun n => coprefix n t).
Proof.
  split.
  - intro i; apply coprefix_le.
  - revert t; cofix CH; intros t ub Hub.
    destruct ub.
    + specialize (Hub (S O)).
      destruct t; inv Hub; constructor.
    + specialize (Hub (S O)).
      destruct t; inv Hub; constructor.
    + destruct t.
      * constructor.
      * specialize (Hub (S O)); inv Hub.
      * constructor; intro x; apply CH.
        intro i.
        specialize (Hub (S i)); simpl in Hub.
        inv Hub; apply H1.
Qed.

#[global]
  Instance Compact_atree {A} : Compact (atree bool A).
Proof.
  constructor; intros a f Hf Ha.
  apply bintree_compact in Ha; auto.
  destruct Ha as [i Ha]; subst; exists i; reflexivity.
Qed.

#[global]
  Instance Dense_cotree {I A} : Dense (cotree I A) (atree I A) :=
  { incl := tinj
  ; ideal := flip tprefix }.

#[global]
  Instance aCPO_cotree {A} : aCPO (cotree bool A) (atree bool A).
Proof.
  constructor.
  - intros a b; split.
    + apply atree_le_cotree_le.
    + apply cotree_le_atree_le.
  - apply chain_tprefix.
  - intros a b Hab i; apply tprefix_monotone; auto.
  - apply tprefix_continuous.
  - intro a; simpl; unfold compose, flip.
    replace (fun i => tinj (tprefix i a)) with (fun i => coprefix i a).
    + apply coprefix_supremum.
    + ext i; rewrite tinj_tprefix_coprefix; reflexivity.
Qed.

Inductive atree_cotree_le {I A} : atree I A -> cotree I A -> Prop :=
| atree_cotree_le_bot : forall t, atree_cotree_le abot t
| atree_cotree_le_leaf : forall x, atree_cotree_le (aleaf x) (coleaf x)
| atree_cotree_le_node : forall f g,
    (forall i, atree_cotree_le (f i) (g i)) ->
    atree_cotree_le (anode f) (conode g).

#[global]
  Instance antimonotone_atree_cotree_le {I A}
  : Proper (leq ==> flip leq) (@atree_cotree_le I A).
Proof.
  intro a; induction a; intros b Hab c Hc; inv Hab; auto.
  - constructor.
  - inv Hc; constructor; intro i.
    specialize (H1 i); apply H in H1; apply H1; auto.
Qed.
#[global] Hint Resolve antimonotone_atree_cotree_le : cotree.

Definition cotree_le' {A} : cotree bool A -> cotree bool A -> Prop :=
  coop atree_cotree_le.

Lemma atree_cotree_le_ideal {I A} (a b : cotree I A) (i : nat) :
  cotree_le a b ->
  atree_cotree_le (ideal a i) b.
Proof.
  revert a b; induction i; intros a b Hab; simpl; unfold flip; simpl.
  - constructor.
  - simpl in IHi; unfold flip in IHi.
    destruct a; inv Hab; constructor; auto.
    intro x; apply IHi, H0.
Qed.

Lemma cotree_le'_inv_leaf {A} (x : A) (t : cotree bool A) :
  cotree_le' (coleaf x) t ->
  t = coleaf x.
Proof.
  intro Hle.
  apply coop_elim2 with (i := S O) in Hle; eauto with cotree order.
  simpl in Hle; unfold flip in Hle; simpl in Hle.
  destruct t; inv Hle; reflexivity.
Qed.

Lemma cotree_le'_inv_node {A} (f : bool -> cotree bool A) (t : cotree bool A) :
  cotree_le' (conode f) t ->
  exists g, t = conode g /\ forall i, cotree_le' (f i) (g i).
Proof.
  intro Hle.
  destruct t; try solve [apply coop_elim2 with (i := S O) in Hle;
                         eauto with cotree order; inv Hle].
  exists c; split; auto.
  intro b; apply coop_intro2; eauto with cotree order; intro i.
  apply coop_elim2 with (i := S i) in Hle; eauto with cotree order.
  inv Hle; apply H1.
Qed.

Lemma cotree_le_cotree_le' {A} (a b : cotree bool A) :
  cotree_le a b <-> cotree_le' a b.
Proof.
  split.
  - intro Hab.
    unfold cotree_le'.
    eapply coop_intro2; eauto with cotree order.
    intro i; apply atree_cotree_le_ideal; auto.
  - revert a b; cofix CH; intros a b Hab.
    destruct a.
    + constructor.
    + apply cotree_le'_inv_leaf in Hab; subst; constructor.
    + apply cotree_le'_inv_node in Hab.
      destruct Hab as [g [? Hg]]; subst.
      constructor; intro b; apply CH, Hg.
Qed.

Fixpoint tfold {I A B}
  (z : B) (f : A -> B) (g : (I -> B) -> B) (t : atree I A) : B :=
  match t with
  | abot => z
  | aleaf x => f x
  | anode k => g (tfold z f g ∘ k)
  end.

#[global]
  Instance monotone_tfold {I A B} `{OType B} (z : B) (f : A -> B) (g : (I -> B) -> B)
  {Hz : forall b, z ⊑ tfold z f g b}
  {Hg : Proper (leq ==> leq) g}
  : Proper (leq ==> leq) (tfold z f g).
Proof.
  intro a; revert Hz Hg; revert f;
    induction a; intros f Hz Hg b Hab; inv Hab; simpl.
  - apply Hz.
  - reflexivity.
  - apply Hg; intro x; apply H0; auto; apply H2.
Qed.
#[global] Hint Resolve monotone_tfold : cotree.

#[global]
  Instance antimonotone_tfold {I A B} `{OType B}
  (z : B) (f : A -> B) (h : (I -> B) -> B)
  {Hz : forall b, tfold z f h b ⊑ z}
  {Hh : Proper (leq ==> leq) h}
  : Proper (leq ==> flip leq) (tfold z f h).
Proof.
  intro a; revert Hz Hh; revert f;
    induction a; simpl; unfold flip; intros f Hz Hh b Hab; inv Hab.
  - apply Hz.
  - reflexivity.
  - apply Hh.
    intro x; unfold compose; simpl.
    eapply H0; auto; apply H2.
Qed.
#[global] Hint Resolve antimonotone_tfold : cotree.

(** Computation lemmas for co tfolds. *)

Lemma co_tfold_bot {A B} `{dCPO B} (z : B) (f : A -> B) (h : (bool -> B) -> B) :
  co (tfold z f h) cobot === z.
Proof.
  apply supremum_sup, supremum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma co_tfold_bot' {A B} `{o : OType B} `{@dCPO B o} `{@ExtType B o}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) :
  co (tfold z f h) cobot = z.
Proof. apply ext, co_tfold_bot. Qed.

Lemma co_tfold_leaf {A B} `{dCPO B}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) (x : A) :
  z ⊑ f x ->
  co (tfold z f h) (coleaf x) === f x.
Proof.
  intro Hz.
  apply supremum_sup.
  apply supremum_eventually_constant_at.
  { intros []; simpl; auto; reflexivity. }
  exists (S O); intros n Hn; destruct n; try lia; reflexivity.
Qed.

Lemma co_tfold_leaf' {A B} `{o : OType B} `{@dCPO B o} `{@ExtType B o}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) (x : A) :
  z ⊑ f x ->
  co (tfold z f h) (coleaf x) = f x.
Proof. intro Hz; apply ext, co_tfold_leaf; auto. Qed.

(* Lemma co_tfold_node {A B} `{dCPO B} *)
(*   (z : B) (f : A -> B) (g : (bool -> B) -> B) (k : bool -> cotree bool A) : *)
(*   Proper (leq ==> leq) g -> *)
(*   (forall b, z ⊑ tfold z f g b) -> *)
(*   z ⊑ g (fun _ => z) -> *)
(*   co (tfold z f g) (conode k) === g (co (tfold z f g) ∘ k). *)
(* Proof. *)
(*   intros Hg Hz Hz'. *)
(*   split. *)
(*   - apply ge_dsup. *)
(*     + apply monotone_directed; eauto with cotree order. *)
(*       apply chain_directed, chain_ideal. *)
(*     + intro i; unfold compose. *)
(*       simpl; unfold flip. *)
(*       destruct i. *)
(*       * simpl. *)

Lemma co_tfold_node {A B} `{dCPO B}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) (k : bool -> cotree bool A) :
  wcontinuous h ->
  (forall b, z ⊑ tfold z f h b) ->
  z ⊑ h (fun _ => z) ->
  co (tfold z f h) (conode k) === h (co (tfold z f h) ∘ k).
Proof.
  intros Hh Hz Hhz.
  assert (Hh': monotone h).
  { apply wcontinuous_monotone; auto. }
  apply supremum_sup.
  apply shift_supremum'' with
    (f := fun i => h (fun x => tfold z f h (ideal (k x) i))); auto.
  { apply Hh.
    { apply monotone_chain.
      - intros i j Hij b; simpl; unfold flip.
        apply monotone_tfold; auto.
        apply tprefix_monotone'; auto.
      - apply chain_id. }
    { apply supremum_apply; intro x.
      apply dsup_spec.
      { apply monotone_directed; auto with cotree order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma co_tfold_node' {A B} `{o : OType B} `{@dCPO B o} `{@ExtType B o}
  (z : B) (f : A -> B) (g : (bool -> B) -> B) (k : bool -> cotree bool A) :
  wcontinuous g ->
  (forall b, z ⊑ tfold z f g b) ->
  z ⊑ g (fun _ => z) ->
  co (tfold z f g) (conode k) = g (co (tfold z f g) ∘ k).
Proof. intros Hg Hz Hg'; apply ext, co_tfold_node; auto. Qed.

(** Computation lemmas for coop tfolds. *)
Lemma coop_tfold_bot {A B} `{ldCPO B} (z : B) (f : A -> B) (h : (bool -> B) -> B) :
  coop (tfold z f h) cobot === z.
Proof.
  apply infimum_inf, infimum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma coop_tfold_leaf {A B} `{ldCPO B}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) (x : A) :
  f x ⊑ z ->
  coop (tfold z f h) (coleaf x) === f x.
Proof.
  intro Hz.
  apply infimum_inf.
  apply infimum_eventually_constant_at.
  { intros []; simpl; auto; reflexivity. }
  exists (S O); intros n Hn; destruct n; try lia; reflexivity.
Qed.

Lemma coop_tfold_node {A B} `{ldCPO B}
  (z : B) (f : A -> B) (h : (bool -> B) -> B) (k : bool -> cotree bool A) :
  dec_wcontinuous h ->
  (forall b, tfold z f h b ⊑ z) ->
  h (fun _ => z) ⊑ z ->
  coop (tfold z f h) (conode k) === h (coop (tfold z f h) ∘ k).
Proof.
  intros Hh Hz Hhz.
  assert (Hh': monotone h).
  { apply dec_wcontinuous_monotone; auto. }
  apply infimum_inf.
  apply shift_infimum'' with
    (f := fun i => h (fun x => tfold z f h (ideal (k x) i))); auto.
  { apply Hh.
    { intros i b; apply antimonotone_tfold; auto; apply chain_ideal. }
    { apply infimum_apply; intro x.
      apply dinf_spec.
      { apply antimonotone_downward_directed; auto with cotree order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Definition tcofold {A B} `{PType B} (f : A -> B) (g : (bool -> B) -> B)
  : cotree bool A -> B :=
  co (tfold ⊥ f g).

Lemma tcofold_bot {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) :
  tcofold f g cobot === ⊥.
Proof. apply co_tfold_bot. Qed.

Lemma tcofold_leaf {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) (x : A) :
  tcofold f g (coleaf x) === f x.
Proof. apply co_tfold_leaf, bot_le. Qed.

Lemma tcofold_leaf' {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  `{@ExtType B o} (f : A -> B) (g : (bool -> B) -> B) (x : A) :
  tcofold f g (coleaf x) = f x.
Proof. apply ext, co_tfold_leaf, bot_le. Qed.

Lemma tfold_le_tcofold {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  (t : cotree bool A) i (f : A -> B) g :
  Proper (leq ==> leq) g ->
  tfold ⊥ f g (tprefix i t) ⊑ tcofold f g t.
Proof.
  revert f g t; induction i; intros f g t Hg; simpl.
  { apply bot_le. }
  destruct t; simpl.
  - apply bot_le.
  - rewrite tcofold_leaf; reflexivity.
  - unfold compose. simpl.
    apply le_dsup with (i := S i).
    + apply monotone_directed; eauto with cotree order.
      apply chain_directed, chain_ideal.
    + reflexivity.
Qed.

Fixpoint cotree_fold {I A B}
  (z : B) (f : A -> B) (g : (I -> B) -> B) (n : nat) (t : cotree I A) : B :=
  match n with
  | O => z
  | S n' =>
      match t with
      | cobot => z
      | coleaf x => f x
      | conode k => g (cotree_fold z f g n' ∘ k)
      end
  end.

Lemma tfold_cotree_fold {I A B} (z : B) (f : A -> B) (g : (I -> B) -> B) (n : nat) (t : cotree I A) :
  tfold z f g (tprefix n t) = cotree_fold z f g n t.
Proof.
  revert z f g t; induction n; intros z f g t; simpl; auto.
  destruct t; simpl; auto.
  unfold compose.
  f_equal; ext i; auto.
Qed.

Lemma tcofold_node {A B} `{o : OType B} `{@PType B o} `{@dCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) (k : bool -> cotree bool A) :
  wcontinuous g ->
  tcofold f g (conode k) === g (tcofold f g ∘ k).
Proof. intro Hg; apply co_tfold_node; auto with order. Qed.

Definition tcoopfold {A B} `{TType B} (f : A -> B) (g : (bool -> B) -> B)
  : cotree bool A -> B :=
  coop (tfold ⊤ f g).

Lemma tcoopfold_bot {A B} `{o : OType B} `{@TType B o} `{@ldCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) :
  tcoopfold f g cobot === ⊤.
Proof. apply coop_tfold_bot. Qed.

Lemma tcoopfold_leaf {A B} `{o : OType B} `{@TType B o} `{@ldCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) (x : A) :
  tcoopfold f g (coleaf x) === f x.
Proof. apply coop_tfold_leaf; apply le_top. Qed.

Lemma tcoopfold_node {A B} `{o : OType B} `{@TType B o} `{@ldCPO B o}
  (f : A -> B) (g : (bool -> B) -> B) (k : bool -> cotree bool A) :
  dec_wcontinuous g ->
  tcoopfold f g (conode k) === g (tcoopfold f g ∘ k).
Proof. intro Hg; apply coop_tfold_node; auto with order. Qed.

(** Extraction primitive for tcofold. Only safe for generative cotrees
    (no occurrences of nil). *)
Extract Constant tcofold => "
  \ o p f g t ->
    case t of
      Cobot -> Prelude.error ""Cobot""
      Coleaf a -> f a
      Conode k -> g (tcofold o p f g . k)
".

Definition atree_cotree_bind {I A B} (k : A -> cotree I B) : atree I A -> cotree I B :=
  tfold ⊥ k (@conode I B).

Definition cotree_bind {A B} (t : cotree bool A) (k : A -> cotree bool B) : cotree bool B :=
  tcofold k (@conode bool B) t.

#[global]
  Instance monotone_atree_cotree_bind {I A B} (k : A -> cotree I B) :
  Proper (leq ==> leq) (atree_cotree_bind k).
Proof.
  intro a; revert k; induction a; intros k b Hab; inv Hab; simpl.
  - constructor.
  - reflexivity.
  - constructor; intro x; apply H, H1.
Qed.

(** Computation lemmas for bind. *)

Lemma cotree_bind_bot {A B} (k : A -> cotree bool B) :
  cotree_bind cobot k = cobot.
Proof.
  apply cotree_ext, equ_cotree_eq.
  unfold cotree_bind, tcofold.
  rewrite co_tfold_bot; reflexivity.
Qed.

Lemma cotree_bind_leaf {A B} (k : A -> cotree bool B) (x : A) :
  cotree_bind (coleaf x) k = k x.
Proof.
  apply cotree_ext, equ_cotree_eq.
  unfold cotree_bind, tcofold.
  rewrite co_tfold_leaf; try reflexivity; constructor.
Qed.

Lemma cotree_bind_node {A B} (k : A -> cotree bool B) (f : bool -> cotree bool A) :
  cotree_bind (conode f) k = conode (fun x => cotree_bind (f x) k).
Proof.
  apply cotree_ext, equ_cotree_eq.
  unfold cotree_bind, tcofold.
  rewrite co_tfold_node; auto with cotree order;
    try reflexivity; intros; constructor.
Qed.

Definition atree_cotree_map {I A B} (f : A -> B) : atree I A -> cotree I B :=
  tfold ⊥ (@coleaf I B ∘ f) (@conode I B).

Definition cotree_map {A B} (f : A -> B) (t : cotree bool A) : cotree bool B :=
  tcofold (@coleaf bool B ∘ f) (@conode bool B) t.

#[global]
  Instance monotone_atree_cotree_map {I A B} (f : A -> B) :
  Proper (leq ==> leq) (@atree_cotree_map I A B f).
Proof.
  intro a; revert f; induction a; intros f b Hab; inv Hab; simpl.
  - constructor.
  - reflexivity.
  - constructor; intro x; apply H, H1.
Qed.
#[global] Hint Resolve monotone_atree_cotree_map : cotree.

(* Fixpoint aremove_bot {A} (t : atree bool A) : atree bool A := *)
(*   match t with *)
(*   | abot => abot *)
(*   | aleaf x => aleaf x *)
(*   | anode k => let l := aremove_bot (k true) in *)
(*               let r := aremove_bot (k false) in *)
(*               match (l, r) with *)
(*               | (abot, _) => r *)
(*               | (_, abot) => l *)
(*               | _ => anode (fun b : bool => if b then l else r) *)
(*               end *)
(*   end. *)

(* #[global] *)
(*   Instance monotone_aremove_bot {A} : Proper (leq ==> leq) (@aremove_bot A). *)
(* Proof. *)
(*   intro a; induction a; simpl; intros b Hab. *)
(*   { constructor. } *)
(*   { inv Hab; constructor. } *)
(*   inv Hab. *)
(*   simpl. *)
(*   assert (H0: aremove_bot (a true) ⊑ aremove_bot (g true)). *)
(*   { apply H, H1. } *)
(*   assert (H2: aremove_bot (a false) ⊑ aremove_bot (g false)). *)
(*   { apply H, H1. } *)
(*   destruct (aremove_bot (g true)) eqn:HGt. *)
(*   { inv H0; auto. } *)
(*   { inv H0. *)
(*     - destruct (aremove_bot (g false)) eqn:Hgf. *)
(*       { inv H2; constructor. } *)
(*       { inv H2. *)
(*         - constructor. *)
(*         -  *)

(* Fixpoint afilter {A} (P : A -> bool) (t : atree bool A) : cotree bool A := *)
(*   match t with *)
(*   | abot => cobot *)
(*   | aleaf x => coleaf x *)
(*   | anode k => let l := afilter P (k true) in *)
(*               let r := afilter P (k false) in *)
(*               match (l, r) with *)
(*               | (coleaf x, _) => if P x then conode (fun b : bool => if b then l else r) else r *)
(*               | (_, coleaf y) => if P y then conode (fun b : bool => if b then l else r) else l *)
(*               | _ => conode (fun b : bool => if b then l else r) *)
(*               end *)
(*   end. *)

(* #[global] *)
(*   Instance monotone_afilter {A} (P : A -> bool) : *)
(*   Proper (leq ==> leq) (afilter P). *)
(* Proof. *)
(*   intros a; induction a; intros b Hab; inv Hab; simpl. *)
(*   { constructor. } *)
(*   { constructor. } *)
(*   pose proof (H1 true) as H0. *)
(*   pose proof (H1 false) as H2. *)
(*   destruct (g false) eqn:Hgf; simpl. *)
(*   - inv H2; simpl. *)
(*     destruct (g true) eqn:Hgt. *)
(*     + inv H0; simpl. *)
(*       constructor; intros []; constructor. *)
(*     + inv H0; simpl. *)
(*     + inv H0. *)
(*       * constructor. *)
(*       * simpl. *)
(*       rewrite <- Hgt. *)
(*       simpl. constructor. *)
(*       * constructor. *)
(*   destruct (afilter P (a true)) eqn:Ha. *)
(*   { simpl. *)


(* Fixpoint afilter {A} (P : A -> bool) (t : atree bool A) : cotree bool A := *)
(*   match t with *)
(*   | abot => cobot *)
(*   | aleaf x => coleaf x *)
(*   | anode k => let l := afilter P (k true) in *)
(*               let r := afilter P (k false) in *)
(*               match (l, r) with *)
(*               | (coleaf x, coleaf y) => *)
(*                   if P x then *)
(*                     if P y then conode (fun b : bool => if b then l else r) else l *)
(*                   else *)
(*                     if P y then r else cobot *)
(*               | (cobot, _) => r *)
(*               | (_, cobot) => l *)
(*               | (coleaf x, _) => if P x then conode (fun b : bool => if b then l else r) else r *)
(*               | (_, coleaf y) => if P y then conode (fun b : bool => if b then l else r) else l *)
(*               | _ => conode (fun b : bool => if b then l else r) *)
(*               end *)
(*   end. *)

(* #[global] *)
(*   Instance monotone_afilter {A} (P : A -> bool) : *)
(*   Proper (leq ==> leq) (afilter P). *)
(* Proof. *)
(*   intros a; induction a; intros b Hab; inv Hab; simpl. *)
(*   { constructor. } *)
(*   { constructor. } *)
(*   pose proof (H1 true) as H0. *)
(*   pose proof (H1 false) as H2. *)
(*   destruct (g false) eqn:Hgf; simpl. *)
(*   - inv H2; simpl. *)
(*     destruct (g true) eqn:Hgt. *)
(*     + inv H0; simpl. *)
(*       constructor; intros []; constructor. *)
(*     + inv H0; constructor. *)
(*     + inv H0. *)
(*       * constructor. *)
(*       * rewrite H2. *)
(*         rewrite <- Hgt. *)
(*         destruct (afilter P (a true)) eqn:HPa. *)
(*         { constructor. } *)
(*         destruct (afilter P (g true)) eqn:HPg. *)
(*         { rewrite Hgt in HPg. *)
(*           admit. } *)
(*         {  *)

Definition atree_cotree_filter {I A} (P : A -> bool) : atree I A -> cotree I A :=
  tfold ⊥ (fun x => if P x then coleaf x else cobot) (@conode I A).

Definition cotree_filter {A} (P : A -> bool) : cotree bool A -> cotree bool A :=
  tcofold (fun x => if P x then coleaf x else cobot) (@conode bool A).

#[global]
  Instance monotone_atree_cotree_filter {I A} (P : A -> bool) :
  Proper (leq ==> leq) (@atree_cotree_filter I A P).
Proof.
  intro a; revert P; induction a; intros P b Hab; inv Hab; simpl.
  - constructor.
  - compute; destruct (P a); constructor.
  - constructor; intro x; apply H, H1.
Qed.
#[global] Hint Resolve monotone_atree_cotree_filter : cotree.

(* Lifting a relation to atrees. *)
Inductive atreeR {I A B} (R : A -> B -> Prop) : atree I A -> atree I B -> Prop :=
| atreeR_bot : atreeR R abot abot
| atreeR_leaf : forall x y, R x y -> atreeR R (aleaf x) (aleaf y)
| atreeR_node : forall f g,
    (forall i, atreeR R (f i) (g i)) ->
    atreeR R (anode f) (anode g).

Lemma atreeR_map {I A B} (t : atree I A) (f : A -> B) :
  atreeR (fun x y => f x = y) t (atree_map f t).
Proof.
  revert f; induction t; intro f; simpl.
  - constructor.
  - constructor; reflexivity.
  - constructor; intro i; apply H.
Qed.

Lemma cotree_le_bind {A B} (a : cotree bool A) (f g : A -> cotree bool B) :
  (forall x, f x ⊑ g x) ->
  cotree_bind a f ⊑ cotree_bind a g.
Proof.
  intros Hfg.
  apply cotree_le_cotree_le'. 
  unfold cotree_le'.
  apply coop_intro2; eauto with cotree order.
  intro i; simpl; unfold flip; simpl.
  revert Hfg; revert a f g.
  induction i; intros a f g Hfg; simpl.
  { constructor. }
  destruct a.
  - rewrite 2!cotree_bind_bot; constructor.
  - rewrite 2!cotree_bind_leaf.
    specialize (Hfg a); inv Hfg; constructor.
    + intro b; apply atree_cotree_le_ideal; auto.
  - rewrite 2!cotree_bind_node; constructor; intro b; apply IHi; auto.
Qed.

(** This can't be defined as a comorphism because (A -> cotree I B) is
    not an aCPO in general. *)
Definition cotree_iter_F {I A} (f : I -> cotree bool (I + A))
  : (I -> cotree bool A) -> I -> cotree bool A :=
  fun g i => cotree_bind (f i) (fun lr => match lr with
                                    | inl j => g j
                                    | inr x => coleaf x
                                    end).

Definition cotree_iter {I A} (f : I -> cotree bool (I + A)) (z : I) : cotree bool A :=
  iter (cotree_iter_F f) (const cobot) z.

Lemma monotone_cotree_iter_F {I A} (f : I -> cotree bool (I + A)) :
  monotone (cotree_iter_F f).
Proof.
  intros g g' Hg i.
  unfold cotree_iter_F.
  apply cotree_le_bind.
  intros []; try constructor; apply Hg.
Qed.
#[global] Hint Resolve monotone_cotree_iter_F : cotree.

Lemma co_tinj_t {A} (t : cotree bool A) :
  co tinj t = t.
Proof.
  cut (co incl t === t).
  { intro H; apply cotree_ext, equ_cotree_eq; apply H. }
  apply co_incl_id'.
Qed.

Lemma supremum_cotree_bind {A B}
  (t : cotree bool A) (f : A -> cotree bool B) (g : nat -> A -> cotree bool B) :
  directed g ->
  supremum f g ->
  supremum (cotree_bind t f) (fun i : nat => cotree_bind t (g i)).
Proof.
  intros Hch Hsup.
  assert (forall x, supremum (f x) (fun i : nat => g i x)).
  { intro x; apply apply_supremum; auto. }
  split.
  - intro i; apply cotree_le_bind; intro x; apply H.
  - intros x Hx.
    unfold upper_bound in Hx.
    apply cotree_le_cotree_le'.
    apply coop_intro2; eauto with cotree order.
    intro i; unfold uncurry; simpl; unfold flip.
    revert Hsup H Hx.
    revert f x t.
    induction i; simpl; intros f x t Hsup H Hx.
    { constructor. }
    destruct t.
    + rewrite cotree_bind_bot; constructor.
    + rewrite cotree_bind_leaf.
      assert (Hle: cotree_le (f a) x).
      { apply H; intro j; specialize (Hx j).
        rewrite cotree_bind_leaf in Hx; apply Hx. }
      destruct (f a) eqn:Hfa.
      * constructor.
      * inv Hle; constructor.
      * inv Hle; constructor.
        intro b; unfold compose.
        apply atree_cotree_le_ideal; auto.
    + rewrite cotree_bind_node.
      pose proof Hx as Hx'.
      specialize (Hx i); rewrite cotree_bind_node in Hx.
      inv Hx.
      constructor.
      intro b.
      apply IHi; auto.
      intro j; specialize (Hx' j); rewrite cotree_bind_node in Hx'.
      inv Hx'; auto.
      apply H3.
Qed.

Lemma wcontinuous_cotree_iter_F {I A} (f : I -> cotree bool (I + A)) :
  wcontinuous (cotree_iter_F f).
Proof.
  intros ch Hch s Hs.
  unfold cotree_iter_F.
  eapply supremum_apply.
  unfold compose.
  intro x.
  apply supremum_cotree_bind.
  { apply chain_directed; intros i []; try constructor; apply Hch. }
  split.
  - intros i []; try constructor; apply Hs.
  - intros g Hg [].
    + unfold upper_bound in Hg. simpl in Hg.
      pose proof Hg as Hg'.
      specialize (Hg O (inl i)); simpl in Hg.
      assert (Hsi: supremum (s i) (fun j => ch j i)).
      { apply apply_supremum; auto. }
      apply Hsi.
      intro j.
      specialize (Hg' j (inl i)); simpl in Hg'; auto.
    + unfold upper_bound in Hg; simpl in Hg.
      pose proof Hg as Hg'.
      specialize (Hg O (inr a)); simpl in Hg.
      inv Hg; reflexivity.
Qed.

Lemma continuous_cotree_iter_F {I A} (f : I -> cotree bool (I + A)) :
  continuous (cotree_iter_F f).
Proof.
  intros ch Hch s Hs.
  unfold cotree_iter_F.
  eapply supremum_apply.
  unfold compose.
  intro x.
  apply supremum_cotree_bind.
  { intros i j; simpl.
    specialize (Hch i j); destruct Hch as [k [Hk Hk']].
    exists k; split.
    - intros [y|a]; try constructor; apply Hk.
    - intros [y|a]; try constructor; apply Hk'. }
  split.
  - intros i []; try constructor; apply Hs.
  - intros g Hg [].
    + unfold upper_bound in Hg. simpl in Hg.
      pose proof Hg as Hg'.
      specialize (Hg O (inl i)); simpl in Hg.
      assert (Hsi: supremum (s i) (fun j => ch j i)).
      { apply apply_supremum; auto. }
      apply Hsi.
      intro j.
      specialize (Hg' j (inl i)); simpl in Hg'; auto.
    + unfold upper_bound in Hg; simpl in Hg.
      pose proof Hg as Hg'.
      specialize (Hg O (inr a)); simpl in Hg.
      inv Hg; reflexivity.
Qed.

(** Unfolding lemma for cotree_iter. *)
Lemma cotree_iter_unfold {I A} (f : I -> cotree bool (I + A)) (i : I) :
  cotree_iter f i = cotree_bind (f i) (fun lr => match lr with
                                              | inl j => cotree_iter f j
                                              | inr x => coleaf x
                                              end).
Proof.
  apply cotree_ext, equ_cotree_eq.
  unfold cotree_iter.
  assert (iter (cotree_iter_F f) (const cobot) ===
            cotree_iter_F f (iter (cotree_iter_F f) (const cobot))).
  { apply iter_unfold.
    - apply continuous_wcontinuous, continuous_cotree_iter_F.
    - constructor. }
  rewrite equ_arrow in H; apply H.
Qed.

(** Computation lemmas for cotree_map. *)

Lemma cotree_map_bot {A B} (f : A -> B) :
  @cotree_map A B f cobot = cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_map, tcofold.
  rewrite co_tfold_bot; reflexivity.
Qed.

Lemma cotree_map_leaf {A B} (f : A -> B) (x : A) :
  @cotree_map A B f (coleaf x) = coleaf (f x).
Proof.
  apply cotree_equ_eq.
  unfold cotree_map, tcofold.
  rewrite co_tfold_leaf; try reflexivity; constructor.
Qed.

Lemma cotree_map_node {A B} (f : A -> B) (k : bool -> cotree bool A) :
  cotree_map f (conode k) = conode (cotree_map f ∘ k).
Proof.
  apply cotree_equ_eq.
  unfold cotree_map, tcofold.
  rewrite co_tfold_node; auto with cotree order;
    try reflexivity; intros; constructor.
Qed.

(** Computation lemmas for cotree_filter. *)

Lemma cotree_filter_bot {A} (P : A -> bool) :
  @cotree_filter A P cobot = cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_filter, tcofold.
  rewrite co_tfold_bot; reflexivity.
Qed.

Lemma cotree_filter_leaf {A} (P : A -> bool) (x : A) :
  @cotree_filter A P (coleaf x) = if P x then coleaf x else cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_filter, tcofold.
  rewrite co_tfold_leaf; try reflexivity; intros; constructor.
Qed.

Lemma cotree_filter_node {A} (P : A -> bool) (k : bool -> cotree bool A) :
  cotree_filter P (conode k) = conode (cotree_filter P ∘ k).
Proof.
  apply cotree_equ_eq.
  unfold cotree_filter, tcofold.
  rewrite co_tfold_node; auto with cotree order;
    try reflexivity; intros; constructor.
Qed.

Definition atree_some {I A} (P : A -> Prop) : atree I A -> Prop :=
  tfold False P (fun k => exists i, k i).

Definition atree_all {I A} (P : A -> Prop) : atree I A -> Prop :=
  tfold True P (fun k => forall i, k i).

Definition cotree_some {A} (P : A -> Prop) : cotree bool A -> Prop :=
  co (atree_some P).

Definition cotree_all {A} (P : A -> Prop) : cotree bool A -> Prop :=
  coop (atree_all P).

Lemma monotone_exists {I} :
  Proper (leq ==> leq) (fun k : I -> Prop => exists i : I, k i).
Proof.
  intros f g; simpl; unfold impl; intros Hfg [i Hi].
  exists i; apply Hfg, Hi.
Qed.
#[global] Hint Resolve monotone_exists : cotree.

#[global]
  Instance monotone_atree_some {I A} (P : A -> Prop) : Proper (leq ==> leq) (@atree_some I A P).
Proof. apply monotone_tfold; auto with cotree order; intros ? []. Qed.
#[global] Hint Resolve monotone_atree_some : cotree.

Lemma cotree_some_bot {A} (P : A -> Prop) :
  ~ cotree_some P cobot.
Proof.
  intro HC; apply co_elim in HC; eauto with cotree order.
  destruct HC as [[] []].
Qed.

(** Introduction rule 1 for cotree_some. *)
Lemma cotree_some_intro_leaf {A} (P : A -> Prop) (a : A) :
  P a ->
  cotree_some P (coleaf a).
Proof with eauto with order cotree.
  unfold cotree_some, atree_some.
  rewrite co_tfold_leaf...
  intros [].
Qed.

(** Introduction rule 2 for cotree_some. *)
Lemma cotree_some_intro_node {A} (P : A -> Prop) (b : bool) (k : bool -> cotree bool A) :
  cotree_some P (k b) ->
  cotree_some P (conode k).
Proof with eauto with order cotree.
  unfold cotree_some, atree_some.
  rewrite co_tfold_node...
  { apply continuous_wcontinuous, continuous_exists. }
  { intros ? []. }
  intros [].
Qed.

(** Elimination rule 1 for cotree_some. *)
Lemma cotree_some_elim_leaf {A} (P : A -> Prop) (a : A) :
  cotree_some P (coleaf a) ->
  P a.
Proof with eauto with order cotree.
  unfold cotree_some, atree_some.
  rewrite co_tfold_leaf...
  intros [].
Qed.

(** Elimination rule 2 for cotree_some. *)
Lemma cotree_some_elim_node {A} (P : A -> Prop) (k : bool -> cotree bool A) :
  cotree_some P (conode k) ->
  exists b, cotree_some P (k b).
Proof with eauto with order cotree.
  unfold cotree_some, atree_some.
  rewrite co_tfold_node...
  { apply continuous_wcontinuous, continuous_exists. }
  { intros ? []. }
  intros [].
Qed.

Corollary continuous_cotree_some {A} (P : A -> Prop) :
  continuous (cotree_some P).
Proof. apply continuous_co, monotone_atree_some. Qed.

Lemma monotone_forall {I} :
  Proper (leq ==> leq) (fun k : I -> Prop => forall i : I, k i).
Proof. intros f g; simpl; unfold impl; intros Hfg Hf i; apply Hfg, Hf. Qed.
#[global] Hint Resolve monotone_forall : cotree.

#[global]
  Instance antimonotone_atree_all {I A} (P : A -> Prop)
  : Proper (leq ==> flip leq) (@atree_all I A P).
Proof.
  apply antimonotone_tfold; auto with cotree order; intros ? ?; constructor.
Qed.
#[global] Hint Resolve antimonotone_atree_all : cotree.

(** Introduction rule 1 for cotree_all. *)
Lemma cotree_all_intro_leaf {A} (P : A -> Prop) (a : A) :
  P a ->
  cotree_all P (coleaf a).
Proof with eauto with order cotree.
  unfold cotree_all, atree_all.
  rewrite coop_tfold_leaf...
  intro; apply I.
Qed.

(** Introduction rule 2 for cotree_all. *)
Lemma cotree_all_intro_node {A} (P : A -> Prop) (k : bool -> cotree bool A) :
  (forall b, cotree_all P (k b)) ->
  cotree_all P (conode k).
Proof with eauto with order cotree.
  unfold cotree_all, atree_all.
  rewrite coop_tfold_node...
  { apply dec_continuous_dec_wcontinuous, dec_continuous_forall. }
  { intros ? ?; apply I. }
  intro; apply I.
Qed.

(** Elimination rule 1 for cotree_all. *)
Lemma cotree_all_elim_leaf {A} (P : A -> Prop) (a : A) :
  cotree_all P (coleaf a) ->
  P a.
Proof with eauto with order cotree.
  unfold cotree_all, atree_all.
  rewrite coop_tfold_leaf...
  intro; apply I.
Qed.

(** Elimination rule 2 for cotree_all. *)
Lemma cotree_all_elim_node {A} (P : A -> Prop) (k : bool -> cotree bool A) (b : bool) :
  cotree_all P (conode k) ->
  cotree_all P (k b).
Proof with eauto with order cotree.
  unfold cotree_all, atree_all.
  rewrite coop_tfold_node...
  { intro H; apply H. }
  { apply dec_continuous_dec_wcontinuous, dec_continuous_forall. }
  { intros ? ?; apply I. }
  intro; apply I.
Qed.

Corollary cocontinuous_cotree_all {A} (P : A -> Prop) :
  cocontinuous (cotree_all P).
Proof. apply cocontinuous_coop, antimonotone_atree_all. Qed.

Lemma atree_some_exists {I A} (P : A -> Prop) (t : atree I A) :
  atree_some P t <-> exists x, atree_some (eq x) t /\ P x.
Proof.
  unfold atree_some.
  split.
  - revert P; induction t; simpl; intros P Hsome; firstorder.
    apply H in H0; destruct H0; firstorder.
  - revert P; induction t; simpl; intros P [x [Hsome Hx]]; subst; firstorder.
    eexists; apply H; exists x; split; eauto.
Qed.

Lemma atree_some_map {I A B} (P : B -> Prop) (t : atree I A) (f : A -> B) :
  atree_some P (atree_map f t) ->
  atree_some (P ∘ f) t.
Proof.
  unfold atree_some.
  revert P f; induction t; unfold compose; simpl; auto; intros P f [i Hi].
  exists i; apply H; auto.
Qed.

Lemma atree_map_some {I A B} (P : B -> Prop) (t : atree I A) (f : A -> B) :
  atree_some (P ∘ f) t ->
  atree_some P (atree_map f t).
Proof.
  unfold atree_some.
  revert P f; induction t; simpl; unfold compose; intros P f; auto.
  intros [i Hi]; exists i; apply H; auto.
Qed.

Lemma tprefix_map {A B} (t : cotree bool A) (f : A -> B) (i : nat) :
  tprefix i (cotree_map f t) = atree_map f (tprefix i t).
Proof.
  revert t f; induction i; intros t f; simpl; auto.
  destruct t; simpl.
  - rewrite cotree_map_bot; reflexivity.
  - rewrite cotree_map_leaf; reflexivity.
  - rewrite cotree_map_node; f_equal; ext x; apply IHi.
Qed.

Lemma atree_some_impl {I A} (t : atree I A) (P Q : A -> Prop) :
  (forall x, P x -> Q x) ->
  atree_some P t ->
  atree_some Q t.
Proof.
  unfold atree_some.
  revert P Q; induction t; simpl; intros P Q HPQ; auto.
  intros [i Hi]; exists i; eapply H; eauto.
Qed.

Lemma atree_all_map {I A B} (P : B -> Prop) (t : atree I A) (f : A -> B) :
  atree_all (P ∘ f) t ->
  atree_all P (atree_map f t).
Proof.
  unfold atree_all.
  revert P f; induction t; simpl; firstorder.
Qed.

(* Inductive atree_disjoint {I A} `{OType A} : atree I A -> Prop := *)
(* | atree_disjoint_bot : atree_disjoint abot *)
(* | atree_disjoint_leaf : forall x, atree_disjoint (aleaf x) *)
(* | atree_disjoint_node : forall f, *)
(*     (forall i, atree_disjoint (f i)) -> *)
(*     (forall i j, i <> j -> forall x, atree_some (eq x) (f i) -> *)
(*                          atree_all (incomparable x) (f j)) -> *)
(*     atree_disjoint (anode f). *)

Lemma atree_all_impl {I A} (t : atree I A) (P Q : A -> Prop) :
  (forall x, P x -> Q x) ->
  atree_all P t ->
  atree_all Q t.
Proof.
  unfold atree_all.
  revert P Q; induction t; simpl; firstorder.
Qed.

Definition atree_disjoint {I A} `{OType A} (a b : atree I A) : Prop :=
  atree_all (fun x => atree_all (incomparable x) b) a /\
    atree_all (fun x => atree_all (incomparable x) a) b.

Definition cotree_disjoint {A} `{OType A} (a b : cotree bool A) : Prop :=
  cotree_all (fun x => cotree_all (incomparable x) b) a /\
    cotree_all (fun x => cotree_all (incomparable x) a) b.

(** Can technically be generalized to arbitrary index type but it's
    cleaner this way for our use case.*)
Inductive atree_partition {A} `{OType A} : atree bool A -> Prop :=
| atree_partition_bot : atree_partition abot
| atree_partition_leaf : forall x, atree_partition (aleaf x)
| atree_partition_node : forall f,
    (forall i, atree_partition (f i)) ->
    atree_disjoint (f true) (f false) ->
    atree_partition (anode f).

Definition cotree_partition {A} `{OType A} : cotree bool A -> Prop :=
  coop (atree_partition).

#[global]
  Instance antimonotone_atree_partition {A} `{OType A}
  : Proper (leq ==> flip leq) (@atree_partition A _).
Proof.
  intro a; induction a; simpl; intros b Hab Hb; inv Hab; auto.
  - constructor.
  - inv Hb; constructor.
    + intro i; eapply H0; eauto; apply H2.
    + destruct H4 as [H4 H4'].
      split.
      * eapply antimonotone_atree_all.
        { apply H2. }
        eapply atree_all_impl; eauto.
        simpl; intros x Hx.
        eapply antimonotone_atree_all; eauto; apply H2.
      * eapply antimonotone_atree_all.
        { apply H2. }
        eapply atree_all_impl; eauto.
        simpl; intros x Hx.
        eapply antimonotone_atree_all; eauto; apply H2.
Qed.
#[global] Hint Resolve antimonotone_atree_partition : cotree.

(* #[global] *)
(*   Instance antimonotone_atree_disjoint {I A} `{OType A} *)
(*   : Proper (leq ==> flip leq) (@atree_disjoint I A _). *)
(* Proof. *)
(*   intro a; induction a; simpl; intros b Hab Hb; inv Hab; auto. *)
(*   - constructor. *)
(*   - inv Hb; constructor. *)
(*     + intro i; eapply H0; eauto; apply H2. *)
(*     + intros i j Hij. *)
(*       eapply antimonotone_atree_all. *)
(*       { apply H2. } *)
(*       eapply atree_all_impl. *)
(*       2: { eapply H4; eauto. } *)
(*       simpl; intros x Hx. *)
(*       eapply antimonotone_atree_all; eauto; apply H2. *)
(* Qed. *)
(* #[global] Hint Resolve antimonotone_atree_disjoint : cotree. *)

Lemma atree_all_true {I A} (t : atree I A) :
  atree_all (const True) t.
Proof. unfold const; induction t; firstorder. Qed.

Lemma atree_all_true' {I A} (P : A -> Prop) (t : atree I A) :
  (forall x, P x) ->
  atree_all P t.
Proof. intro; induction t; firstorder. Qed.

Lemma atree_cotree_bind_assoc {A B C}
  (t : atree bool A) (f : A -> cotree bool B) (g : B -> cotree bool C) :
  cotree_bind (atree_cotree_bind f t) g ===
    atree_cotree_bind (fun x : A => cotree_bind (f x) g) t.
Proof.
  unfold atree_cotree_bind.
  revert f g; induction t; intros f g; simpl.
  - rewrite cotree_bind_bot; reflexivity.
  - reflexivity.
  - rewrite cotree_bind_node.
    apply cotree_eq_equ; constructor; intro b; apply equ_cotree_eq, H.
Qed.

(** cotree_bind is associative. *)
Lemma cotree_bind_assoc {A B C}
  (t : cotree bool A) (f : A -> cotree bool B) (g : B -> cotree bool C) :
  cotree_bind (cotree_bind t f) g = cotree_bind t (fun x => cotree_bind (f x) g).
Proof.
  apply ext.
  unfold cotree_bind, tcofold.
  rewrite co_co''; eauto with cotree order.
  apply Proper_co'; eauto with cotree order; try reflexivity.
  { apply monotone_compose; eauto with cotree order.
    apply monotone_co; eauto with cotree order. }
  apply equ_arrow; unfold compose; intro a.
  apply atree_cotree_bind_assoc.
Qed.

Lemma atree_cotree_bind_tinj {A} :
  atree_cotree_bind (@coleaf bool A) = tinj.
Proof.
  unfold atree_cotree_bind.
  ext t; induction t; simpl; auto.
  f_equal; ext b; unfold compose; rewrite H; reflexivity.
Qed.

(** coleaf is the identity on the right wrt bind. *)
Lemma cotree_bind_id_r {A} (t : cotree bool A) :
  cotree_bind t (@coleaf bool A) = t.
Proof.
  apply ext.
  replace t with (id t) by reflexivity.
  symmetry.
  apply co_unique'; eauto with cotree order.
  intro b.
  unfold id, incl; simpl.
  rewrite <- atree_cotree_bind_tinj; reflexivity.
Qed.

#[global]
  Instance Proper_tinj {I A} : Proper (leq ==> leq) (@tinj I A).
Proof. intros a b Hab; induction Hab; simpl; constructor; auto. Qed.

(* (* Monotone wrt the usual (disjunctive) ordering. A cotree is total *)
(*    whenever there exists one of its finite approximations that is total. *) *)
(* Inductive atotal {I A} : atree I A -> Prop := *)
(* | atotal_leaf : forall x, atotal (aleaf x) *)
(* | atotal_node : forall k, (forall x, atotal (k x)) -> atotal (anode k). *)

(* Definition total {A} : cotree bool A -> Prop := co atotal. *)

(* Lemma monotone_atotal {I A} : *)
(*   monotone (@atotal I A). *)
(* Proof. *)
(*   intros a b Hab H. *)
(*   revert Hab H. *)
(*   revert b; induction a; intros b Hab Hb; inv Hab; inv Hb; constructor. *)
(*   intro i; eapply H; eauto; apply H1. *)
(* Qed. *)
(* #[global] Hint Resolve monotone_atotal : cotree. *)

(* Lemma not_total_cobot {A} : ~ total (@cobot bool A). *)
(* Proof. *)
(*   intro HC. *)
(*   apply co_elim in HC; eauto with cotree. *)
(*   destruct HC as [[] HC]; inv HC. *)
(* Qed. *)

(* Lemma total_coleaf {A} (x : A) : *)
(*   total (coleaf x). *)
(* Proof. apply co_intro with (S O); eauto with cotree; constructor. Qed. *)

(* Lemma total_conode {A} (k : bool -> cotree bool A) (b : bool) : *)
(*   total (conode k) -> *)
(*   total (k b). *)
(* Proof. *)
(*   intro Ht; apply co_elim in Ht; eauto with cotree. *)
(*   destruct Ht as [i Ht]; simpl in Ht; unfold flip in Ht. *)
(*   destruct i; inv Ht. *)
(*   apply co_intro with i; eauto with cotree; apply H0. *)
(* Qed. *)

Definition snip {A} (t : cotree bool (unit + A)) : cotree bool A :=
  cotree_bind t (cotuple (const cobot) (@coleaf bool A)).

Corollary snip_leaf {A} (x : unit + A) :
  snip (coleaf x) = match x with
                    | inl _ => cobot
                    | inr y => coleaf y
                    end.
Proof.
  unfold snip; rewrite cotree_bind_leaf.
  destruct x; reflexivity.
Qed.

Corollary snip_bind {A B} (t : cotree bool (unit + A)) (k : unit + A -> cotree bool (unit + B)) :
  snip (cotree_bind t k) = cotree_bind t (snip ∘ k).
Proof. apply cotree_bind_assoc. Qed.

(** TODO: inductive predicate for existence of bottom. [total] is
    negation of it. *)

Inductive exists_bot {I A} : cotree I A -> Prop :=
| exists_bot_bot : exists_bot cobot
| exists_bot_node : forall k i,
    exists_bot (k i) ->
    exists_bot (conode k).

(** This still allows trees with infinite nodes and no leaves. *)
Definition total {I A} (t : cotree I A) : Prop :=
  ~ exists_bot t.

(* Inductive productive {I A} : atree I A -> Prop := *)
(* | productive_bot : productive abot *)
(* | productive_leaf : forall a, productive (aleaf a) *)
(* | productive_node : forall k, *)
(*     (forall i, atree_some (const True) (k i)) -> *)
(*     (forall i, productive (k i)) -> *)
(*     productive (anode k). *)

(* #[global] *)
(*   Instance antimonotone_productive {I A} : Proper (leq ==> flip leq) (@productive I A). *)
(* Proof. *)
(*   intro a; induction a; intros b Hab Hsome; inv Hsome; inv Hab; constructor. *)
(*   - intro i; eapply monotone_atree_some. *)
(*   intro i; eapply H. *)
(*   - apply H3. *)
(*   - apply H0. *)
(* Qed. *)
(* #[global] Hint Resolve antimonotone_productive : cotree. *)

(* Definition coproductive {A} : cotree bool A -> Prop := *)
(*   coop productive. *)
