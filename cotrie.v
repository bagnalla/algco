(** * Coinductive tries (cotries) algebraic CPO. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Vector
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
  Nat
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

From algco Require Import
  aCPO axioms cpo misc order tactics conat colist prod kleene_algebra.

Local Open Scope bool_scope.
Local Open Scope order_scope.

Create HintDb cotrie.

(** Tries with index type A and label type B. *)
Inductive trie (A B : Type) : Type :=
| trie_bot : trie A B
| trie_node : B -> (A -> trie A B) -> trie A B.

Inductive is_bot {A B} `{PType B} : trie A B -> Prop :=
| is_bot_bot : is_bot trie_bot
| is_bot_node : forall b k,
    b === ⊥ ->
    (forall a, is_bot (k a)) ->
    is_bot (trie_node b k).

Definition tlabel {A B} `{PType B} (t : trie A B) : B :=
  match t with
  | trie_bot => ⊥
  | trie_node b _ => b
  end.

Definition tdelta {A B} (t : trie A B) (a : A) : trie A B :=
  match t with
  | trie_bot => trie_bot
  | trie_node _ k => k a
  end.

Inductive trie_le {A B : Type} `{PType B} : trie A B -> trie A B -> Prop :=
| trie_le_bot : forall a b, is_bot a -> trie_le a b
| trie_le_node : forall b b' k k',
    b ⊑ b' ->
    (forall a, trie_le (k a) (k' a)) ->
    trie_le (trie_node b k) (trie_node b' k').

#[global]
  Instance Reflexive_trie_le {A B} `{PType B} : Reflexive (@trie_le A B _ _).
Proof.
  intro t; induction t.
  - repeat constructor.
  - apply trie_le_node; auto; reflexivity.
Qed.

Lemma is_bot_le {A B} `{PType B} (a b : trie A B) :
  is_bot b ->
  trie_le a b ->
  is_bot a.
Proof.
  revert b; induction a; intros b' Hb Hab.
  { constructor. }
  inv Hab.
  - inv H1; constructor; auto.
  - inv Hb.
    constructor.
    + rewrite H4 in H3; apply le_bot in H3; auto.
    + intro a; eapply H0; eauto.
Qed.  

#[global]
  Instance Transitive_trie_le {A B} `{PType B} : Transitive (@trie_le A B _ _).
Proof.
  intro x; induction x; intros y z Hxy Hyz.
  - repeat constructor.
  - inv Hxy.
    + constructor; auto.
    + inv Hyz.
      * inv H1.
        constructor; constructor.
        { rewrite H6 in H3; apply le_bot in H3; auto. }
        intro a.
        eapply is_bot_le; auto.
      * apply trie_le_node; eauto.
        etransitivity; eauto.
Qed.

#[global]
  Instance PreOrder_trie_le {A B} `{PType B} : PreOrder (@trie_le A B _ _).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_trie {A B} `{PType B} : OType (trie A B) :=
  {| leq := trie_le |}.

#[global]
  Program Instance PType_trie {A B} `{PType B} : PType (trie A B) :=
  {| bot := trie_bot |}.
Next Obligation. constructor; constructor. Qed.

#[global]
  Instance monotone_trie_node {A B} `{PType B} : Proper (leq ==> leq ==> leq) (@trie_node A B).
Proof. intros b b' Hb k k' Hk; apply trie_le_node; auto. Qed.

#[global]
  Instance monotone_tlabel {A B} `{PType B} : Proper (leq ==> leq) (@tlabel A B _ _).
Proof.
  intro a; induction a; intros c Hc; simpl.
  - apply bot_le.
  - inv Hc; auto.
    inv H1; rewrite H4; apply bot_le.
Qed.

#[global]
  Instance monotone_tdelta {A B} `{PType B} (a : A)
  : Proper (leq ==> leq) (fun t => tdelta t a).
Proof.
  intro t; revert a; induction t; intros a t' Ht'; simpl.
  { constructor; constructor. }
  inv Ht'.
  { inv H1; constructor; auto. }
  simpl; auto.
Qed.

Lemma trie_bot_bot {A B} `{PType B} :
  @trie_bot A B === ⊥.
Proof. reflexivity. Qed.

Lemma equ_trie_node {A B} `{PType B} (b b' : B) (k k' : A -> trie A B) :
  b === b' ->
  k === k' ->
  trie_node b k === trie_node b' k'.
Proof. intros Hb Hk'; rewrite Hb, Hk'; reflexivity. Qed.

(** Interesting type because:

    1) All elements are infinite.

    2) Bottom and top elements exist without need for special
    constructors.

    3) Compact basis is made up of elements that are technically not
    finite but are finitely approximable (tries that are only
    interesting up to a finite depth and then are infinitely empty).
    We can still represent the basis elements with an inductive type
    by letting bot stand for empty but have to be careful with the
    order relation so that all basis elements that approximate the
    empty cotrie are collapsed into a single equivalence class.

    4) Structural order relation coincides perfectly with semantic
    equivalence of languages (see 'in_lang_cotrie_le' lemma). This
    makes some proofs, e.g., that of continuity, extremely easy
    (rearranging quantifiers).

    Union, intersection, and complement are implemented as primitive
    CoFixpoints. Concatenation is a cofold over cotries, and Kleene
    star is repeated concatenation with infinite fuel (coiter
    construction applied to omega).

*)

CoInductive cotrie (A B : Type) : Type :=
| cotrie_node : B -> (A -> cotrie A B) -> cotrie A B.

Definition label {A B} (t : cotrie A B) : B :=
  match t with
  | cotrie_node b _ => b
  end.

Definition accepts {A} (t : cotrie A bool) : bool := label t.

Definition delta {A B} (t : cotrie A B) (a : A) : cotrie A B :=
  match t with
  | cotrie_node _ k => k a
  end.

Definition unf {A B} (t : cotrie A B) :=
  match t with
  | cotrie_node b k => cotrie_node b k
  end.

Lemma unf_eq {A B} (t : cotrie A B) : t = unf t.
Proof. destruct t; auto. Qed.

CoInductive cotrie_le {A B : Type} `{OType B} : cotrie A B -> cotrie A B -> Prop :=
| cotrie_le_node : forall b b' k k',
    b ⊑ b' ->
    (forall a, cotrie_le (k a) (k' a)) ->
    cotrie_le (cotrie_node b k) (cotrie_node b' k').

#[global]
  Instance Reflexive_cotrie_le {A B} `{OType B} : Reflexive (@cotrie_le A B _).
Proof. cofix CH; intros []; constructor; auto; reflexivity. Qed.

#[global]
  Instance Transitive_cotrie_le {A B} `{OType B} : Transitive (@cotrie_le A B _).
Proof.
  cofix CH; intros x y z Hxy Hyz.
  inv Hxy; inv Hyz; constructor; eauto; etransitivity; eauto.
Qed.

#[global]
  Instance PreOrder_cotree_le {A B} `{OType B} : PreOrder (@cotrie_le A B _).
Proof. constructor; typeclasses eauto. Qed.

#[global]
  Instance OType_cotrie {A B} `{OType B} : OType (cotrie A B) :=
  {| leq := cotrie_le |}.

CoFixpoint cotrie_bot {A B} `{PType B} : cotrie A B :=
  cotrie_node ⊥ (const cotrie_bot).

Lemma cotrie_bot_le {A B} `{PType B} (t : cotrie A B) :
  cotrie_bot ⊑ t.
Proof.
  revert t; cofix CH; intro t.
  rewrite unf_eq; destruct t; constructor.
  - apply bot_le.
  - intro a; apply CH.
Qed.

#[global]
  Instance PType_cotrie {A B} `{PType B} : PType (cotrie A B) :=
  {| bot := cotrie_bot
   ; bot_le := @cotrie_bot_le _ _ _ _ |}.

CoFixpoint cotrie_top {A B} `{TType B} : cotrie A B :=
  cotrie_node ⊤ (const cotrie_top).

Lemma cotrie_le_top {A B} `{TType B} (t : cotrie A B) :
  t ⊑ cotrie_top.
Proof.
  revert t; cofix CH; intro t.
  rewrite (@unf_eq _ _ cotrie_top); destruct t; constructor.
  - apply le_top.
  - intro a; apply CH.
Qed.

#[global]
  Instance TType_cotrie {A B} `{TType B} : TType (cotrie A B) :=
  {| top := cotrie_top
   ; le_top := @cotrie_le_top _ _ _ _ |}.

(** Only used when B is an ExtType so no need to complicate the
    definition with equivalence on B (just use equality instead). *)
CoInductive cotrie_eq {A B : Type} : cotrie A B -> cotrie A B -> Prop :=
| cotrie_eq_node : forall b k k',
    (forall a, cotrie_eq (k a) (k' a)) ->
    cotrie_eq (cotrie_node b k) (cotrie_node b k').

(** Extensionality axiom for cotries. *)
Axiom cotrie_ext : forall {A B} (a b : cotrie A B), cotrie_eq a b -> a = b.

Lemma equ_cotrie_eq {A B} `{ExtType B} (a b : cotrie A B) :
  a === b -> cotrie_eq a b.
Proof.
  revert a b; cofix CH; intros a b [Hab Hba].
  inv Hab; inv Hba; try constructor.
  assert (Heq: b0 = b').
  { apply ext; split; auto. }
  subst; constructor; intro x; apply CH; split; try apply H2; apply H8.
Qed.

Lemma cotrie_eq_equ {A B} `{OType B} (a b : cotrie A B) :
  cotrie_eq a b -> a === b.
Proof.
  split; revert H0; revert a b; cofix CH; intros a b Hab; inv Hab;
    constructor; try reflexivity; intro a; apply CH; auto.
Qed.

#[global]
  Instance Reflexive_cotrie_eq {A B} `{ExtType B} : Reflexive (@cotrie_eq A B).
Proof. cofix CH; intros []; constructor; auto. Qed.

#[global]
  Instance Transitive_cotrie_eq {A B} `{ExtType B} : Transitive (@cotrie_eq A B).
Proof.
  cofix CH; intros x y z Hxy Hyz.
  inv Hxy; auto.
  - inv Hyz; constructor; eauto.
Qed.

#[global]
  Instance Symmetric_cotrie_eq {A B} `{ExtType B} : Symmetric (@cotrie_eq A B).
Proof.
  cofix CH; intros x y Hxy.
  inv Hxy; auto; constructor; intro a; apply CH; auto.
Qed.

#[global]
  Instance ExtType_cotrie {A B} `{ExtType B} : ExtType (cotrie A B).
Proof.
  constructor; intros a b Hab; apply cotrie_ext, equ_cotrie_eq; auto.
Qed.

CoFixpoint cotrie_sup {A B} `{CPO B} (f : nat -> cotrie A B) : cotrie A B :=
  cotrie_node (sup (label ∘ f)) (fun x => cotrie_sup (fun i => delta (f i) x)).

Lemma supremum_cotrie_sup {A B} `{CPO B} (f : nat -> cotrie A B) :
  supremum (cotrie_sup f) f.
Proof.
  split.
  - revert f; cofix CH; intros f i.
    rewrite (@unf_eq _ _ (cotrie_sup _)); simpl.
    destruct (f i) eqn:Hfi.
    constructor.
    + apply le_sup with i.
      unfold compose; rewrite Hfi; reflexivity.
    + intro a.
      set (g := fun i => delta (f i) a).
      replace (c a) with (g i).
      2: { unfold g; rewrite Hfi; reflexivity. }
      apply CH.
  - revert f; cofix CH; intros f x Hx.
    destruct x.
    rewrite unf_eq; simpl.
    constructor.
    + apply ge_sup.
      intro i; unfold compose.
      specialize (Hx i).
      destruct (f i); inv Hx; auto.
    + intro a; apply CH; intro i.
      specialize (Hx i).
      destruct (f i); inv Hx; simpl; auto.
Qed.

CoFixpoint cotrie_inf {A B} `{lCPO B} (f : nat -> cotrie A B) : cotrie A B :=
  cotrie_node (inf (label ∘ f)) (fun x => cotrie_inf (fun i => delta (f i) x)).

Lemma infimum_cotrie_inf {A B} `{lCPO B} (f : nat -> cotrie A B) :
  infimum (cotrie_inf f) f.
Proof.
  split.
  - revert f; cofix CH; intros f i.
    rewrite unf_eq; simpl.
    destruct (f i) eqn:Hfi.
    constructor.
    + apply ge_inf with i.
      unfold compose; rewrite Hfi; reflexivity.
    + intro a.
      set (g := fun i => delta (f i) a).
      replace (c a) with (g i).
      2: { unfold g; rewrite Hfi; reflexivity. }
      apply CH.
  - revert f; cofix CH; intros f x Hx.
    destruct x.
    rewrite (@unf_eq _ _ (cotrie_inf _)); simpl.
    constructor.
    + apply le_inf.
      intro i; unfold compose.
      specialize (Hx i).
      destruct (f i); inv Hx; auto.
    + intro a; apply CH; intro i.
      specialize (Hx i).
      destruct (f i); inv Hx; simpl; auto.
Qed.

#[global]
  Instance CPO_cotrie {A B} `{CPO B} : CPO (@cotrie A B).
Proof.
  constructor; intro f; exists (cotrie_sup f).
  apply supremum_cotrie_sup.
Qed.
#[global] Hint Resolve CPO_cotrie : cotrie.

#[global]
  Instance lCPO_cotrie {A B} `{lCPO B} : lCPO (@cotrie A B).
Proof.
  constructor; intro f; exists (cotrie_inf f).
  apply infimum_cotrie_inf.
Qed.
#[global] Hint Resolve lCPO_cotrie : cotrie.

Fixpoint fin_inj (n : nat) (x : Fin.t n) : Fin.t (S n) :=
  match x with
  | F1 => F1
  | FS x' => FS (fin_inj x')
  end.

Fixpoint fin_of_nat (n : nat) : Fin.t (S n) :=
  match n with
  | O => F1
  | S n' => FS fin_of_nat
  end.

Lemma fin_S_n_cases (n : nat) (x : Fin.t (S n)) :
  (exists m, x = fin_inj m) \/ x = fin_of_nat.
Proof.
  dependent induction x.
  - destruct n.
    + right; auto.
    + left; exists F1; auto.
  - destruct n.
    { inv x. }
    specialize (IHx n x (eq_refl _) JMeq_refl).
    destruct IHx as [[m H]|H]; subst.
    + left; exists (FS m); reflexivity.
    + right; reflexivity.
Qed.

Lemma compact_finfun {A} `{OType A} (n : nat) (f : Fin.t n -> A) :
  (forall a, compact (f a)) ->
  compact f.
Proof.
  intros Hf ch Hch Hsup.
  unfold compact in Hf.
  assert (forall a, exists i, ch i a === f a).
  { intro a; apply Hf.
    - intros i j.
      destruct (Hch i j) as [k [Hik Hjk]].
      exists k; auto.
    - apply apply_supremum; auto. }
  clear Hf.
  revert H0 Hch Hsup.
  revert f ch.
  induction n; intros f ch Ha Hch Hsup.
  { exists O; apply equ_arrow; intro a; inv a. }
  assert (Hlt: n < S n) by lia.
  set (m := @fin_of_nat n).
  pose proof (Ha m) as Hm.
  destruct Hm as [i Hi].
  set (f' := f ∘ @fin_inj n).
  set (ch' := fun i x => ch i (fin_inj x)).
  assert (Hf':  forall a : t n, exists i, ch' i a === f' a).
  { intro a.
    specialize (Ha (fin_inj a)).
    destruct Ha as [j Hj].
    exists j; apply Hj. }
  apply IHn in Hf'.
  2: { intros j k.
       destruct (Hch j k) as [k' [Hjk' Hkk']].
       exists k'; firstorder. }
  2: { unfold f', ch'.
       unfold compose.
       apply supremum_apply.
       intro x; apply apply_supremum; auto. }
  destruct Hf' as [j Hj].
  destruct (Hch i j) as [k [Hik Hjk]].
  exists k.
  apply equ_arrow; intro x.
  unfold ch', f' in Hj.
  destruct (@fin_S_n_cases _ x).
  - destruct H0 as [y ?]; subst.
    simpl in *.
    apply equ_arrow with (x:=y) in Hj.
    unfold compose in Hj.
    rewrite <- Hj.
    split; auto.
    rewrite Hj.
    apply Hsup.
  - subst.
    unfold m in *.
    rewrite <- Hi.
    split; auto.
    rewrite Hi.
    apply Hsup.
Qed.

Lemma directed_tlabel {A B} `{PType B} (f : nat -> trie A B) :
  directed f ->
  directed (tlabel ∘ f).
Proof.
  intro Hf.
  apply monotone_directed; auto.
  apply monotone_tlabel.
Qed.

Lemma directed_tdelta {A B} `{PType B} (f : nat -> trie A B) :
  directed f ->
  directed (tdelta ∘ f).
Proof.
  intros Hf.
  apply monotone_directed; auto.
  intros i j Hij a; apply monotone_tdelta; auto.
Qed.

Lemma is_bot_tlabel {A B} `{PType B} (t : trie A B) :
  is_bot t ->
  tlabel t === ⊥.
Proof. intro Ht; inv Ht; auto; reflexivity. Qed.

Lemma supremum_tlabel {A B} `{PType B} (f : nat -> trie A B) (b : B) (t : A -> trie A B) :
  supremum (trie_node b t) f ->
  supremum b (tlabel ∘ f).
Proof.
  intros [Hub Hlub].
  split.
  - intro i; unfold compose.
    specialize (Hub i).
    inv Hub; simpl; auto.
    apply is_bot_tlabel in H0.
    rewrite H0; apply bot_le.
  - intros x Hx.
    assert (Hb: upper_bound (trie_node x t) f).
    { intro i; specialize (Hx i); specialize (Hub i).
      unfold compose in Hx.
      destruct (f i) eqn:Hfi.
      - constructor; constructor.
      - inv Hub.
        + inv H0; constructor; constructor; auto.
        + apply trie_le_node; auto. }
    apply Hlub in Hb; inv Hb; auto.
    inv H0; rewrite H3; apply bot_le.
Qed.

Lemma is_bot_tdelta {A B} `{PType B} (t : trie A B) :
  is_bot t ->
  tdelta t === ⊥.
Proof.
  intro Ht; split.
  - inv Ht; intro a.
    + constructor; constructor.
    + apply trie_le_bot; auto.
  - apply bot_le.
Qed.

Lemma supremum_tdelta {A B} `{PType B} (f : nat -> trie A B) (b : B) (t : A -> trie A B) :
  supremum (trie_node b t) f ->
  supremum t (tdelta ∘ f).
Proof.
  intros [Hub Hlub].
  split.
  - intro i; unfold compose.
    specialize (Hub i).
    inv Hub.
    + apply is_bot_tdelta in H0; rewrite H0; apply bot_le.
    + intro a; simpl; auto.
  - intros x Hx.
    assert (Hb: upper_bound (trie_node b x) f).
    { intro i; specialize (Hx i); specialize (Hub i).
      unfold compose in Hx.
      destruct (f i) eqn:Hfi.
      - constructor; constructor.
      - inv Hub.
        + apply trie_le_bot; auto.
        + apply trie_le_node; auto. }
    apply Hlub in Hb; inv Hb; auto.
    inv H0; intro a; apply trie_le_bot; auto.
Qed.

Lemma is_bot_cases {A B} `{PType B} (f : nat -> trie A B) :
  (forall i, is_bot (f i)) \/ (exists i, ~ is_bot (f i)).
Proof.
  destruct (classic (exists i, ~ is_bot (f i))).
  - right; auto.
  - left. intro i.
    eapply not_ex_not_all in H0; eauto.
Qed.

Lemma supremum_trie_node_exists {A B} `{PType B} (f : nat -> trie A B) b k :
  ~ is_bot (trie_node b k) ->
  supremum (trie_node b k) f ->
  exists i b' k', f i = trie_node b' k' /\ b' ⊑ b /\ k' ⊑ k.
Proof.
  intros Hnb [Hub Hlub].
  destruct (is_bot_cases f) as [Hf|Hf].
  - assert (H0: upper_bound trie_bot f).
    { intro i; specialize (Hf i); inv Hf.
      - reflexivity.
      - constructor; constructor; auto. }
    apply Hlub in H0; inv H0; congruence.
  - destruct Hf as [n Hn]; specialize (Hub n).
    destruct (f n) eqn:Hfn.
    + exfalso; apply Hn; constructor.
    + inv Hub.
      * congruence.
      * exists n, b0, t; repeat split; auto.
Qed.

#[global]
  Instance monotone_is_bot {A B} `{PType B} : Proper (equ ==> flip leq) (@is_bot A B _ _).
Proof.
  intro x. induction x; intros y Hxy Hy; constructor.
  - inv Hxy.
    inv Hy.
    + inv H1; inv H3; auto.
    + inv H1.
      * inv H5; auto.
      * rewrite H3 in H8; apply le_bot in H8; auto.
  - intro a.
    destruct Hxy.
    inv H1.
    + inv H3; auto.
    + eapply is_bot_le.
      2: { auto. }
      inv Hy; auto.
Qed.

#[global]
  Instance Compact_trie {n B} `{oB : OType B} `{@PType _ oB} `{@Compact _ oB}
  : Compact (trie (Fin.t n) B).
Proof.
  constructor.
  intro x.
  induction x.
  - intros ch Hch [Hub Hlub].
    exists O; specialize (Hub O); split.
    + apply Hub.
    + constructor; constructor.
  - intros ch Hch Hsup.

    destruct (classic (is_bot (trie_node b t))).
    { exists O; split.
      - apply Hsup.
      - apply trie_le_bot; auto. }
    
    (* 1 *)
    pose proof Hsup as Hsup'.
    apply supremum_trie_node_exists in Hsup'; auto.
    destruct Hsup' as [i [b' [t' [Hi [Hb' Ht']]]]].
    
    (* 2 *)
    destruct H0.
    specialize (compact_spec b).
    unfold compact in compact_spec.
    assert (Hd: directed (tlabel ∘ ch)).
    { apply directed_tlabel; auto. }
    assert (Hs: supremum b (tlabel ∘ ch)).
    { eapply supremum_tlabel; eauto. }
    pose proof Hs as Hs'.
    apply compact_spec in Hs'; auto.
    destruct Hs' as [j Hj].
    clear Hd compact_spec.

    (* 3 *)
    assert (Hd': directed (tdelta ∘ ch)).
    { apply directed_tdelta; auto. }
    assert (Hs': supremum t (tdelta ∘ ch)).
    { eapply supremum_tdelta; eauto. }
    assert (Ht: compact t).
    { apply compact_finfun; auto. }
    specialize (Ht _ Hd' Hs').
    destruct Ht as [k Hk].
    unfold compose in *.
    destruct (Hch i j) as [m [Him Hjm]].
    destruct (Hch m k) as [p [Hmp Hkp]].
    exists p.
    split.
    { apply Hsup. }
    destruct (classic (is_bot (ch j))).
    { assert (Hb: b === ⊥).
      { destruct (ch j) eqn:Hchj.
        - simpl in Hj; rewrite Hj; reflexivity.
        - simpl in Hj.
          rewrite <- Hj.
          inv H0; auto. }
      rewrite Hb.
      destruct (classic (is_bot (ch k))).
      { constructor.
        constructor; try reflexivity.
        intro a.
        destruct (ch k) eqn:Hchk.
        - assert (Hx: forall x, tdelta trie_bot x === t x).
          { apply equ_arrow; auto. }
          specialize (Hx a).
          rewrite <- Hx; constructor.
        - inv H3.
          assert (Hx: forall x, tdelta (trie_node b0 t0) x === t x).
          { apply equ_arrow; auto. }
          simpl in Hx.
          eapply is_bot_le.
          + apply H7.
          + apply Hx. }     
      destruct (ch k) eqn:Hchk.
      - exfalso; apply H3; constructor.
      - inv Hkp; try congruence.
        apply trie_le_node.
        + apply bot_le.
        + intro a.
          assert (Ht: t0 === t).
          { rewrite <- Hk; reflexivity. }
          etransitivity.
          * apply Ht.
          * auto. }
    destruct (classic (is_bot (ch k))).
    { assert (Ht: forall x, is_bot (t x)).
      { intro x.
        inv H3.
        - rewrite <- H5 in Hk.
          eapply is_bot_le.
          { constructor. }
          apply Hk.
        - eapply is_bot_le.
          + apply H6.
          + rewrite <- H4 in Hk.
            apply Hk. }
      destruct (ch p) eqn:Hchp.
      - rewrite trie_bot_bot in Hmp.
        apply le_bot in Hmp.
        rewrite Hmp in Hjm.
        apply le_bot in Hjm.
        exfalso; apply H0.
        rewrite Hjm; constructor.
      - apply trie_le_node.
        + (* b is label of ch j which is le label of ch m which is le b0 *)
          inv Hjm; try congruence.
          rewrite <- H4 in Hj.
          simpl in Hj.
          rewrite <- Hj.
          rewrite <- H5 in Hmp.
          inv Hmp.
          * inv H8.
            rewrite H11 in H6.
            apply le_bot in H6.
            rewrite H6; apply bot_le.
          * etransitivity; eauto.
        + intro a; apply trie_le_bot; auto. }
    destruct (ch p) eqn:Hchp.
    { rewrite trie_bot_bot in Hmp.
      apply le_bot in Hmp.
      rewrite Hmp in Hjm.
      apply le_bot in Hjm.
      exfalso; apply H0.
      rewrite Hjm; constructor. }
    apply trie_le_node.
    + inv Hjm; try congruence.
      rewrite <- H4 in Hj.
      simpl in Hj.
      rewrite <- Hj.
      rewrite <- H5 in Hmp.
      inv Hmp.
      * inv H8.
        rewrite H11 in H6; apply le_bot in H6.
        rewrite H6; apply bot_le.
      * etransitivity; eauto.
    + intro a.
      inv Hkp; try congruence.
      * rewrite <- H4 in Hk.
        etransitivity.
        { apply Hk. }
        auto.
Qed.


Fixpoint inj {A B} `{PType B} (t : trie A B) : cotrie A B :=
  match t with
  | trie_bot => ⊥
  | trie_node b k => cotrie_node b (inj ∘ k)
  end.

Lemma is_bot_inj {A B} `{PType B} (a : trie A B) (b : cotrie A B) :
  is_bot a ->
  inj a ⊑ b.
Proof.
  revert b; induction a; intros b' Ha; simpl.
  { apply cotrie_bot_le. }
  destruct b'.
  inv Ha.
  constructor.
  - rewrite H3; apply bot_le.
  - intro a; apply H0; auto.
Qed.

#[global]
  Instance monotone_inj {A B} `{PType B} : Proper (leq ==> leq) (@inj A B _ _).
Proof.
  intro x; induction x; intros y Hxy; inv Hxy; simpl.
  { apply cotrie_bot_le. }
  - eapply is_bot_inj in H1; eauto.
  - constructor; auto; intro a; apply H0; simpl; auto.
Qed.

Fixpoint prefix {A B} (n : nat) (t : cotrie A B) : trie A B :=
  match n with
  | O => trie_bot
  | S n' => match t with
           | cotrie_node b k => trie_node b (prefix n' ∘ k)
           end
  end.

Lemma monotone_prefix {A B} `{PType B} (x y : cotrie A B) (i : nat) :
  x ⊑ y ->
  prefix i x ⊑ prefix i y.
Proof.
  revert x y; induction i; intros [] [] Hxy; simpl.
  { constructor; constructor. }
  inv Hxy.
  apply trie_le_node; auto.
  intro a; apply IHi; simpl; auto.
Qed.

Lemma monotone_prefix' {A B} `{PType B} (t : cotrie A B) (i j : nat) :
  i ⊑ j ->
  prefix i t ⊑ prefix j t.
Proof.
  revert t j; induction i; intros t j Hij; simpl.
  { constructor; constructor. }
  destruct t.
  destruct j.
  { inv Hij. }
  apply trie_le_node.
  - reflexivity.
  - intro a; apply IHi; simpl in *; lia.
Qed.

Lemma inj_prefix_le {A B} `{PType B} (t : cotrie A B) (i : nat) :
  inj (prefix i t) ⊑ t.
Proof.
  revert t; induction i; intro t; simpl.
  { apply cotrie_bot_le. }
  destruct t.
  constructor.
  - reflexivity.
  - intro a; apply IHi.
Qed.

Lemma supremum_inj_prefix {A B} `{PType B} (t : cotrie A B) :
  supremum t (fun i => inj (prefix i t)).
Proof.
  split.
  - intro i; apply inj_prefix_le.
  - revert t; cofix CH; intros t ub Hub.
    destruct ub.
    destruct t.
    pose proof Hub as Hub'.
    specialize (Hub' (S O)).
    inv Hub'.
    constructor; auto; intro a; apply CH.
    intro i.
    specialize (Hub (S i)); simpl in Hub.
    inv Hub; apply H7.
Qed.

Lemma trie_le_cotrie_le {A B} `{PType B} (a b : trie A B) :
  a ⊑ b -> inj a ⊑ inj b.
Proof.
  revert b; induction a; intros y Hy; simpl.
  - apply cotrie_bot_le.
  - inv Hy.
    + eapply is_bot_inj in H1; eauto.
    + constructor; auto; intro a; apply H0; simpl; auto.
Qed.

Lemma inj_is_bot {A B} `{PType B} (a : trie A B) :
  inj a ⊑ cotrie_bot ->
  is_bot a.
Proof.
  induction a; intros Ha.
  { constructor. }
  rewrite (@unf_eq _ _ cotrie_bot) in Ha.
  inv Ha; constructor.
  - apply le_bot in H4; auto.
  - intro a; apply H0; unfold compose, const in *; simpl; auto.
Qed.

Lemma cotrie_le_trie_le {A B} `{PType B} (a b : trie A B) :
  inj a ⊑ inj b -> a ⊑ b.
Proof.
  revert b; induction a; intros y Hy.
  { constructor; constructor. }
  - destruct y.
    + simpl in *.
      rewrite (@unf_eq _ _ cotrie_bot) in Hy.
      inv Hy.
      constructor; constructor.
      * apply le_bot in H4; auto.
      * intro a; apply inj_is_bot; unfold compose, const in *; simpl; auto.
    + inv Hy.
      apply trie_le_node; auto; intro a; apply H0; simpl; eauto.
Qed.

Lemma chain_prefix {A B} `{PType B} (t : cotrie A B) :
  chain (fun n : nat => prefix n t).
Proof.
  apply monotone_chain.
  - intros i j Hij; apply monotone_prefix'; auto.
  - intro i; simpl; lia.
Qed.

Lemma supremum_label {A B} `{OType B}
  (b : B) (k : A -> cotrie A B) (ch : nat -> cotrie A B) :
  supremum (cotrie_node b k) ch ->
  supremum b (label ∘ ch).
Proof.
  unfold flip, compose.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i).
    inv Hub; simpl; auto.
  - intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (Hb: upper_bound (cotrie_node y k) ch).
    { intro i; specialize (Hub i).
      specialize (Hy i).
      destruct (ch i); simpl in *.
      inv Hub.
      constructor; auto. }
    apply Hlub in Hb.
    inv Hb; auto.
Qed.

Lemma supremum_delta {A B} `{OType B}
  (b : B) (k : A -> cotrie A B) (ch : nat -> cotrie A B) (x : A) :
  supremum (cotrie_node b k) ch ->
  supremum (k x) (flip delta x ∘ ch).
Proof.
  unfold flip, compose.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i).
    inv Hub; simpl; auto.
  - intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (Hu: upper_bound (cotrie_node b (fun z => if classicT (z = x) then y else k z)) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub; auto.
      - intro a.
        destruct_classic; subst; auto.
        simpl in Hy.
        specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub; auto. }
    apply Hlub in Hu; inv Hu.
    specialize (H5 x).
    destruct_classic; auto; congruence.
Qed.

Lemma cotrie_bot_is_bot_prefix {A B} `{PType B} (t : cotrie A B) (i : nat) :
  t === cotrie_bot ->
  is_bot (prefix i t).
Proof.
  revert t; induction i; intros t Ht; simpl.
  - constructor.
  - destruct t.
    destruct Ht as [H0 H1].
    rewrite (@unf_eq _ _ cotrie_bot) in H0.
    inv H0.
    constructor.
    + split; auto; apply bot_le.
    + intro a; unfold compose.
      apply IHi.
      split; simpl; eauto.
      apply cotrie_bot_le.
Qed.

Lemma trie_le_trie_bot_cotrie_bot {A B} `{PType B} (t : cotrie A B) :
  (forall i, trie_le (prefix i t) trie_bot) ->
  t === cotrie_bot.
Proof.
  intro Hle.
  split.
  2: { apply cotrie_bot_le. }
  revert Hle; revert t.
  cofix CH; intros [] Ht.
  rewrite (@unf_eq _ _ cotrie_bot); constructor.
  - specialize (Ht (S O)).
    simpl in Ht.
    inv Ht; inv H0.
    rewrite H3; reflexivity.
  - intro a.
    apply CH.
    intro i.
    specialize (Ht (S i)).
    simpl in Ht.
    inv Ht.
    constructor.
    inv H0; eauto.
Qed.

Lemma upper_bound_trie_bot_is_bot {A B} `{PType B} (f : nat -> trie A B) (i : nat) :
  upper_bound trie_bot f ->
  is_bot (f i).
Proof.
  intro Hub.
  specialize (Hub i).
  eapply is_bot_le; eauto; constructor.
Qed.

Lemma supremum_is_bot_prefix {A B} `{PType B}
  (t : cotrie A B) (ch : nat -> cotrie A B) (n : nat) :
  supremum t ch ->
  (forall i, is_bot (prefix n (ch i))) ->
  is_bot (prefix n t).
Proof.
  revert t ch; induction n; intros t ch Ht Hub; simpl.
  { constructor. }
  destruct t.
  constructor.
  { apply supremum_label in Ht.
    split.
    2: { apply bot_le. }
    apply Ht.
    intro i.
    unfold compose.
    specialize (Hub i).
    simpl in Hub.
    destruct (ch i); simpl in *.
    inv Hub.
    rewrite H2; reflexivity. }
  intro a; eapply IHn.
  - eapply supremum_delta; eauto.
  - intro i; unfold flip, compose.
    specialize (Hub i).
    simpl in Hub.
    destruct (ch i).
    simpl.
    inv Hub.
    apply H3.
Qed.

Lemma supremum_ub_prefix_le_trie_bot {A B} `{PType B}
  (t : cotrie A B) (ch : nat -> cotrie A B) (n : nat) :
  supremum t ch ->
  upper_bound trie_bot (prefix n ∘ ch) ->
  prefix n t ⊑ trie_bot.
Proof.
  intros Ht Hub.
  constructor.
  eapply supremum_is_bot_prefix; eauto.
  intro i.
  specialize (Hub i).
  simpl in Hub.
  unfold compose in Hub.
  eapply is_bot_le; eauto.
  constructor.
Qed.

Lemma prefix_continuous {A B} `{PType B} (n : nat) :
  continuous (@prefix A B n).
Proof.
  induction n; intros ch Hch a Hsup; unfold compose; simpl.
  { apply supremum_const. }
  destruct a.
  assert (Hc: forall x, supremum (c x) (flip delta x ∘ ch)).
  { intro i; eapply supremum_delta; eauto. }
  split.
  - intro i; destruct (ch i) eqn:Hchi; simpl.
    apply trie_le_node.
    + destruct Hsup as [Hub _].
      specialize (Hub i); rewrite Hchi in Hub.
      inv Hub; auto.
    + intro x.
      replace ((prefix n ∘ c0) x) with ((prefix n ∘ (flip delta x ∘ ch)) i).
      2: { unfold compose; rewrite Hchi; reflexivity. }
      specialize (Hc x).
      apply IHn; auto.
      apply monotone_directed; auto.
      intros [] [] Hzw; inv Hzw; unfold flip; simpl; auto.
  - intros x Hx; destruct x.
    + assert (Hx': upper_bound trie_bot (prefix (S n) ∘ ch)).
      { apply Hx. }
      clear Hx.
      replace (trie_node b (prefix n ∘ c)) with (prefix (S n) (cotrie_node b c)) by reflexivity.
      eapply supremum_ub_prefix_le_trie_bot; eauto.
    + apply trie_le_node.
      { apply supremum_label in Hsup.
        assert (Hb: upper_bound b0 (label ∘ ch)).
        { intro i.
          specialize (Hx i).
          simpl in Hx.
          unfold compose.
          destruct (ch i); simpl.
          inv Hx; auto.
          inv H0; rewrite H3; apply bot_le. }
        apply Hsup in Hb; auto. }
      intro a.
      eapply IHn.
      2: { eauto. }
      { apply monotone_directed; auto.
        intros [] [] Hxy; inv Hxy; unfold flip; simpl; auto. }
      intro i; unfold compose.
      specialize (Hx i); simpl in Hx.
      destruct (ch i) eqn:Hchi.
      unfold flip; simpl.
      inv Hx; eauto.
      inv H0; constructor; eauto.
Qed.      

#[global]
  Instance Dense_cotrie {A B} `{PType B} : Dense (cotrie A B) (trie A B) :=
  { incl := inj
  ; ideal := flip prefix }.

#[global]
  Instance aCPO_cotrie {n B} `{oB: OType B} `{@PType B oB}
  `{@Compact _ oB} `{@CPO B oB}
  : aCPO (cotrie (Fin.t n) B) (trie (Fin.t n) B).
Proof.
  constructor.
  - intros a b; split.
    + apply trie_le_cotrie_le.
    + apply cotrie_le_trie_le.
  - apply chain_prefix.
  - intros a b Hab i; apply monotone_prefix; auto.
  - intro; apply prefix_continuous.
  - intro a; simpl; unfold compose, flip.
    apply supremum_inj_prefix.
Qed.

(** Regular language with alphabet A. *)
Definition tlang (n : nat) : Type := trie (Fin.t n) bool.
Definition lang (n : nat) : Type := cotrie (Fin.t n) bool.

Fixpoint fold {A B C} (z : C) (f : B -> (A -> C) -> C) (t : trie A B) : C :=
  match t with
  | trie_bot => z
  | trie_node b k => f b (fold z f ∘ k)
  end.

#[global]
  Instance monotone_fold {A B C} `{PType B} `{OType C}
  (z : C) (f : B -> (A -> C) -> C)
  {Hz : forall x, z ⊑ fold z f x}
  {Hf : Proper (leq ==> leq ==> leq) f}
  {Hf': forall b t y, is_bot (trie_node b t) -> f b (fold z f ∘ t) ⊑ fold z f y}
  : Proper (leq ==> leq) (fold z f).
Proof.
  intro x; induction x; intros y Hxy; simpl; auto.
  inv Hxy; simpl; auto.
  apply Hf; auto.
  intro a; apply H1, H6.
Qed.
#[global] Hint Resolve monotone_fold : cotrie.

#[global]
  Instance antimonotone_fold {A B C} `{PType B} `{OType C}
  (z : C) (f : B -> (A -> C) -> C)
  {Hz : forall x, fold z f x ⊑ z}
  {Hf : Proper (flip leq ==> leq ==> leq) f}
  {Hf': forall b t y, is_bot (trie_node b t) -> fold z f y ⊑ f b (fold z f ∘ t)}
  : Proper (leq ==> flip leq) (fold z f).
Proof.
  intro x; induction x; intros y Hxy; simpl; unfold flip; auto.
  inv Hxy; simpl; auto.
  apply Hf; auto.
  unfold flip in H1.
  intro a; apply H1, H6.
Qed.
#[global] Hint Resolve antimonotone_fold : cotrie.

Lemma co_fold_node {n B C} `{oB: OType B} `{@PType B oB}
  `{@CPO _ oB} `{@Compact _ oB} `{dCPO C}
  (z : C) (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (leq ==> leq ==> leq) f ->
  (forall b, wcontinuous (f b)) ->
  (forall b, z ⊑ fold z f b) ->
  z ⊑ f b (fun _ : Fin.t n => z) ->
  (forall b t y, is_bot (trie_node b t) -> f b (fold z f ∘ t) ⊑ fold z f y) ->
  co (fold z f) (cotrie_node b k) === f b (co (fold z f) ∘ k).
Proof.
  intros Hprop Hf Hz Hzf Hf'.
  apply supremum_sup.
  apply shift_supremum'' with
    (f := fun i => f b (fun x => fold z f (ideal (k x) i))); auto.
  { apply Hf.
    { apply monotone_chain; auto with cotrie order.
      intros i j Hij a.
      apply monotone_fold; auto.
      apply chain_leq; auto; apply chain_ideal. }
    { apply supremum_apply; intro x.
      apply dsup_spec.
      { apply monotone_directed; auto with cotrie order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma co_fold_node' {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@dCPO _ oC} `{@ExtType _ oC}
  (z : C) (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (leq ==> leq ==> leq) f ->
  (forall b, wcontinuous (f b)) ->
  (forall b, z ⊑ fold z f b) ->
  z ⊑ f b (fun _ : Fin.t n => z) ->
  (forall b t y, is_bot (trie_node b t) -> f b (fold z f ∘ t) ⊑ fold z f y) ->
  co (fold z f) (cotrie_node b k) = f b (co (fold z f) ∘ k).
Proof. intros Hprop Hf Hz Hzf Hf'; apply ext, co_fold_node; auto. Qed.

Definition cofold {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{PType C} (f : B -> (Fin.t n -> C) -> C)
  : cotrie (Fin.t n) B -> C :=
  co (fold ⊥ f).

Lemma cofold_node {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@PType _ oC} `{@dCPO _ oC}
  (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (leq ==> leq ==> leq) f ->
  (forall b, wcontinuous (f b)) ->
  (forall b t y, is_bot (trie_node b t) -> f b (fold ⊥ f ∘ t) ⊑ fold ⊥ f y) ->
  cofold f (cotrie_node b k) === f b (cofold f ∘ k).
Proof.
  intros Hprop Hf Hf'.
  apply co_fold_node; auto.
  - intro t; apply bot_le.
  - apply bot_le.
Qed.

Lemma cofold_node' {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@PType _ oC} `{@dCPO _ oC} `{@ExtType _ oC}
  (f : B -> (Fin.t  n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (leq ==> leq ==> leq) f ->
  (forall b, wcontinuous (f b)) ->
  (forall b t y, is_bot (trie_node b t) -> f b (fold ⊥ f ∘ t) ⊑ fold ⊥ f y) ->
  cofold f (cotrie_node b k) = f b (cofold f ∘ k).
Proof. intros Hprop Hf Hf'; apply ext, cofold_node; auto. Qed.

Extract Constant cofold => "
  \ n oB pB oC pC f t ->
    case t of
      Cotrie_Node b k -> f b (cofold n oB pB oC pC f Prelude.. k)
".

Definition coopfold {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{TType C} (f : B -> (Fin.t n -> C) -> C)
  : cotrie (Fin.t n) B -> C :=
  coop (fold ⊤ f).

Lemma coop_fold_node {n B C} `{oB: OType B} `{@PType B oB}
  `{@CPO _ oB} `{@Compact _ oB} `{ldCPO C}
  (z : C) (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (flip leq ==> leq ==> leq) f ->
  (forall b, dec_wcontinuous (f b)) ->
  (forall b, fold z f b ⊑ z) ->
  f b (fun _ : Fin.t n => z) ⊑ z ->
  (forall b t y, is_bot (trie_node b t) -> fold z f y ⊑ f b (fold z f ∘ t)) ->
  coop (fold z f) (cotrie_node b k) === f b (coop (fold z f) ∘ k).
Proof.
  intros Hprop Hf Hz Hzf Hf'.
  apply infimum_inf.
  apply shift_infimum'' with
    (f := fun i => f b (fun x => fold z f (ideal (k x) i))); auto.
  { apply Hf.
    { intros i x.
      apply antimonotone_fold; eauto.
      apply chain_leq; auto; apply chain_ideal. }
    { apply infimum_apply; intro x.
      apply dinf_spec.
      { apply antimonotone_downward_directed; auto with cotrie order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma coop_fold_node' {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@ldCPO _ oC} `{@ExtType _ oC}
  (z : C) (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (flip leq ==> leq ==> leq) f ->
  (forall b, dec_wcontinuous (f b)) ->
  (forall b, fold z f b ⊑ z) ->
  f b (fun _ : Fin.t n => z) ⊑ z ->
  (forall b t y, is_bot (trie_node b t) -> fold z f y ⊑ f b (fold z f ∘ t)) ->
  coop (fold z f) (cotrie_node b k) = f b (coop (fold z f) ∘ k).
Proof. intros Hprop Hf Hz Hzf Hf'; apply ext, coop_fold_node; auto. Qed.

Lemma coopfold_node {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@TType _ oC} `{@ldCPO _ oC}
  (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (flip leq ==> leq ==> leq) f ->
  (forall b, dec_wcontinuous (f b)) ->
  (forall b t y, is_bot (trie_node b t) -> fold ⊤ f y ⊑ f b (fold ⊤ f ∘ t)) ->
  coopfold f (cotrie_node b k) === f b (coopfold f ∘ k).
Proof.
  intros Hprop Hf Hf'.
  apply coop_fold_node; auto.
  - intro t; apply le_top.
  - apply le_top.
Qed.

Lemma coopfold_node' {n B C} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} `{oC : OType C} `{@TType _ oC} `{@ldCPO _ oC} `{@ExtType _ oC}
  (f : B -> (Fin.t n -> C) -> C) (b : B) (k : Fin.t n -> cotrie (Fin.t n) B) :
  Proper (flip leq ==> leq ==> leq) f ->
  (forall b, dec_wcontinuous (f b)) ->
  (forall b t y, is_bot (trie_node b t) -> fold ⊤ f y ⊑ f b (fold ⊤ f ∘ t)) ->
  coopfold f (cotrie_node b k) = f b (coopfold f ∘ k).
Proof. intros Hprop Hf Hf'; apply ext, coopfold_node; auto. Qed.

Extract Constant coopfold => "
  \ oB pB oC tC f t ->
    case t of
      Cotrie_Node b k -> f b (coopfold oB pB oC pC f Prelude.. k)
".

Inductive trie_cotrie_le {A B} `{PType B} : trie A B -> cotrie A B -> Prop :=
(* | trie_cotrie_le_bot : forall t, trie_cotrie_le trie_bot t *)
| trie_cotrie_le_bot : forall a b, is_bot a -> trie_cotrie_le a b
| trie_cotrie_le_node : forall b b' f g,
    b ⊑ b' ->
    (forall a, trie_cotrie_le (f a) (g a)) ->
    trie_cotrie_le (trie_node b f) (cotrie_node b' g).

#[global]
  Instance antimonotone_trie_cotrie_le {A B} `{PType B}
  : Proper (leq ==> flip leq) (@trie_cotrie_le A B _ _).
Proof.
  intro x; induction x; intros y Hxy z Hz.
  { constructor; constructor. }
  inv Hxy.
  { constructor; auto. }
  simpl in H0; unfold flip, impl in H0.
  inv Hz.
  { constructor.
    eapply is_bot_le; eauto.
    apply trie_le_node; auto. }
  apply trie_cotrie_le_node; eauto.
  etransitivity; eauto.
Qed.
#[global] Hint Resolve antimonotone_trie_cotrie_le : cotrie.

Definition cotrie_le' {n B} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} : cotrie (Fin.t n) B -> cotrie (Fin.t n) B -> Prop :=
  coop trie_cotrie_le.

Lemma trie_cotrie_le_trans {A B} `{PType B} (x y : trie A B) (z : cotrie A B) :
  x ⊑ y ->
  trie_cotrie_le y z ->
  trie_cotrie_le x z.
Proof.
  revert y z; induction x; intros y z Hxy Hyz.
  { constructor; constructor. }
  inv Hxy.
  { constructor; auto. }
  inv Hyz.
  { constructor; eapply is_bot_le; eauto.
    apply trie_le_node; auto. }
  apply trie_cotrie_le_node.
  - etransitivity; eauto.
  - intro a; eapply H0; simpl; auto.
Qed.

Lemma trie_cotrie_le_ideal {A B} `{PType B} (x y : cotrie A B) (i : nat) :
  cotrie_le x y ->
  trie_cotrie_le (ideal x i) y.
Proof.
  revert x y; induction i; intros x y Hxy; simpl; unfold flip; simpl.
  - constructor; constructor.
  - simpl in IHi; unfold flip in IHi.
    destruct x; inv Hxy; apply trie_cotrie_le_node; auto.
    intro a; apply IHi, H4.
Qed.
(* #[global] Hint Resolve trie_cotrie_le_ideal : cotrie. *)

Lemma cotrie_le'_inv_node {n B} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} (b : B) (f : Fin.t n -> cotrie (Fin.t n) B) (t : cotrie (Fin.t n) B) :
  cotrie_le' (cotrie_node b f) t ->
  exists b' g, t = cotrie_node b' g /\ b ⊑ b' /\ forall a, cotrie_le' (f a) (g a).
Proof.
  intro Hle.
  destruct t; try solve [apply coop_elim2 with (i := S O) in Hle;
                         eauto with cotrie order; inv Hle].
  exists b0, c; split; auto; split.
  - apply coop_elim2 with (i := S O) in Hle; eauto with cotrie order.
    inv Hle; auto.
    inv H2; rewrite H5; apply bot_le.
  - intro a; apply coop_intro2; eauto with cotrie order; intro i.
    apply coop_elim2 with (i := S i) in Hle; eauto with cotrie order.
    inv Hle; simpl; eauto.
    inv H2; constructor; eauto.
Qed.

Lemma cotrie_le_cotrie_le' {n B} `{oB: OType B} `{@PType B oB} `{@CPO _ oB}
  `{@Compact _ oB} (x y : cotrie (Fin.t n) B) :
  cotrie_le x y <-> cotrie_le' x y.
Proof.
  split; intro Hle.
  - apply coop_intro2.
    { apply antimonotone_trie_cotrie_le. }
    intro i; apply trie_cotrie_le_ideal; auto.
  - revert Hle; revert x y; cofix CH; intros x y Hle.
    destruct x.
    apply cotrie_le'_inv_node in Hle.
    destruct Hle as [b' [g [? [Hb Hle]]]]; subst.
    constructor; auto.
Qed.

(** Membership checking by induction on the string. *)
Inductive in_lang {n} : lang n -> list (Fin.t n) -> Prop :=
| in_lang_here : forall k,
    in_lang (cotrie_node true k) []
| in_lang_there : forall b k x xs,
    in_lang (k x) xs ->
    in_lang (cotrie_node b k) (x :: xs).

Fixpoint in_langb {n} (t : lang n) (l : list (Fin.t n)) : bool :=
  match t, l with
  | cotrie_node b _, [] => b
  | cotrie_node _ k, x :: xs => in_langb (k x) xs
  end.

(* Definition trie_set {A} (t : tlang A) : list A -> Prop := *)
(*   fold (const False) (fun b k l => match l with *)
(*                             | [] => b = true *)
(*                             | x :: xs => k x xs *)
(*                             end) t. *)

Definition in_langb_spec {n} (t : lang n) (l : list (Fin.t n))
  : Bool.reflect (in_lang t l) (in_langb t l).
Proof.
  revert t; induction l; intros []; simpl.
  - destruct b; constructor.
    + constructor.
    + intro HC; inv HC.
  - specialize (IHl (c a)).
    destruct IHl.
    + constructor; constructor; auto.
    + constructor; intro HC; inv HC; apply n0; auto.
Qed.

Lemma in_lang_cotrie_le {n} (a b : lang n) :
  (forall l, in_lang a l -> in_lang b l) <-> a ⊑ b.
Proof.
  split.
  - revert a b; cofix CH; intros [] [] Hab.
    constructor.
    + specialize (Hab []).
      destruct b.
      * assert (H: in_lang (cotrie_node true c) []).
        { constructor. }
        apply Hab in H; inv H; reflexivity.
      * destruct b0; simpl; auto.
    + intro a.
      apply CH.
      intros l Hl.
      specialize (Hab (a :: l)).
      assert (H: in_lang (cotrie_node b c) (a :: l)).
      { constructor; auto. }
      apply Hab in H; inv H; auto.
  - intros Hab l.
    revert Hab; revert a b.
    induction l; intros x y Hxy Hl.
    + inv Hl; inv Hxy.
      destruct b'; simpl in *; try contradiction; constructor.
    + inv Hl; inv Hxy.
      constructor; eapply IHl; eauto; apply H4.
Qed.

Lemma in_lang_eq {n} (a b : lang n) :
  (forall l, in_lang a l <-> in_lang b l) <-> a = b.
Proof.
  split.
  - intro H; apply ext; split; apply in_lang_cotrie_le; firstorder.
  - intros ->; firstorder.
Qed.

(** Empty language ∅. *)
Definition empty {n} : lang n := cotrie_bot.

Definition full {n} : lang n := cotrie_top.

(** Language containing empty string ϵ. *)
Definition epsilon {n} : lang n := cotrie_node true (const empty).

(** Language containing single character a. *)
Definition single {n} (a : Fin.t n) : lang n :=
  cotrie_node false (fun x => if eqb x a then epsilon else empty).

Lemma bool_le_orb_l (a b c : bool) :
  a ⊑ b ->
  a ⊑ orb b c.
Proof. destruct a, b, c; simpl; auto. Qed.

Lemma bool_le_orb_r (a b c : bool) :
  a ⊑ c ->
  a ⊑ orb b c.
Proof. destruct a, b, c; simpl; auto. Qed.

Lemma bool_le_orb (a b c d : bool) :
  a ⊑ c ->
  b ⊑ d ->
  orb a b ⊑ orb c d.
Proof. destruct a, b, c, d; auto. Qed.

Lemma bool_le_andb (a b c d : bool) :
  a ⊑ c ->
  b ⊑ d ->
  andb a b ⊑ andb c d.
Proof. destruct a, b, c, d; auto. Qed.

Lemma leq_cotrie_le {A B} `{OType B} (a b : cotrie A B) :
  a ⊑ b ->
  cotrie_le a b.
Proof. auto. Qed.

Fixpoint tunion {n} (x y : tlang n) : tlang n :=
  match x, y with
  | trie_bot, _ => y
  | _, trie_bot => x
  | trie_node b k, trie_node b' k' => trie_node (b || b') (fun a => tunion (k a) (k' a))
  end.

#[global]
 Instance monotone_orb : Proper (leq ==> leq) orb.
Proof. intros [] []; simpl; intuition; destruct x; auto. Qed.

CoFixpoint union {n} (a b : lang n) : lang n :=
  match a, b with
  | cotrie_node b k, cotrie_node b' k' => cotrie_node (b || b') (fun x => union (k x) (k' x))
  end.

Lemma union_node {n} (b : bool) (k : Fin.t n -> lang n) :
  union (cotrie_node b k) =
    fun l => match l with
          | cotrie_node b' k' => cotrie_node (b || b') (fun x => union (k x) (k' x))
          end.
Proof. ext y; destruct y; rewrite unf_eq; reflexivity. Qed.

CoFixpoint intersection {n} (a b : lang n) : lang n :=
  match a, b with
  | cotrie_node b k, cotrie_node b' k' => cotrie_node (b && b') (fun x => intersection (k x) (k' x))
  end.

Lemma intersection_node {n} (b : bool) (k : Fin.t n -> lang n) :
  intersection (cotrie_node b k) =
    fun l => match l with
          | cotrie_node b' k' => cotrie_node (b && b') (fun x => intersection (k x) (k' x))
          end.
Proof. ext y; destruct y; rewrite unf_eq; reflexivity. Qed.

Lemma full_top {n} :
  @full n === ⊤.
Proof. reflexivity. Qed.

CoFixpoint complement {n} (a : lang n) : lang n :=
  match a with
  | cotrie_node b k => cotrie_node (negb b) (complement ∘ k)
  end.

Lemma complement_node {n} (b : bool) (k : Fin.t n -> lang n) :
  complement (cotrie_node b k) = cotrie_node (negb b) (complement ∘ k).
Proof. rewrite unf_eq; reflexivity. Qed.

Definition tconcat {n} : tlang n -> lang n -> lang n :=
  fold (const empty)
    (fun b k l => cotrie_node (b && accepts l)
                 (fun x => union (k x l) (if b then delta l x else empty))).

Fixpoint tconcat' {n} (x : tlang n) (y : lang n) : lang n :=
  match x, y with
  | trie_bot, _ => empty
  | trie_node b1 k1, cotrie_node b2 k2 =>
      cotrie_node (b1 && b2)
        (fun a => union (tconcat' (k1 a) y) (if b1 then k2 a else empty))
  end.

Lemma tconcat_tconcat' {n} (x : tlang n) (y : lang n) :
  tconcat x y = tconcat' x y.
Proof.
  unfold tconcat; revert y; induction x; intro y; simpl.
  { destruct y; reflexivity. }
  destruct y; auto.
  f_equal.
  ext a; rewrite <- H; reflexivity.
Qed.

#[global]
 Instance monotone_union {n} : Proper (leq ==> leq ==> leq) (@union n).
Proof.
  cofix CH; intros [] [] Hxy [] [] Hzw; simpl.
  inv Hxy; inv Hzw.
  rewrite 2!union_node.
  constructor.
  - apply bool_le_orb; auto.
  - intro a; apply CH; simpl; auto.
Qed.

Lemma union_comm {n} (x y : lang n) :
  union x y = union y x.
Proof.
  apply cotrie_ext.
  revert x y; cofix CH; intros x y.
  destruct x, y.
  rewrite 2!union_node.
  rewrite Bool.orb_comm.
  constructor; intro a; apply CH.
Qed.

Lemma union_empty_l {n} (x : lang n) :
  union empty x = x.
Proof.
  apply cotrie_ext.
  revert x; cofix CH; intros [].
  rewrite union_comm.
  rewrite union_node; simpl.
  rewrite Bool.orb_false_r.
  constructor; intro a.
  unfold const.
  rewrite union_comm.
  apply CH.
Qed.

Lemma union_empty_r {n} (x : lang n) :
  union x empty = x.
Proof. rewrite union_comm; apply union_empty_l. Qed.

Lemma is_bot_tconcat {n} (a : tlang n) (b : lang n) :
  is_bot a -> 
  tconcat a b = empty.
Proof.
  unfold tconcat.
  revert b; induction a; intros b' Ha; simpl; auto.
  inv Ha.
  destruct b; simpl.
  { destruct H2; inv H0. }
  remember (cotrie_node false
    (fun x : Fin.t n =>
     union
       ((fold (const empty)
           (fun (b : bool) (k : Fin.t n -> cotrie (Fin.t n) bool -> lang n)
              (l : cotrie (Fin.t n) bool) =>
            cotrie_node (b && accepts l)
              (fun x0 : Fin.t n => union (k x0 l) (if b then delta l x0 else empty))) ∘ t) x b')
       empty)) as y.
  rewrite (@unf_eq _ _ empty); subst; simpl.
  f_equal.
  ext a.
  unfold compose.  
  rewrite H; auto.
  rewrite union_empty_l; reflexivity.
Qed.

#[global]
  Instance monotone_tconcat {n} : Proper (leq ==> leq) (@tconcat n).
Proof.
  intro x; induction x; intros y Hxy z; inv Hxy; simpl.
  { apply cotrie_bot_le. }
  { eapply is_bot_tconcat in H0.
    rewrite H0.
    apply cotrie_bot_le. }
  destruct z.
  constructor.
  - apply bool_le_andb; auto; reflexivity.
  - intro a.
    apply monotone_union.
    + apply H, H4.
    + destruct b, b'; simpl in H2; try contradiction; try apply cotrie_bot_le.
      reflexivity.
Qed.
#[global] Hint Resolve monotone_tconcat : cotrie.

#[global]
  Instance monotone_tconcat' {n} : Proper (leq ==> leq) (@tconcat' n).
Proof.
  intros x y Hxy z.
  rewrite <- 2!tconcat_tconcat'.
  apply monotone_tconcat; auto.
Qed.
#[global] Hint Resolve monotone_tconcat' : cotrie.

Definition coconcat {n} : lang n -> lang n -> lang n :=
  co tconcat.

Definition concat {n} : lang n -> lang n -> lang n :=
  cofold
    (fun b k l => cotrie_node (b && accepts l)
                 (fun x => union (k x l) (if b then delta l x else empty))).

Lemma concat_coconcat {n} (x y : lang n) :
  concat x y = coconcat x y.
Proof. reflexivity. Qed.

Definition coconcat' {n} : lang n -> lang n -> lang n :=
  co tconcat'.

Lemma coconcat_coconcat' {n} :
  @coconcat n = coconcat'.
Proof.
  ext x; ext y.
  apply ext.
  unfold coconcat, coconcat'.
  unfold co.
  unfold compose.
  rewrite 2!sup_apply.
  apply Proper_sup.
  { apply monotone_directed; eauto with cotrie order.
    intros i j Hij; apply monotone_tconcat.
    apply chain_leq; auto; apply chain_ideal. }
  { apply monotone_directed; eauto with cotrie order.
    intros i j Hij; apply monotone_tconcat'.
    apply chain_leq; auto; apply chain_ideal. }
  apply equ_arrow; intro i.
  apply eq_equ.
  apply tconcat_tconcat'.
Qed.

Fixpoint pow {n} (a : lang n) (k : nat) : lang n :=
  match k with
  | O => epsilon
  | S k' => concat (pow a k') a
  end.

Fixpoint pow' {n} (a : lang n) (k : nat) : lang n :=
  match k with
  | O => epsilon
  | S k' => concat a (pow' a k')
  end.

Fixpoint star_n {n} (a : lang n) (k : nat) : lang n :=
  match k with
  | O => empty
  | S k' => union (pow a k') (star_n a k')
  end.

Definition list_union {n} (z : lang n) (l : list (lang n)) : lang n :=
  colist.fold z union l.

Definition list_union' {n} (z : lang n) (l : list (lang n)) : lang n :=
  colist.foldl union z l.

Definition union_n {n} (z : lang n) (f : nat -> lang n) (k : nat) : lang n :=
  list_union z (seq_prefix f k).

Definition union_n' {n} (z : lang n) (f : nat -> lang n) (k : nat) : lang n :=
  list_union z (seq_prefix_aux f k).

Definition big_union {n} (f : nat -> lang n) : lang n :=
  sup (union_n empty f).

Definition big_union' {n} (f : nat -> lang n) : lang n :=
  sup (union_n' empty f).

#[global]
  Instance monotone_union_n {n} (f : nat -> lang n)
  : Proper (leq ==> leq) (union_n empty f).
Proof.
  intros i j Hij.
  eapply colist.monotone_fold.
  - intro l; apply cotrie_bot_le.
  - intro a; apply monotone_union; reflexivity.
  - apply chain_leq; auto.
    apply chain_seq_prefix.
Qed.
#[global] Hint Resolve monotone_union_n : cotrie.

#[global]
  Instance monotone_list_union {n} : Proper (leq ==> leq) (@list_union n empty).
Proof.
  eapply colist.monotone_fold; auto.
  - intro l; apply cotrie_bot_le.
  - intro a; apply monotone_union; reflexivity.
Qed.
#[global] Hint Resolve monotone_list_union : cotrie.

Fixpoint star_n' {n} (z a : lang n) (k : nat) : lang n :=
  match k with
  | O => z
  | S k' => union (pow a k') (star_n' z a k')
  end.

Fixpoint star_n'' {n} (z a : lang n) (k : nat) : lang n :=
  match k with
  | O => z
  | S k' => star_n'' (union (pow a k') z) a k'
  end.

Definition nstar {n} (a : lang n) : nat -> lang n :=
  iter empty (fun b => cotrie_node true (fun x => coconcat (delta a x) b)).

Definition coplus {n} (a : lang n) : lang n :=
  coiter (fun b => cotrie_node false (fun x => coconcat (delta a x) b)) omega.

(** Kleene star (extractible). *)
Definition star {n} (a : lang n) : lang n :=
  coiter (fun b => cotrie_node true (fun x => concat (delta a x) b)) omega.

Definition costar {n} (a : lang n) : lang n :=
  colist.cofold (fun n x => union x (pow a n)) (nats O).

(*
  empty
  union empty (pow a 0) = union empty epsilon = epsilon
  union epsilon (pow a 1) = union epsilon a
  union (union epsilon a) (pow a 2) = union (union epsilon a) (concat a a)
*)

Lemma monotone_star {n} (a : lang n)
  : Proper (leq ==> leq) (colist.fold ⊥ (fun k x  => union x (pow a k))).
Proof.
  apply colist.monotone_fold.
  { intro b; apply bot_le. }
  intro i.
  intros x y Hxy.
  apply monotone_union; auto.
  reflexivity.
Qed.
#[global] Hint Resolve monotone_star : cotrie.

(** Alternative star construction that is not extractible. *)
Definition star' {n} (a : lang n) : lang n :=
  sup (star_n a).

Definition star2 {n} (a : lang n) : lang n :=
  big_union (pow a).

Definition star'' {n} (a : lang n) : lang n :=
  sup (star_n'' empty a).

Definition star2' {n} (a : lang n) : lang n :=
  big_union (pow' a).

Lemma cotrie_le_tconcat'_prefix_coconcat' {n} (x y : lang n) (i : nat) :
  tconcat' (prefix i x) y ⊑ coconcat' x y.
Proof.
  unfold coconcat'.
  simpl.
  unfold co.
  rewrite sup_apply.
  unfold compose. 
  apply leq_cotrie_le.
  apply le_sup with (i:=i); reflexivity.
Qed.

#[global]
  Instance monotone_cotrie_node {A B} `{OType B} : Proper (leq ==> leq) (@cotrie_node A B).
Proof. intros a b Hab k; constructor; auto; intro; reflexivity. Qed.
#[global] Hint Resolve monotone_cotrie_node : cotrie.

#[global]
  Instance monotone_cotrie_node' {A B} `{OType B} (b : B) : Proper (leq ==> leq) (@cotrie_node A B b).
Proof. intros f g Hfg; constructor; auto; reflexivity. Qed.
#[global] Hint Resolve monotone_cotrie_node' : cotrie.

Lemma continuous_cotrie_node {A B} `{OType B} (b : B) :
  continuous (@cotrie_node A B b).
Proof.
  intros ch Hch f [Hub Hlub]; unfold compose; split.
  - intro i; constructor; try reflexivity.
    intro a; apply Hub.
  - intros [] Hx.
    assert (Hc: upper_bound c ch).
    { intro i; specialize (Hx i); inv Hx; auto. }
    apply Hlub in Hc.
    constructor; auto.
    specialize (Hx (S O)); inv Hx; auto.
Qed.

#[global]
  Instance monotone_delta {A B} `{OType B} : Proper (leq ==> leq) (@delta A B).
Proof. intros [] [] Hab; inv Hab; auto. Qed.

Lemma continuous_delta {A B} `{OType B} :
  continuous (@delta A B).
Proof.
  intros ch Hch ub [Hub Hlub]; split.
  - intros i x; apply monotone_delta; auto.
  - intros k Hk x.
    unfold delta. simpl.
    destruct ub.
    assert (H0: upper_bound (cotrie_node b k) ch).
    { intro i.
      specialize (Hub i).
      specialize (Hk i).
      unfold compose in Hk.
      unfold delta in Hk.
      simpl in Hk.
      inv Hub.
      constructor; auto.
      intro y; specialize (Hk y).
      rewrite  <- H0 in Hk.
      auto. }
    apply Hlub in H0.
    inv H0; auto.
Qed.

Lemma intersection_empty {n} :
  intersection empty = const (@empty n).
Proof.
  ext x.
  apply cotrie_ext.
  revert x; cofix CH.
  intro x.
  unfold const.
  rewrite (@unf_eq _ _ empty); simpl.
  rewrite intersection_node.
  destruct x; simpl.
  constructor.
  intro s; apply CH.
Qed.

(** Set interpretation stuff. *)

Lemma in_lang_empty {n} (l : list (Fin.t n)) :
  ~ in_lang empty l.
Proof.
  induction l; intro HC; inv HC.
  { rewrite (@unf_eq _ _ empty) in H0; inv H0. }
  rewrite (@unf_eq _ _ empty) in H; inv H.
  apply IHl, H1.
Qed.

Lemma in_lang_epsilon {n} (l : list (Fin.t n)) :
  in_lang epsilon l <-> l = [].
Proof.
  split.
  - intro H; destruct l; auto.
    inv H; apply in_lang_empty in H1; contradiction.
  - intros ->; constructor.
Qed.

Lemma in_lang_single {n} (l : list (Fin.t n)) (x : Fin.t n) :
  in_lang (single x) l <-> l = [x].
Proof.
  split.
  - intro Hl; destruct l.
    + inv Hl.
    + inv Hl.
      replace Fin.eqb with eqb in H0 by reflexivity.
      destruct (eqb_spec t x); subst.
      * apply in_lang_epsilon in H0; subst; auto.
      * apply in_lang_empty in H0; contradiction.
  - intros ->; constructor.
    rewrite eqb_refl; constructor.
Qed.

Lemma in_lang_union {n} (a b : lang n) (l : list (Fin.t n)) :
  in_lang (union a b) l <-> in_lang a l \/ in_lang b l.
Proof.
  split.
  - revert a b; induction l; intros [] [] Hxy.
    + rewrite union_node in Hxy; inv Hxy; destruct b.
      * left; constructor.
      * destruct b0; simpl in *; try congruence; right; constructor.
    + rewrite union_node in Hxy; inv Hxy; apply IHl in H0.
      destruct H0 as [H0|H0].
      * left; constructor; auto.
      * right; constructor; auto.
  - intros [H|H].
    + revert H; revert a b; induction l; intros [] [] Hxy.
      * inv Hxy; rewrite union_node; constructor.
      * inv Hxy; rewrite union_node; constructor; apply IHl; auto.
    + revert H; revert a b; induction l; intros [] [] Hxy.
      * inv Hxy; rewrite union_comm, union_node; constructor.
      * inv Hxy; rewrite union_node; constructor; apply IHl; auto.
Qed.

Lemma in_lang_cotrie_sup {n} (f : nat -> lang n) (l : list (Fin.t n)) :
  in_lang (cotrie_sup f) l <-> exists i, in_lang (f i) l.
Proof.
  split.
  - revert f; induction l; intros f Hl.
    + rewrite unf_eq in Hl.
      inv Hl.
      symmetry in H0.
      apply sup_true_exists_i in H0.
      unfold compose in H0.
      destruct H0 as [i Hi]; exists i.
      destruct (f i).
      simpl in Hi; subst.
      constructor.
    + rewrite unf_eq in Hl.
      inv Hl.
      apply IHl in H0.
      destruct H0 as [i Hi].
      exists i.
      destruct (f i).
      simpl in *.
      constructor; auto.
  - revert f; induction l; intros f [i Hi].
    + rewrite unf_eq; simpl.
      destruct (f i) eqn:Hfi; inv Hi.
      assert (H: sup (label ∘ f) = true).
      { apply ext.
        apply supremum_sup.
        split.
        - intro j.
          unfold compose.
          destruct (f j), b; simpl; auto.
        - intros x Hx.
          specialize (Hx i).
          unfold compose in Hx.
          rewrite Hfi in Hx.
          simpl in Hx.
          destruct x; auto. }
      rewrite H; constructor.
    + inv Hi.
      rewrite unf_eq; constructor.
      apply IHl; exists i.
      destruct (f i); inv H; auto.
Qed.

Lemma sup_cotrie_sup {n} (f : nat -> lang n) :
  sup f = cotrie_sup f.
Proof. apply ext, supremum_sup, supremum_cotrie_sup. Qed.

Lemma union_sup {n} (f : nat -> lang n) :
  union (sup f) = sup (union ∘ f).
Proof.
  ext y.
  apply ext.
  rewrite sup_apply.
  apply eq_equ.
  rewrite 2!sup_cotrie_sup.
  apply in_lang_eq.
  intro l.
  split.
  - intro H.
    apply in_lang_union in H.
    destruct H as [H|H].
    + apply in_lang_cotrie_sup in H.
      destruct H as [i Hi].
      apply in_lang_cotrie_sup.
      exists i; apply in_lang_union; left; auto.
    + apply in_lang_cotrie_sup.
      exists O; apply in_lang_union; right; auto.
  - intro H.
    apply in_lang_cotrie_sup in H.
    destruct H as [i H].
    apply in_lang_union in H.
    apply in_lang_union.
    destruct H as [H|H].
    + left; apply in_lang_cotrie_sup; exists i; auto.
    + right; auto.
Qed.

Lemma coconcat'_node' {n} (a : lang n) (b : bool) (k : Fin.t n -> lang n) :
  coconcat' a (cotrie_node b k) =
    match a with
    | cotrie_node b' k' =>
        cotrie_node (b' && b)
          (fun a => union (coconcat' (k' a) (cotrie_node b k)) (if b' then k a else empty))
    end.
Proof.
  destruct a.
  unfold coconcat'.
  unfold co.
  apply ext.
  rewrite sup_apply.
  unfold compose.
  unfold flip.
  apply supremum_sup.
  eapply shift_supremum''.
  { apply cotrie_bot_le. }
  2: { reflexivity. }
  unfold shift.
  simpl.
  apply continuous_cotrie_node.
  { apply monotone_directed; auto with order.
    intros i j Hij a.
    simpl; unfold compose.
    apply monotone_union.
    - apply monotone_tconcat', monotone_prefix'; auto.
    - reflexivity. }
  unfold compose.
  apply supremum_apply.
  intro a.
  assert (Hs: supremum
                (union (sup (fun x : nat => tconcat' (flip prefix (c a) x)) (cotrie_node b k)))
                (fun i : nat => union (tconcat' (prefix i (c a)) (cotrie_node b k)))).
  { rewrite sup_apply.
    rewrite union_sup.
    apply sup_spec. }
  eapply apply_supremum in Hs; eauto.
Qed.

Lemma coconcat'_node {n} (b : bool) (k : Fin.t n -> lang n) :
  coconcat' (cotrie_node b k) =
    fun l => match l with
          | cotrie_node b' k' => cotrie_node (b && b')
                             (fun a => union (coconcat' (k a) l) (if b then k' a else empty))
          end.
Proof.
  unfold coconcat'.
  ext x.
  destruct x.
  apply ext.
  unfold co.
  rewrite sup_apply.
  apply supremum_sup.  
  eapply shift_supremum''.
  { apply cotrie_bot_le. }
  2: { reflexivity. }
  unfold shift.
  simpl.
  apply continuous_cotrie_node.
  { apply monotone_directed; auto with order.
    intros i j Hij a.
    simpl; unfold compose.
    apply monotone_union.
    - apply monotone_tconcat', monotone_prefix'; auto.
    - reflexivity. }
  unfold compose.
  apply supremum_apply.
  intro a.

  assert (Hs: supremum
    (union (sup (fun x : nat => tconcat' (flip prefix (k a) x)) (cotrie_node b0 c)))
    (fun i : nat =>
     union
       ((fix tconcat' (n0 : nat) (x : tlang n0) (y : lang n0) {struct x} : lang n0 :=
           match x with
           | trie_bot => empty
           | trie_node b1 k1 =>
               match y with
               | cotrie_node b2 k2 =>
                   cotrie_node (b1 && b2)
                     (fun a0 : t n0 =>
                      union (tconcat' n0 (k1 a0) y) (if b1 then k2 a0 else empty))
               end
           end) n
          ((fix prefix (A B : Type) (n0 : nat) (t : cotrie A B) {struct n0} : trie A B :=
              match n0 with
              | 0 => trie_bot
              | S n' =>
                  match t with
                  | cotrie_node b1 k0 => trie_node b1 (fun x : A => prefix A B n' (k0 x))
                  end
              end) (t n) bool i (k a)) (cotrie_node b0 c)))).
  { rewrite sup_apply.
    rewrite union_sup.
    apply sup_spec. }
  eapply apply_supremum in Hs; eauto.
Qed.

Lemma concat_node {n} (b : bool) (k : Fin.t n -> lang n) :
  concat (cotrie_node b k) =
    fun l => match l with
          | cotrie_node b' k' => cotrie_node (b && b')
                             (fun a => union (concat (k a) l) (if b then k' a else empty))
          end.
Proof.
  ext a; destruct a; rewrite coconcat_coconcat', coconcat'_node; reflexivity.
Qed.

Lemma concat_node' {n} (a : lang n) (b : bool) (k : Fin.t n -> lang n) :
  concat a (cotrie_node b k) =
    match a with
    | cotrie_node b' k' =>
        cotrie_node (b' && b)
          (fun a => union (concat (k' a) (cotrie_node b k)) (if b' then k a else empty))
    end.
Proof.
  destruct a; rewrite coconcat_coconcat', coconcat'_node'; reflexivity.
Qed.

Lemma seq_prefix_S_shift {A} (f : nat -> A) (i : nat) :
  seq_prefix f (S i) = f O :: seq_prefix (shift f) i.
Proof.
  unfold seq_prefix; simpl.
  revert f; induction i; intro f; simpl; auto.
  rewrite IHi; reflexivity.
Qed.

Lemma in_lang_concat {n} (a b : lang n) (l : list (Fin.t n)) :
  in_lang (concat a b) l <-> exists l1 l2, l = l1 ++ l2 /\ in_lang a l1 /\ in_lang b l2.
Proof.
  split.
  - revert a b; induction l; intros [] [] Hl.
    + rewrite concat_node in Hl.
      inv Hl.
      destruct b, b0; simpl in *; try congruence.
      exists [], []; split; auto; split; constructor.
    + rewrite concat_node in Hl.
      inv Hl.
      apply in_lang_union in H0.
      destruct H0 as [H0|H0].
      * apply IHl in H0.
        destruct H0 as [l1 [l2 [Heq [Hl1 Hl2]]]]; subst.
        exists (a :: l1), l2; split; auto; split; auto; constructor; auto.
      * destruct b.
        { exists [], (a :: l); split; auto; split.
          - constructor.
          - constructor; auto. }
        apply in_lang_empty in H0; contradiction.
  - revert a b; induction l; intros [] [] [l1 [l2 [Heq [Hl1 Hl2]]]]; subst.
    + symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      inv Hl1; inv Hl2.
      rewrite concat_node; constructor.
    + rewrite concat_node.
      inv Hl1.
      * inv Hl2.
        { inv Heq. }
        simpl in *.
        inv Heq.
        constructor.
        apply in_lang_union.
        right; auto.
      * inv Hl2.
        { simpl in *.
          rewrite app_nil_r in Heq; inv Heq.
          constructor.
          apply in_lang_union.
          left.
          apply IHl.
          exists xs, []; repeat split; auto.
          - rewrite app_nil_r; reflexivity.
          - constructor. }
        simpl in *.
        constructor.
        apply in_lang_union.
        left.
        apply IHl.
        inv Heq.
        exists xs, (x0 :: xs0); repeat split; auto.
        constructor; auto.
Qed.

Lemma concat_cotrie_sup {n} (a : lang n) (f : nat -> lang n) :
  concat a (cotrie_sup f) = cotrie_sup (concat a ∘ f).
Proof.
  apply in_lang_eq.
  intro l.
  split.
  - intro H.
    apply in_lang_concat in H.
    destruct H as [l1 [l2 [Heq [Hl1 Hl2]]]]; subst.
    apply in_lang_cotrie_sup in Hl2.
    destruct Hl2 as [i Hl2].
    apply in_lang_cotrie_sup.
    exists i.
    unfold compose.
    apply in_lang_concat.
    exists l1, l2; repeat split; auto.
  - intro H.
    apply in_lang_cotrie_sup in H.
    destruct H as [i H].
    apply in_lang_concat in H.
    destruct H as [l1 [l2 [Heq [Hl1 Hl2]]]]; subst.
    apply in_lang_concat.
    exists l1, l2; repeat split; auto.
    apply in_lang_cotrie_sup.
    exists i; auto.
Qed.

(** Strategy is to go through set interpretations (concat_cotrie_sup
    proves continuity). *)
Lemma continuous_coconcat' {n} (a : lang n) :
  continuous (coconcat' a).
Proof.
  intros ch Hch x Hx.
  assert (Hsup: x = sup ch).
  { apply ext; symmetry; apply supremum_sup; auto. }
  subst; clear Hx.
  rewrite sup_cotrie_sup.
  rewrite <- coconcat_coconcat'.
  rewrite concat_cotrie_sup.
  apply supremum_cotrie_sup.
Qed.

Lemma continuous_concat {n} (a : lang n) :
  continuous (concat a).
Proof. rewrite coconcat_coconcat'; apply continuous_coconcat'. Qed.

Lemma continuous_coconcat'' {n} (a : lang n) :
  continuous (fun x : lang n => coconcat' x a).
Proof.
  intros ch Hch x Hx.
  apply apply_supremum.
  simpl.
  unfold compose, flip.
  replace (fun i : nat => let (a0, _) := sup_prim (fun x0 : nat => tconcat' (prefix x0 (ch i))) in a0)
    with (coconcat' ∘ ch).
  2: { ext i; reflexivity. }
  apply continuous_co; auto.
  apply monotone_tconcat'.
Qed.

Lemma continuous_concat''' {n} (a : lang n) :
  continuous (fun x : lang n => concat x a).
Proof.
  intros ch Hch x Hx.
  apply apply_supremum.
  simpl.
  unfold compose, flip.
  replace (fun i : nat => let (a0, _) := sup_prim (fun x0 : nat => tconcat (prefix x0 (ch i))) in a0)
    with (concat ∘ ch).
  2: { ext i; reflexivity. }
  apply continuous_co; auto.
  apply monotone_tconcat.
Qed.

(** Kleene algebra laws. *)

Theorem union_assoc {n} (x y z : lang n) :
  union (union x y) z = union x (union y z).
Proof.
  apply cotrie_ext.
  revert x y z; cofix CH; intros [] [] [].
  rewrite 3!union_node.
  rewrite Bool.orb_assoc; constructor.
  intro a; apply CH.
Qed.

Lemma intersection_assoc {n} (x y z : lang n) :
  intersection (intersection x y) z = intersection x (intersection y z).
Proof.
  apply cotrie_ext.
  revert x y z; cofix CH; intros [] [] [].
  rewrite 3!intersection_node.
  rewrite Bool.andb_assoc; constructor.
  intro a; apply CH.
Qed.

Lemma intersection_comm {n} (x y : lang n) :
  intersection x y = intersection y x.
Proof.
  apply cotrie_ext.
  revert x y; cofix CH; intros x y.
  destruct x, y.
  rewrite 2!intersection_node.
  rewrite Bool.andb_comm.
  constructor; intro a; apply CH.
Qed.

Theorem union_idempotent {n} (x : lang n) :
  union x x = x.
Proof.
  apply cotrie_ext.
  revert x; cofix CH; intros [].
  rewrite union_node.
  rewrite Bool.orb_diag.
  constructor; auto.
Qed.

Lemma union_intersection_l {n} (x y : lang n) :
  x = union x (intersection x y).
Proof.
  apply cotrie_ext.
  revert x y; cofix CH; intros [] [].
  rewrite union_node, intersection_node.
  rewrite Bool.absorption_orb; constructor; intro a; apply CH.
Qed.

Lemma intersection_union_distr_r {n} (x y z : lang n) :
  intersection x (union y z) = union (intersection x y) (intersection x z).
Proof.
  apply cotrie_ext.
  revert x y z; cofix CH; intros [] [] [].
  rewrite intersection_node, 2!union_node.
  rewrite Bool.andb_orb_distrib_r.
  constructor; intro a; apply CH.
Qed.

Lemma intersection_union_distr_l {n} (x y z : lang n) :
  intersection (union x y) z = union (intersection x z) (intersection y z).
Proof.
  rewrite intersection_comm, intersection_union_distr_r.
  f_equal; apply intersection_comm.
Qed.

Lemma intersection_empty_l {n} (x : lang n) :
  intersection empty x = empty.
Proof.
  apply cotrie_ext; destruct x; rewrite intersection_empty; reflexivity.
Qed.

Lemma intersection_empty_r {n} (x : lang n) :
  intersection x empty = empty.
Proof. rewrite intersection_comm; apply intersection_empty_l. Qed.

Lemma prefix_union_tunion {n} (x y : lang n) (i : nat) :
  prefix i (union x y) = tunion (prefix i x) (prefix i y).
Proof.
  revert x y; induction i; simpl; intros [] []; auto.
  simpl.
  f_equal.
  ext a.
  unfold compose.
  apply IHi.
Qed.

Lemma trie_cotrie_le_union_l {n} (x : tlang n) (y z : lang n) :
  trie_cotrie_le x y ->
  trie_cotrie_le x (union y z).
Proof.
  revert y z; induction x; intros y z Hxy; simpl.
  { constructor; constructor. }
  inv Hxy.
  { constructor; auto. }
  rewrite union_node.
  destruct z.
  apply trie_cotrie_le_node; auto.
  apply bool_le_orb_l; auto.
Qed.

Lemma trie_cotrie_le_union_r {n} (x : tlang n) (y z : lang n) :
  trie_cotrie_le x z ->
  trie_cotrie_le x (union y z).
Proof.
  intro Hxz; rewrite union_comm; apply trie_cotrie_le_union_l; auto.
Qed.

Lemma is_bot_tunion {n} (a b : tlang n) :
  is_bot a ->
  is_bot b ->
  is_bot (tunion a b).
Proof.
  revert b; induction a; intros b' Ha Hb; simpl; auto.
  inv Ha.
  destruct b'.
  - constructor; auto.
  - inv Hb. constructor.
    + destruct b, b0; auto.
    + intro a; apply H; auto.
Qed.

Lemma trie_cotrie_le_tunion {n} (x y : tlang n) (z w : lang n) :
  trie_cotrie_le x z ->
  trie_cotrie_le y w ->
  trie_cotrie_le (tunion x y) (union z w).
Proof.
  revert y z w; induction x; intros y z w Hxz Hyw; simpl.
  - apply trie_cotrie_le_union_r; auto.
  - inv Hxz.
    { inv H0.
      destruct y.
      - apply trie_cotrie_le_bot; constructor; auto.
      - destruct z, w.
        rewrite union_node.
        apply trie_cotrie_le_node.
        + apply bool_le_orb.
          * rewrite H3; apply bot_le.
          * inv Hyw; auto.
            inv H0; rewrite H5; apply bot_le.
        + intro a.
          inv Hyw.
          * inv H0.
            apply trie_cotrie_le_bot; auto.
            apply is_bot_tunion; auto.
          * apply H; auto.
            apply trie_cotrie_le_bot; auto. }
    destruct y.
    + rewrite union_node.
      destruct w.
      apply trie_cotrie_le_node.
      * apply bool_le_orb_l; auto.
      * intro a; apply trie_cotrie_le_union_l; auto.
    + inv Hyw.
      * inv H0.
        rewrite union_node.
        destruct w.
        apply trie_cotrie_le_node.
        { apply bool_le_orb; auto; rewrite H5; apply bot_le. }
        intro a. apply H; auto.
        apply trie_cotrie_le_bot; auto.
      * rewrite union_node.
        apply trie_cotrie_le_node.
        {  apply bool_le_orb; auto. }
        { intro a; apply H; auto. }
Qed.

Lemma trie_cotrie_le_prefix {A B} `{PType B} (x y : cotrie A B) (i : nat) :
  cotrie_le x y ->
  trie_cotrie_le (prefix i x) y.
Proof.
  revert x y; induction i; intros [] [] Hxy; simpl; inv Hxy.
  - constructor; constructor.
  - apply trie_cotrie_le_node; auto; intro a; apply IHi; auto.
Qed.

Lemma union_assoc4 {n} (x y z w : lang n) :
  union (union (union x y) w) z = union (union x w) (union y z).
Proof.
  rewrite 3!union_assoc; f_equal.
  rewrite <- union_assoc, (union_comm y w).
  apply union_assoc.
Qed.

(** Can't do primitive coinduction because applications of CIH are
    under union (concat is primitive corecursive up-to union). *)
Theorem concat_union_distr_r {n} (x y z : lang n) :
  concat (union x y) z = union (concat x z) (concat y z).
Proof.
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    + constructor; constructor.
    + rewrite concat_node'.
      rewrite union_node.
      rewrite concat_node'.
      rewrite union_node.
      rewrite concat_node'.
      unfold compose.
      rewrite Bool.andb_orb_distrib_l.
      apply trie_cotrie_le_node.
      { reflexivity. }
      intro a.
      destruct b; simpl.
      * destruct b0; simpl.
        { rewrite <- union_assoc.
          rewrite prefix_union_tunion.
          rewrite union_assoc4.
          rewrite union_idempotent.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
        { rewrite union_empty_r.
          rewrite prefix_union_tunion.
          rewrite union_assoc.
          rewrite (union_comm (c1 a)).
          rewrite <- union_assoc.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
      * rewrite union_empty_r.
        destruct b0.
        { rewrite <- union_assoc.
          rewrite prefix_union_tunion.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
        rewrite 2!union_empty_r.
        apply IHi.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    + constructor; constructor.
    + rewrite concat_node'.
      rewrite union_node.
      rewrite concat_node'.
      rewrite concat_node'.
      unfold compose.
      rewrite Bool.andb_orb_distrib_l.
      apply trie_cotrie_le_node.
      { reflexivity. }
      intro a.
      destruct b; simpl.
      * destruct b0; simpl.
        { rewrite <- union_assoc.
          rewrite union_assoc4.
          rewrite prefix_union_tunion.
          rewrite union_idempotent.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
        { rewrite union_empty_r.
          rewrite union_assoc.
          rewrite (union_comm (c1 a)).
          rewrite <- union_assoc.
          rewrite prefix_union_tunion.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
      * rewrite union_empty_r.
        destruct b0.
        { rewrite <- union_assoc.
          rewrite prefix_union_tunion.
          apply trie_cotrie_le_tunion.
          2: { apply trie_cotrie_le_prefix; reflexivity. }
          apply IHi. }
        rewrite 2!union_empty_r.
        apply IHi.
Qed.

Theorem concat_union_distr_l {n} (x y z : lang n) :
  concat x (union y z) = union (concat x y) (concat x z).
Proof.
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    + constructor; constructor.
    + rewrite concat_node.
      rewrite union_node.
      rewrite union_node.
      unfold compose.
      rewrite Bool.andb_orb_distrib_r.
      apply trie_cotrie_le_node.
      { reflexivity. }
      intro a.
      destruct b.
      * replace (cotrie_node (b0 || b1) (fun x : Fin.t n => union (c0 x) (c1 x))) with
          (union (cotrie_node b0 c0) (cotrie_node b1 c1)).
        2: { rewrite union_node; reflexivity. }
        rewrite prefix_union_tunion.
        rewrite union_assoc.
        rewrite (union_comm (c0 a) (union _ _)).
        rewrite union_assoc.
        rewrite <- union_assoc.
        apply trie_cotrie_le_tunion.
        { apply IHi. }
        rewrite union_comm.
        apply trie_cotrie_le_prefix; reflexivity.
      * replace (cotrie_node (b0 || b1) (fun x : Fin.t n => union (c0 x) (c1 x))) with
          (union (cotrie_node b0 c0) (cotrie_node b1 c1)).
        2: { rewrite union_node; reflexivity. }
        rewrite 3!union_empty_r.
        apply IHi.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    + constructor; constructor.
    + rewrite concat_node.
      rewrite union_node.
      unfold compose.
      rewrite Bool.andb_orb_distrib_r.
      apply trie_cotrie_le_node.
      { reflexivity. }
      intro a.
      destruct b.
      * replace (cotrie_node (b0 || b1) (fun x : Fin.t n => union (c0 x) (c1 x))) with
          (union (cotrie_node b0 c0) (cotrie_node b1 c1)).
        2: { rewrite union_node; reflexivity. }
        rewrite union_assoc.
        rewrite (union_comm (c0 a) (union _ _)).
        rewrite union_assoc.
        rewrite <- union_assoc.
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { rewrite union_comm; apply trie_cotrie_le_prefix; reflexivity. }
        apply IHi.
      * replace (cotrie_node (b0 || b1) (fun x : Fin.t n => union (c0 x) (c1 x))) with
          (union (cotrie_node b0 c0) (cotrie_node b1 c1)).
        2: { rewrite union_node; reflexivity. }
        rewrite 3!union_empty_r.
        apply IHi.
Qed.

Theorem concat_assoc {n} (x y z : lang n) :
  concat (concat x y) z = concat x (concat y z).
Proof.
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    { constructor; constructor. }
    rewrite 3!concat_node.
    unfold compose.
    rewrite Bool.andb_assoc.
    apply trie_cotrie_le_node.
    { reflexivity. }
    intro a.
    destruct b; simpl.
    + destruct b0; simpl.
      * rewrite <- union_assoc.
        rewrite concat_union_distr_r.
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        replace (cotrie_node b1 (fun a0 : Fin.t n =>
                              union (concat (c0 a0) (cotrie_node b1 c1)) (c1 a0)))
          with (concat (cotrie_node true c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
      * rewrite 2!union_empty_r.
        rewrite concat_union_distr_r.
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        replace (cotrie_node false (fun a0 : Fin.t n =>
                                 union (concat (c0 a0) (cotrie_node b1 c1)) empty))
          with (concat (cotrie_node false c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
    + destruct b0; simpl.
      * rewrite 3!union_empty_r.
        replace (cotrie_node b1 (fun a0 : Fin.t n =>
                              union (concat (c0 a0) (cotrie_node b1 c1)) (c1 a0)))
          with (concat (cotrie_node true c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
      * rewrite 3!union_empty_r.
        replace (cotrie_node false (fun a0 : Fin.t n =>
                                 union (concat (c0 a0) (cotrie_node b1 c1)) empty))
          with (concat (cotrie_node false c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x y z; induction i; intros [] [] []; simpl.
    { constructor; constructor. }
    rewrite 3!concat_node.
    unfold compose.
    rewrite Bool.andb_assoc.
    apply trie_cotrie_le_node.
    { reflexivity. }
    intro a.
    destruct b; simpl.
    + destruct b0; simpl.
      * rewrite <- union_assoc.
        rewrite concat_union_distr_r.
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        replace (cotrie_node b1 (fun a0 : Fin.t n =>
                              union (concat (c0 a0) (cotrie_node b1 c1)) (c1 a0)))
          with (concat (cotrie_node true c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
      * rewrite 2!union_empty_r.
        rewrite concat_union_distr_r.
        rewrite prefix_union_tunion.
        apply trie_cotrie_le_tunion.
        2: { apply trie_cotrie_le_prefix; reflexivity. }
        replace (cotrie_node false (fun a0 : Fin.t n =>
                                 union (concat (c0 a0) (cotrie_node b1 c1)) empty))
          with (concat (cotrie_node false c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
    + destruct b0; simpl.
      * rewrite 3!union_empty_r.
        replace (cotrie_node b1 (fun a0 : Fin.t n =>
                              union (concat (c0 a0) (cotrie_node b1 c1)) (c1 a0)))
          with (concat (cotrie_node true c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
      * rewrite 3!union_empty_r.
        replace (cotrie_node false (fun a0 : Fin.t n =>
                                 union (concat (c0 a0) (cotrie_node b1 c1)) empty))
          with (concat (cotrie_node false c0) (cotrie_node b1 c1)).
        2: { rewrite concat_node; reflexivity. }
        apply IHi.
Qed.

Theorem concat_empty_l {n} (x : lang n) :
  concat empty x = empty.
Proof.
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node'; simpl.
    unfold compose.
    remember (trie_node false (fun x : Fin.t n =>
                             prefix i (union (concat (const cotrie_bot x)
                                                (cotrie_node b c)) empty))) as y.
    rewrite (@unf_eq _ _ empty); simpl.
    subst.
    apply trie_cotrie_le_node.
    + reflexivity.
    + intro a.
      unfold const.
      rewrite union_empty_r.
      apply IHi.
  - apply cotrie_bot_le.
Qed.

Theorem concat_empty_r {n} (x : lang n) :
  concat x empty = empty.
Proof.
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node; simpl.
    rewrite Bool.andb_false_r.
    unfold compose.
    unfold const.
    destruct b.
    + remember (trie_node false (fun x : Fin.t n =>
                               prefix i (union (concat (c x) empty) cotrie_bot)))
        as y.
      rewrite (@unf_eq _ _ empty); simpl.
      subst.
      apply trie_cotrie_le_node.
      * reflexivity.
      * intro a.
        unfold const.
        replace cotrie_bot with (@empty n) by reflexivity.
        rewrite union_empty_r.
        apply IHi.
    + remember (trie_node false (fun x : Fin.t n =>
                               prefix i (union (concat (c x) empty) empty)))
        as y.
      rewrite (@unf_eq _ _ empty); simpl.
      subst.
      apply trie_cotrie_le_node.
      * reflexivity.
      * intro a.
        rewrite union_empty_r.
        apply IHi.
  - apply cotrie_bot_le.
Qed.

Theorem concat_epsilon_l {n} (x : lang n) :
  concat epsilon x = x.
Proof.  
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node'; simpl.
    apply trie_cotrie_le_node.
    + reflexivity.
    + intro a.
      unfold compose.
      unfold const.
      rewrite concat_empty_l.
      rewrite union_empty_l.
      apply trie_cotrie_le_prefix; reflexivity.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node'.
    simpl.
    apply trie_cotrie_le_node.
    + reflexivity.
    + intro a.
      unfold compose.
      unfold const.
      rewrite concat_empty_l.
      rewrite union_empty_l.
      apply trie_cotrie_le_prefix; reflexivity.
Qed.

Theorem concat_epsilon_r {n} (x : lang n) :
  concat x epsilon = x.
Proof.  
  apply ext; split.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node; simpl.
    rewrite Bool.andb_true_r.
    apply trie_cotrie_le_node.
    + reflexivity.
    + intro a.
      unfold compose.
      unfold const.
      destruct b; rewrite union_empty_r; apply IHi.
  - apply cotrie_le_cotrie_le'.
    apply coop_intro2; eauto with cotrie order.
    intro i; simpl; unfold flip.
    revert x; induction i; intros []; simpl.
    { constructor; constructor. }
    rewrite concat_node; simpl.
    rewrite Bool.andb_true_r.
    apply trie_cotrie_le_node.
    + reflexivity.
    + intro a.
      unfold compose.
      unfold const.
      destruct b; rewrite union_empty_r; apply IHi.
Qed.

Lemma union_star_n' {n} (z a x : lang n) (k : nat) :
  union x (star_n' z a k) = star_n' (union x z) a k.
Proof.
  revert z a x; induction k; intros z a x; simpl; auto.
  rewrite 3!IHk.
  rewrite <- 2!union_assoc.
  f_equal; f_equal.
  rewrite union_comm; auto.
Qed.

Lemma star_n'_star_n'' {n} (z a : lang n) :
  star_n' z a = star_n'' z a.
Proof.
  ext k; revert z a; induction k; intros z a; simpl; auto.
  rewrite <- IHk.
  rewrite union_star_n'; auto.
Qed.

Lemma fold_range_star_n'' {n} (a z : lang n) (i : nat) :
  colist.fold z (fun (k : nat) (x : lang n) => union x (pow a k)) (range i) =
    star_n'' z a i.
Proof.
  revert a z; induction i; simpl; intros a z; auto.
  - rewrite fold_app; simpl.
    rewrite IHi; f_equal; apply union_comm.
Qed.

Lemma union_star_n''_star_n' {n} (a z x : lang n) (i : nat) :
  union (star_n'' x a i) z = union x (star_n' z a i).
Proof.
  revert a z x; induction i; intros a z x; simpl; auto.
  rewrite IHi.
  rewrite <- union_assoc.
  f_equal; apply union_comm.
Qed.

Lemma star_n_star_n' {n} (a : lang n) :
  star_n a = star_n' empty a.
Proof.
  ext i; revert a; induction i; intro a; simpl; auto.
  rewrite IHi; reflexivity.
Qed.

Lemma cotrie_le_union_l {n} (x y z : lang n) :
  x ⊑ y ->
  x ⊑ union y z.
Proof.
  revert x y z; cofix CH; intros [] [] [] Hle; inv Hle.
  rewrite union_node; constructor.
  - apply bool_le_orb_l; auto.
  - intro a; apply CH, H4.
Qed.

Lemma cotrie_le_union_r {n} (x y z : lang n) :
  x ⊑ z ->
  x ⊑ union y z.
Proof. rewrite union_comm; apply cotrie_le_union_l. Qed.

#[global]
 Instance monotone_concat' {n} : Proper (leq ==> leq ==> leq) (@concat n).
Proof.
  intros x y Hxy z w Hzw.
  apply cotrie_le_cotrie_le'.
  apply coop_intro2; eauto with cotrie order; intro i.
  simpl; unfold flip.
  revert Hxy Hzw.
  revert x y z w.
  induction i; simpl; intros [] [] [] [] Hxy Hzw.
  { constructor; constructor. }
  rewrite 2!concat_node.
  inv Hxy.
  inv Hzw.
  apply trie_cotrie_le_node.
  - apply bool_le_andb; auto.
  - intro a; unfold compose.
    rewrite prefix_union_tunion.
    apply trie_cotrie_le_tunion. 
    * apply IHi.
      { apply H4. }
      constructor; auto.
    * apply trie_cotrie_le_prefix; auto.
      destruct b, b0; simpl in *; try contradiction; auto; apply cotrie_bot_le.
Qed.

#[global]
 Instance monotone_concat {n} : Proper (leq ==> leq ==> leq) (@concat n).
Proof.
  intros x y Hxy z w Hzw.
  apply monotone_concat'; auto.
Qed.

#[global]
  Instance monotone_nstar {n} (a : lang n) : Proper (leq ==> leq) (nstar a).
Proof.
  apply monotone_iter.
  - intro i; apply cotrie_bot_le.
  - intros x y Hxy; constructor; try reflexivity.
    intro b; apply monotone_concat; auto; reflexivity.
Qed.
#[global] Hint Resolve monotone_nstar : cotrie.

Lemma monotone_star_n {n} (a : lang n) : Proper (leq ==> leq) (star_n a).
Proof.
  intros i j Hij.
  apply chain_leq; auto.
  clear Hij i j.
  intro i; simpl.
  apply cotrie_le_union_r; reflexivity.
Qed.
#[global] Hint Resolve monotone_star_n : cotrie.

Lemma costar_star' {n} (a : lang n) :
  costar a = star' a.
Proof.
  unfold costar, star'.
  unfold colist.cofold, co.
  f_equal; ext i.
  simpl; unfold compose, flip.
  rewrite prefix_nats.
  rewrite <- range_seq.
  revert a; induction i; intro a; simpl; auto.
  rewrite fold_app.
  simpl.
  rewrite fold_range_star_n''.
  replace cotrie_bot with (@empty n) by reflexivity.
  rewrite union_empty_l.
  rewrite star_n_star_n'.
  rewrite <- union_star_n''_star_n'.
  rewrite union_empty_r; auto.
Qed.

Lemma cotrie_le_z_list_union {n} (z : lang n) (l : list (lang n)) :
  cotrie_le z (list_union z l).
Proof.
  revert z; induction l; intro z; simpl.
  { reflexivity. }
  apply cotrie_le_union_r; apply IHl.
Qed.

Lemma union_le {n} (a b x : lang n) :
  a ⊑ x ->
  b ⊑ x ->
  union a b ⊑ x.
Proof.
  revert a b x; cofix CH; intros [] [] x Ha Hb.
  inv Ha; inv Hb.
  rewrite union_node.
  constructor.
  - destruct b, b0, b'; simpl; auto.
  - intro a; apply CH.
    + apply H3.
    + apply H6.
Qed.

Lemma in_list_union_le {n} (a z : lang n) (l : list (lang n)) :
  In a l ->
  a ⊑ list_union z l.
Proof.
  unfold list_union.
  revert a z; induction l; intros x z Hin; inv Hin; simpl.
  - apply cotrie_le_union_l; reflexivity.
  - apply cotrie_le_union_r, IHl; auto.
Qed.

Lemma list_union_monotone {n} (z : lang n) (l1 l2 : list (lang n)) :
  List.Forall (fun a => List.In a l2) l1 ->
  list_union z l1 ⊑ list_union z l2.
Proof.
  unfold list_union.
  revert z l2; induction l1; intros z l2 Hall; simpl.
  { apply cotrie_le_z_list_union. }
  inv Hall.
  apply union_le; auto.
  apply in_list_union_le; auto.
Qed.

#[global]
  Instance monotone_union_n' {n} (f : nat -> lang n)
  : Proper (leq ==> leq) (union_n' empty f).
Proof.
  intros i j Hij.
  unfold union_n'.
  apply list_union_monotone.
  apply seq_prefix_aux_monotone; auto.
Qed.
#[global] Hint Resolve monotone_union_n' : cotrie.

Lemma union_cotrie_sup {n} (a : lang n) (f : nat -> lang n) :
  union a (cotrie_sup f) = cotrie_sup (union a ∘ f).
Proof.
  apply in_lang_eq.
  intro l.
  split.
  - intro H.
    apply in_lang_union in H.
    destruct H as [H|H].
    + apply in_lang_cotrie_sup.
      exists O; apply in_lang_union; left; auto.
    + apply in_lang_cotrie_sup in H.
      destruct H as [i Hi].
      apply in_lang_cotrie_sup.
      exists i; apply in_lang_union; right; auto.
  - intro H.
    apply in_lang_cotrie_sup in H.
    destruct H as [i H].
    apply in_lang_union.
    unfold compose in H.
    apply in_lang_union in H.
    destruct H as [H|H].
    + left; auto.
    + right; apply in_lang_cotrie_sup; exists i; auto.
Qed.

Lemma continuous2_union {n} (x : lang n) :
  continuous (union x).
Proof.
  intros ch Hch y Hy.
  assert (Hsup: y = sup ch).
  { apply ext; symmetry; apply supremum_sup; auto. }
  subst; clear Hy.
  rewrite sup_cotrie_sup.
  rewrite union_cotrie_sup.
  apply supremum_cotrie_sup.
Qed.

Lemma big_union_shift {n} (f : nat -> lang n) :
  big_union f = union (f O) (big_union (shift f)).
Proof.
  apply ext; unfold big_union; rewrite <- sup_shift.
  2: { intro i; apply monotone_union_n; simpl; lia. }
  rewrite continuous_sup with (f := union (f O)).
  2: { apply continuous2_union. }
  2: { apply monotone_directed; eauto with order cotrie.
       apply chain_directed, chain_seq_prefix. }
  apply eq_equ; f_equal.
  unfold compose.
  ext i.
  unfold shift; simpl.
  unfold union_n.
  unfold list_union.
  simpl.
  rewrite seq_prefix_S_shift; reflexivity.
Qed.

Lemma union_n_union_n' {n} :
  @union_n n = union_n'.
Proof.
  ext z; ext g; ext i.
  unfold union_n, union_n'; apply ext.
  split; apply list_union_monotone; auto; apply Forall_forall; intros x Hx.
  - apply in_rev; auto.
  - apply in_rev in Hx; auto.
Qed.

Lemma star_n'_union_n {n} (z a : lang n) :
  star_n' z a = union_n z (pow a).
Proof.
  rewrite union_n_union_n'.
  ext i; revert z a; induction i; intros z a; simpl; auto.
  rewrite IHi; auto.
Qed.

Lemma star'_star2 {n} (a : lang n) :
  star' a = star2 a.
Proof.
  unfold star', star2, big_union.
  f_equal.
  rewrite star_n_star_n'.
  apply star_n'_union_n.
Qed.

Lemma star'_star'' {n} (a : lang n) :
  star' a = star'' a.
Proof.
  unfold star', star''.
  rewrite star_n_star_n', star_n'_star_n''; reflexivity.
Qed.

Lemma concat_pow' {n} (a : lang n) (i : nat) :
  concat (pow' a i) a = concat a (pow' a i).
Proof.
  revert a; induction i; intro a; simpl.
  { rewrite concat_epsilon_l, concat_epsilon_r; reflexivity. }
  rewrite <- IHi.
  rewrite <- concat_assoc.
  rewrite IHi; reflexivity.
Qed.

Lemma pow_pow' {n} :
  @pow n = pow'.
Proof.
  ext a; ext i.
  revert a; induction i; intro a; simpl; auto.
  rewrite IHi.
  apply concat_pow'.
Qed.

Lemma star2_star2' {n} (a : lang n) :
  star2 a = star2' a.
Proof. unfold star2, star2'; rewrite pow_pow'; reflexivity. Qed.

Lemma list_union_concat {n} (a : lang n) f i :
  colist.fold empty union (seq_prefix (fun n : nat => concat (f n) a) i) =
    concat (colist.fold empty union (seq_prefix f i)) a.
Proof.
  revert a f; induction i; simpl; intros a f.
  { rewrite concat_empty_l; reflexivity. }
  rewrite 2!seq_prefix_S_shift.
  simpl; unfold shift.
  rewrite concat_union_distr_r.
  f_equal; apply IHi.
Qed.

Lemma list_union_concat' {n} (a : lang n) f i :
  colist.fold empty union (seq_prefix (fun n : nat => concat a (f n)) i) =
    concat a (colist.fold empty union (seq_prefix f i)).
Proof.
  revert a f; induction i; simpl; intros a f.
  { rewrite concat_empty_r; reflexivity. }
  rewrite 2!seq_prefix_S_shift.
  simpl; unfold shift.
  rewrite concat_union_distr_l.
  f_equal; apply IHi.
Qed.
  
Lemma star2_unfold {n} (a : lang n) :
  star2 a = union epsilon (concat (star2 a) a).
Proof.
  remember (union epsilon (concat (star2 a) a)) as y.
  unfold star2.
  rewrite big_union_shift.
  simpl; subst.
  f_equal.
  unfold star2.
  unfold big_union.
  apply ext.
  assert (H: concat (sup (union_n empty (pow a))) =
               sup (concat ∘ union_n empty (pow a))).
  { apply ext.
    rewrite continuous_sup with (f := @concat n).
    - reflexivity.
    - apply continuous_co, monotone_tconcat.
    - apply monotone_directed; eauto with cotrie order.
      apply chain_directed, chain_seq_prefix. }
  rewrite H.
  unfold compose.
  rewrite sup_apply.
  apply eq_equ.
  f_equal.
  ext i.
  unfold shift. simpl.
  unfold union_n, list_union.
  clear H.
  apply list_union_concat.
Qed.

Lemma star2'_unfold {n} (a : lang n) :
  star2' a = union epsilon (concat a (star2' a)).
Proof.
  remember (union epsilon (concat a (star2' a))) as y.
  unfold star2'.
  rewrite big_union_shift.
  simpl; subst.
  f_equal.
  unfold star2'.
  unfold big_union.
  apply ext.
  rewrite continuous_sup with (f := concat a).
  2: { apply continuous_concat. }
  2: { apply monotone_directed; eauto with cotrie order.
       apply chain_directed, chain_seq_prefix. }
  unfold compose.
  apply eq_equ.
  f_equal.
  ext i.
  unfold shift. simpl.
  unfold union_n, list_union.
  apply list_union_concat'.
Qed.

Lemma union_epsilon_concat_costar_l {n} (a : lang n) :
  union epsilon (concat (costar a) a) ⊑ costar a.
Proof.
  rewrite costar_star'.
  rewrite star'_star2.
  remember (union epsilon (concat (star2 a) a)) as y.
  rewrite star2_unfold.
  subst; reflexivity.
Qed.

Lemma le_iter_union_concat {n} (a : lang n) (k : nat) :
  a ⊑ iter a (fun x : lang n => union x (concat x a)) k.
Proof.
  revert a; induction k; intro a; simpl.
  { reflexivity. }
  apply cotrie_le_union_l; auto.
Qed.

Lemma cotrie_le_order {n} (a b : lang n) :
  a ⊑ b <-> union a b = b.
Proof.
  split.
  - intro Hle.
    apply cotrie_ext.
    revert Hle; revert a b.
    cofix CH; intros [] [] Hab.
    inv Hab.
    rewrite union_node.
    replace (b || b0) with b0.
    2: { destruct b, b0; simpl; auto. }
    constructor; intro a; apply CH, H4.
  - intros <-.
    apply cotrie_le_union_l; reflexivity.
Qed.

Lemma union_epsilon_concat_costar_r {n} (a : lang n) :
  union epsilon (concat a (costar a)) ⊑ costar a.
Proof.
  rewrite costar_star'.
  rewrite star'_star2.
  rewrite star2_star2'.
  remember (union epsilon (concat a (star2' a))) as y.
  rewrite star2'_unfold.
  subst; reflexivity.
Qed.

Lemma concat_pow'_le {n} (a x : lang n) (i : nat) :
  concat a x ⊑ x ->
  concat (pow' a i) x ⊑ x.
Proof.
  revert a x; induction i; intros a x Hle; simpl.
  { rewrite concat_epsilon_l; reflexivity. }
  etransitivity.
  2: { apply Hle. }
  rewrite concat_assoc.
  apply monotone_concat; try reflexivity.
  apply IHi; auto.
Qed.

Lemma concat_pow_le {n} (a x : lang n) (i : nat) :
  concat x a ⊑ x ->
  concat x (pow a i) ⊑ x.
Proof.
  revert a x; induction i; intros a x Hle; simpl.
  { rewrite concat_epsilon_r; reflexivity. }
  etransitivity.
  2: { apply Hle. }
  rewrite <- concat_assoc.
  apply monotone_concat; try reflexivity.
  apply IHi; auto.
Qed.

Lemma concat_list_union_map_l {n} (x : lang n) (l : list (lang n)) :
  concat (colist.fold empty union l) x =
    colist.fold empty union (map (fun a => concat a x) l).
Proof.
  revert x; induction l; intro x; simpl.
  { apply concat_empty_l. }
  rewrite concat_union_distr_r, IHl; reflexivity.
Qed.

Lemma concat_list_union_map_r {n} (x : lang n) (l : list (lang n)) :
  concat x (colist.fold empty union l) =
    colist.fold empty union (map (fun a => concat x a) l).
Proof.
  revert x; induction l; intro x; simpl.
  { apply concat_empty_r. }
  rewrite concat_union_distr_l, IHl; reflexivity.
Qed.

Lemma concat_costar_l_big_union {n} (a x : lang n) :
  concat (costar a) x = big_union (fun i => concat (pow a i) x).
Proof.
  rewrite costar_star'.
  rewrite star'_star2.
  unfold star2.
  unfold big_union.
  assert (H: concat (sup (union_n empty (pow a))) =
               sup (concat ∘ union_n empty (pow a))).
  { apply ext; apply continuous_sup.
    - apply continuous_co, monotone_tconcat.
    - apply monotone_directed; eauto with cotrie order.
      apply chain_directed, chain_seq_prefix. }
  rewrite H; clear H.
  unfold compose.
  apply ext.
  rewrite sup_apply.
  apply eq_equ.
  f_equal.
  ext i.
  unfold union_n.
  unfold list_union.
  rewrite concat_list_union_map_l.
  rewrite map_seq_prefix; reflexivity.
Qed.

Lemma concat_costar_r_big_union {n} (a x : lang n) :
  concat x (costar a) = big_union (fun i => concat x (pow a i)).
Proof.
  rewrite costar_star'.
  rewrite star'_star2.
  unfold star2.
  unfold big_union.
  apply ext.
  rewrite continuous_sup with (f := concat x).
  2: { apply continuous_concat. }
  2: { apply monotone_directed; eauto with cotrie order.
       apply chain_directed, chain_seq_prefix. }
  apply eq_equ.
  f_equal.
  ext i.
  unfold compose.
  unfold union_n.
  unfold list_union.
  rewrite concat_list_union_map_r.
  rewrite map_seq_prefix; reflexivity.
Qed.

Lemma list_union_lub {n} (x : lang n) (l : list (lang n)) :
  List.Forall (fun a => a ⊑ x) l ->
  list_union empty l ⊑ x.
Proof.
  unfold list_union.
  revert x; induction l; intros x Hall; simpl.
  { apply cotrie_bot_le. }
  inv Hall.
  apply union_le; auto.
Qed.

Lemma big_union_lub {n} (f : nat -> lang n) (x : lang n) :
  (forall i, f i ⊑ x) ->
  big_union f ⊑ x.
Proof.
  intro H; apply ge_sup.
  intro i; apply list_union_lub, forall_seq_prefix; auto.
Qed.

Lemma concat_costar_l {n} (a x : lang n) :
  concat a x ⊑ x ->
  concat (costar a) x ⊑ x.
Proof.
  intro Hle.
  rewrite concat_costar_l_big_union.
  apply big_union_lub.
  intro i; rewrite pow_pow'.
  apply concat_pow'_le; auto.
Qed.

Lemma concat_costar_r {n} (a x : lang n) :
  concat x a ⊑ x ->
  concat x (costar a) ⊑ x.
Proof.
  intro Hle.
  rewrite concat_costar_r_big_union.
  apply big_union_lub.
  intro i; apply concat_pow_le; auto.
Qed.

Lemma coconcat_unfold {n} (a b : lang n) :
  coconcat a b =
    cotrie_node (accepts a && accepts b)
      (fun x => union (coconcat (delta a x) b) (if accepts a then delta b x else empty)).
Proof. destruct a, b; rewrite concat_node; auto. Qed.

Corollary delta_concat {n} (a b : lang n) (x : Fin.t n) :
  delta (concat a b) x = union (concat (delta a x) b)
                           (if accepts a then delta b x else empty).
Proof. rewrite coconcat_unfold; reflexivity. Qed.

Lemma union_epsilon_concat {n} (a b : lang n) :
  union epsilon (concat a b) =
    cotrie_node true (fun x => union (coconcat (delta a x) b)
                         (if accepts a then delta b x else empty)).
Proof.
  rewrite coconcat_unfold.
  rewrite union_comm, union_node.
  simpl.
  rewrite Bool.orb_true_r.
  f_equal.
  ext x.
  unfold const.
  rewrite union_empty_r.
  auto.
Qed.

Lemma union_epsilon_concat_star {n} (a : lang n) :
  union epsilon (concat a (costar a)) =
    cotrie_node true (fun x => union (coconcat (delta a x) (costar a))
                         (if accepts a then delta (costar a) x else empty)).
Proof. apply union_epsilon_concat. Qed.

Lemma union_epsilon_concat_star' {n} (a : lang n) :
  union epsilon (concat a (costar a)) =
    if accepts a then 
      cotrie_node true (fun x => union (coconcat (delta a x) (costar a)) (delta (costar a) x))
    else
      cotrie_node true (fun x => coconcat (delta a x) (costar a)).
Proof.
  rewrite union_epsilon_concat.
  destruct (accepts a); auto.
  f_equal; ext x.
  rewrite union_empty_r; auto.
Qed.

Lemma list_union_map_concat {n} (a : lang n) (l : list (lang n)) :
  colist.fold empty union (map (concat a) l) =
    concat a (colist.fold empty union l).
Proof.
  revert a; induction l; intro x; simpl.
  { rewrite concat_empty_r; reflexivity. }
  rewrite IHl, concat_union_distr_l; reflexivity.
Qed.

Lemma delta_union {n} (a b : lang n) (x : Fin.t n) :
  delta (union a b) x = union (delta a x) (delta b x).
Proof. destruct a, b; reflexivity. Qed.

Lemma delta_union_epsilon {n} (a : lang n) (x : Fin.t n) :
  delta (union epsilon a) x = delta a x.
Proof.
  rewrite delta_union; simpl; unfold const; apply union_empty_l.
Qed.

Lemma list_union_union {n B} (f g : Fin.t n -> lang B) (l : list (Fin.t n)) :
  colist.fold empty union (map (fun x => union (f x) (g x)) l) =
    union (colist.fold empty union (map f l))
      (colist.fold empty union (map g l)).
Proof.
  revert f g; induction l; intros f g; simpl.
  { rewrite union_empty_l; reflexivity. }
  rewrite IHl, 2!union_assoc.
  f_equal; rewrite <- 2!union_assoc, (union_comm (g a)); reflexivity.
Qed.

Lemma list_union_assoc {n} (z a : lang n) (l : list (lang n)) :
  union a (colist.fold z union l) = colist.fold (union z a) union l.
Proof.
  revert z a; induction l; intros z b; simpl.
  { apply union_comm. }
  rewrite <- IHl.
  rewrite <- union_assoc.
  rewrite (union_comm b a).
  rewrite union_assoc; auto.
Qed.

Lemma list_union_list_union' {n} (z : lang n) (l : list (lang n)) :
  colist.fold z union l = foldl union z l.
Proof.
  revert z; induction l; intro z; simpl; auto.
  rewrite <- IHl.
  apply list_union_assoc.
Qed.

Lemma list_union_unfold {n} (f : nat -> lang n) i :
  colist.fold empty union (seq_prefix_aux f (S i)) =
    union (f i) (colist.fold empty union (seq_prefix_aux f i)).
Proof. reflexivity. Qed.

Lemma list_union'_rev {n} (z : lang n) (l : list (lang n)) :
  list_union' z l = list_union' z (rev l).
Proof.
  unfold list_union'.
  revert z; induction l; intro z; simpl; auto.
  rewrite IHl.
  rewrite <- (list_union_list_union' _ (rev l ++ [a])).
  rewrite fold_app.
  rewrite list_union_list_union'.
  simpl.
  rewrite union_comm; reflexivity.
Qed.

Lemma list_union_rev {n} (z : lang n) (l : list (lang n)) :
  colist.fold z union l = colist.fold z union (rev l).
Proof.
  rewrite 2!list_union_list_union'.
  apply list_union'_rev.
Qed.

Lemma list_union_pow_unfold {n} (a : lang n) i :
  colist.fold empty union (seq_prefix (pow' a) (S i)) =
    union (pow' a i) (colist.fold empty union (seq_prefix (pow' a) i)).
Proof.
  unfold seq_prefix.
  rewrite <- list_union_rev.
  rewrite list_union_unfold.
  rewrite list_union_rev; reflexivity.
Qed.

Lemma delta_pow_le_union_concat {n} (a : lang n) x i :
  accepts a = true ->
  delta (pow' a i) x ⊑
    list_union empty (seq_prefix (fun j => concat (delta a x) (pow' a j)) i).
Proof.
  revert a x; induction i; intros a x Ha; simpl.
  { apply cotrie_bot_le. }
  unfold list_union.
  rewrite list_union_concat'.
  rewrite list_union_pow_unfold.
  rewrite delta_concat.
  rewrite Ha.
  rewrite concat_union_distr_l.
  apply union_le.
  - apply cotrie_le_union_l; reflexivity.
  - apply cotrie_le_union_r.
    rewrite <- list_union_concat'.
    apply IHi; auto.
Qed.

Lemma delta_union_delta_concat_union {n} (a : lang n) x i :
  accepts a = true ->
  delta (colist.fold empty union (seq_prefix (pow' a) i)) x
    ⊑ concat (delta a x) (colist.fold empty union (seq_prefix (pow' a) i)).
Proof.
  revert a x; induction i; intros a x Ha; simpl.
  { apply cotrie_bot_le. }
  rewrite list_union_pow_unfold.
  rewrite delta_union.
  rewrite concat_union_distr_l.
  apply union_le.
  - apply cotrie_le_union_r.
    rewrite <- list_union_concat'.
    apply delta_pow_le_union_concat; auto.
  - apply cotrie_le_union_r; apply IHi; auto.
Qed.

Lemma star_star2' {n} (a : lang n) :
  star a = star2' a.
Proof.
  unfold star, star2', coiter, big_union, co, union_n, list_union.
  simpl; unfold compose, flip.
  f_equal.
  ext i.
  rewrite prefix_omega.
  revert a; induction i; intro a; simpl; auto.
  rewrite IHi.
  rewrite seq_prefix_S_shift; simpl.
  clear IHi.
  unfold shift. simpl.
  replace (fun n => concat a (pow' a n)) with (concat a ∘ pow' a) by reflexivity.
  rewrite <- map_seq_prefix.
  rewrite list_union_map_concat.
  rewrite union_epsilon_concat.
  f_equal.
  ext x.
  destruct (accepts a) eqn:Ha.
  - symmetry.
    rewrite union_comm.
    apply cotrie_le_order.
    apply delta_union_delta_concat_union; auto.
  - rewrite union_empty_r; reflexivity.
Qed.

Lemma star_costar {n} (a : lang n) :
  star a = costar a.
Proof.
  rewrite costar_star', star'_star2, star2_star2'; apply star_star2'.
Qed.

(** Kleene algebra laws specialized to star. *)

Theorem union_epsilon_concat_star_l {n} (a : lang n) :
  union epsilon (concat (star a) a) ⊑ star a.
Proof. rewrite star_costar; apply union_epsilon_concat_costar_l. Qed.

Theorem union_epsilon_concat_star_r {n} (a : lang n) :
  union epsilon (concat a (star a)) ⊑ star a.
Proof. rewrite star_costar; apply union_epsilon_concat_costar_r. Qed.

Theorem concat_star_l {n} (a x : lang n) :
  concat a x ⊑ x ->
  concat (star a) x ⊑ x.
Proof. intro Hle; rewrite star_costar; apply concat_costar_l; auto. Qed.

Theorem concat_star_r {n} (a x : lang n) :
  concat x a ⊑ x ->
  concat x (star a) ⊑ x.
Proof. intro Hle; rewrite star_costar; apply concat_costar_r; auto. Qed.

(** The type of cotries with finite alphabet type and Boolean labels
    forms a Kleene algebra. *)

#[global]
  Instance KleeneAlgebra_lang {n} : @KleeneAlgebra (lang n) _ :=
  { plus := union
  ; mult := concat
  ; star := star
  ; zero := empty
  ; one := epsilon
  }.

#[global]
  Instance KleeneAlgebraLaws_lang {n} : @KleeneAlgebraLaws (lang n) _ _.
Proof.
  constructor; intros; unfold plus, mult, star; simpl.
  - rewrite union_assoc; reflexivity.
  - rewrite concat_assoc; reflexivity.
  - rewrite union_comm; reflexivity.
  - rewrite concat_union_distr_l; reflexivity.
  - rewrite concat_union_distr_r; reflexivity.
  - rewrite union_empty_l; reflexivity.
  - rewrite union_empty_r; reflexivity.
  - rewrite concat_empty_l; reflexivity.
  - rewrite concat_empty_r; reflexivity.
  - rewrite concat_epsilon_l; reflexivity.
  - rewrite concat_epsilon_r; reflexivity.
  - rewrite union_idempotent; reflexivity.
  - rewrite union_epsilon_concat_star_r; reflexivity.
  - rewrite union_epsilon_concat_star_l; reflexivity.
  - apply concat_star_l; auto.
  - apply concat_star_r; auto.
Qed.

Print Assumptions KleeneAlgebraLaws_lang.
