(** * Equidistribution theorems for cotrees, itrees, CF trees, and cpGCL. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Streams
  Basics
  List
  Morphisms
  Equality
  Lia
.

Import ListNotations.
Local Open Scope program_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

From algco Require Import
  aCPO
  axioms
  cocwp
  cocwp_facts
  cotree
  cpo
  misc
  mu
  order
  eR
  tactics
.

Local Open Scope eR_scope.

Definition Sigma01 : Type := cotree bool (list bool).

Definition measure (U : Sigma01) : eR :=
  mu (fun bs => 1 / 2 ^ length bs) U.

Fixpoint count {A} (P : A -> Prop) (l : list A) : nat :=
  match l with
  | [] => O
  | x :: xs => if classicT (P x) then S (count P xs) else count P xs
  end.

Inductive is_stream_prefix {A} : list A -> Stream A -> Prop :=
| is_stream_prefix_nil : forall s, is_stream_prefix [] s
| is_stream_prefix_cons : forall x l s,
    is_stream_prefix l s ->
    is_stream_prefix (x :: l) (Cons x s).

Definition freq {A} (P : A -> Prop) (l : list A) :=
  INeR (count P l) / INeR (length l).

Definition in_Sigma01 (U : Sigma01) (s : Stream bool) : Prop :=
  cotree_some (fun l => is_stream_prefix l s) U.

Definition uniform (bitstreams : nat -> Stream bool) : Prop :=
  forall U : Sigma01,
    cotree_disjoint U ->
    converges (freq (in_Sigma01 U) ∘ prefix bitstreams) (measure U).

Inductive produces {A} (P : A -> Prop) : Stream bool -> cotree bool A -> Prop :=
| produces_leaf : forall bs x, P x -> produces P bs (coleaf x)
| produces_node : forall b bs k,
    produces P bs (k b) ->
    produces P (Cons b bs) (conode k).

Lemma list_rel_count {A B} (P : A -> Prop) (Q : B -> Prop) (l1 : list A) (l2 : list B) :
  list_rel (fun x y => P x <-> Q y) l1 l2 ->
  count P l1 = count Q l2.
Proof.
  induction 1; simpl; auto.
  repeat destruct_classic; auto.
  - apply H in p; congruence.
  - apply H in q; congruence.
Qed.

Lemma produces_in_sigma01 {A} (x : A) (bs : Stream bool) (P : A -> bool) (t : cotree bool A) :
  produces (eq x) bs t ->
  in_Sigma01 (cotree_preimage P t) bs <-> is_true (P x).
Proof.
  unfold in_Sigma01.
  induction 1; subst.
  - rewrite cotree_preimage_leaf.
    split.
    + intro Hsome.
      destruct (P x0); auto.
      apply co_elim in Hsome; eauto with cotree order.
      destruct Hsome as [i Hsome].
      destruct i; inv Hsome.
    + unfold is_true; intro HP.
      destruct (P x0); try congruence.
      apply co_intro with (S O); eauto with cotree order.
      constructor; constructor.
  - rewrite cotree_preimage_node; split.
    + intro Hsome.
      apply co_elim in Hsome; eauto with cotree order.
      destruct Hsome as [i Hsome].
      apply IHproduces.
      apply atree_some_exists in Hsome.
      destruct Hsome as [l [H1 H2]].
      apply atree_some_exists in H1.
      destruct H1 as [l' [Hsome Hl]]; subst.
      inv H2.
      { destruct i; simpl in Hsome.
        - inv Hsome.
        - inv Hsome.
          unfold compose in H1. simpl in H1.
          rewrite tprefix_map in H1.
          apply atree_some_map in H1.
          unfold compose in H1.
          apply atree_some_exists in H1.
          destruct H1 as [l [H1 Heq]].
          inv Heq. }
      destruct i.
      { inv Hsome. }
      { simpl in Hsome; unfold flip in Hsome; simpl in Hsome.
        unfold compose in Hsome.
        inv Hsome.
        rewrite tprefix_map in H1.
        apply atree_some_map in H1.
        unfold compose in H1.
        apply atree_some_exists in H1.
        destruct H1 as [l' [Hsome Hl']].
        inv Hl'.
        eapply co_intro; eauto with cotree order.
        apply atree_some_exists; exists l'; split; eauto.
        apply Hsome. }
    + unfold is_true; intro HPx.
      unfold cotree_some.
      apply IHproduces in HPx.
      apply co_elim in HPx; eauto with cotree order.
      destruct HPx as [i Hi].
      apply co_intro with (S i); eauto with cotree order.
      simpl; unfold flip; simpl.
      econstructor.
      unfold compose.
      rewrite tprefix_map.
      apply atree_map_some.
      unfold compose.
      eapply atree_some_impl; try apply Hi.
      intros l Hl; constructor; auto.
Qed.

Record SamplingEnvironment : Type :=
  mkSampleEnvironment
    { bitstreams : nat -> Stream bool
    ; bitstreams_uniform : uniform bitstreams }.

(** Cotree sampling theorem. *)
Section cotree_equidistribution.
  Context (env : SamplingEnvironment) (A : Type) (t : cotree bool A) (P : A -> bool).

  Variable samples : nat -> A.
  Hypothesis bitstreams_samples : forall i, produces (eq (samples i)) (env.(bitstreams) i) t.

  Lemma cotree_freq_bitstreams_samples (n : nat) :
    freq (in_Sigma01 (cotree_preimage P t)) (prefix env.(bitstreams) n) =
      freq (fun x : A => is_true (P x)) (prefix samples n).
  Proof.
    unfold freq; f_equal.
    2: { f_equal; rewrite 2!length_prefix; reflexivity. }
    f_equal; apply list_rel_count, list_rel_prefix.
    intro i; specialize (@bitstreams_samples i).
    apply produces_in_sigma01; auto.
  Qed.

  Theorem cotree_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cotwp (fun s => if P s then 1 else 0) t).
  Proof.
    intros eps Heps.
    pose proof env.(bitstreams_uniform) as Huniform.
    specialize (Huniform _ (disjoint_cotree_preimage P t) _ Heps).
    destruct Huniform as [n0 Huniform].
    exists n0; intros n Hn; specialize (Huniform n Hn).
    unfold compose in *.
    rewrite cotwp_mu_preimage'.
    unfold measure in Huniform.
    rewrite <- cotree_freq_bitstreams_samples; apply Huniform.
  Qed.
End cotree_equidistribution.

Print Assumptions cotree_samples_equidistributed.
