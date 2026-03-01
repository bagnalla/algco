(** * Sum (coproduct) algebraic CPO. *)

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

From algco Require Import aCPO axioms conat cpo eR misc order tactics.

Local Open Scope order_scope.

Create HintDb sum.

#[global]
  Instance Compact_sum {A B} `{Compact A} `{Compact B} : Compact (A + B).
Proof.
  constructor.
  intros [a | b].
  - intros f Hf Hsup.
    destruct H0.
    set (f' := fun i => match f i with
                     | inl x => x
                     | inr _ => a
                     end).
    assert (Hf': directed f').
    { intros i j; specialize (Hf i j); destruct Hf as [k [Hk Hk']].
      unfold f'.
      exists k.
      destruct (f k).
      2: { assert (f i ⊑ inl a) by apply Hsup.
           destruct (f i).
           - inv Hk.
           - inv H0. }
      destruct (f i).
      2: { inv Hk. }
      destruct (f j).
      2: { inv Hk'. }
      split; auto. }
    specialize (compact_spec a f' Hf' (inl_supremum _ _ Hsup)).
    destruct compact_spec as [i Hi].
    unfold f' in Hi.
    exists i.
    destruct (f i) eqn:Hfi; subst; auto.
    assert (HC: inr b ⊑ inl a).
    { rewrite <- Hfi; apply Hsup. }
    inv HC.
  - intros f Hf Hsup.
    destruct H2.
    set (f' := fun i => match f i with
                     | inl _ => b
                     | inr y => y
                     end).
    assert (Hf': directed f').
    { intros i j; specialize (Hf i j); destruct Hf as [k [Hk Hk']].
      unfold f'.
      exists k.
      destruct (f k).
      { assert (f i ⊑ inr b) by apply Hsup.
        destruct (f i).
        - inv H2.
        - inv Hk. }
      destruct (f i).
      { inv Hk. }
      destruct (f j).
      { inv Hk'. }
      split; auto. }
    specialize (compact_spec b f' Hf' (inr_supremum _ _ Hsup)).
    destruct compact_spec as [i Hi].
    unfold f' in Hi.
    exists i.
    destruct (f i) eqn:Hfi; subst; auto.
    assert (HC: inl a ⊑ inr b).
    { rewrite <- Hfi; apply Hsup. }
    inv HC.
Qed.

Definition sum_incl {A bA B bB} (inclA : bA -> A) (inclB : bB -> B) (x : bA + bB) : A + B :=
  match x with
  | inl a => inl (inclA a)
  | inr b => inr (inclB b)
  end.

Definition sum_ideal {A bA B bB} (idealA : A -> nat -> bA) (idealB : B -> nat -> bB)
  (x : A + B) (i : nat) : bA + bB :=
  match x with
  | inl a => inl (idealA a i)
  | inr b => inr (idealB b i)
  end.

#[global]
 Instance Dense_sum {A bA B bB} `{Dense A bA} `{Dense B bB} : Dense (A + B) (bA + bB) :=
  { incl := sum_incl incl incl
  ; ideal := sum_ideal ideal ideal }.

#[global]
  Instance aCPO_sum {A bA B bB} `{aCPO A bA} `{aCPO B bB} : aCPO (A + B) (bA + bB).
Proof.
  constructor; simpl.
  - intros [a|b] [a'|b']; split; try intros [].
    + destruct H; apply incl_order.
    + destruct H; apply incl_order.
    + destruct H0; apply incl_order.
    + destruct H0; apply incl_order.
  - intros [a|b].
    + destruct H; apply chain_ideal.
    + destruct H0; apply chain_ideal.
  - intros [a|b] [a'|b']; try intros [].
    + destruct H; apply monotone_ideal.
    + destruct H0; apply monotone_ideal.
  - unfold flip; intros i ch Hch [a|b] Hsup; simpl.
    + destruct H.
      specialize (continuous_ideal i).
      simpl in continuous_ideal; unfold flip in continuous_ideal.
      set (ch' := fun i => match ch i with
                       | inl x => x
                       | inr _ => a
                       end).
      assert (Hch': directed ch').
      { intros n m; specialize (Hch n m); destruct Hch as [k [Hk Hk']].
        unfold ch'.
        exists k.
        destruct (ch k).
        2: { assert (ch n ⊑ inl a) by apply Hsup.
             destruct (ch n).
             - inv Hk.
             - inv H. }
        destruct (ch n).
        2: { inv Hk. }
        destruct (ch m).
        2: { inv Hk'. }
        split; auto. }
      specialize (continuous_ideal ch' Hch' a (inl_supremum _ _ Hsup)).
      split.
      * intro j; simpl; unfold compose.
        unfold sum_le.
        destruct (ch j) eqn:Hchj; simpl.
        2: { assert (HC: inr b ⊑ inl a).
             { rewrite <- Hchj; apply Hsup. }
             inv HC. }
        apply monotone_ideal.
        assert (Heq: @inl A B a0 ⊑ inl a).
        { rewrite <- Hchj; apply Hsup. }
        apply Heq.
      * intros [a'|b'] Hub.
        { simpl; unfold sum_le.
          eapply continuous_ideal.
          intro j; unfold compose.
          specialize (Hub j); unfold compose in Hub.
          unfold ch'.
          destruct (ch j) eqn:Hchj.
          2: { assert (HC: inr b ⊑ inl a).
               { rewrite <- Hchj; apply Hsup. }
               inv HC. }
          rewrite <- Hchj in Hub.
          simpl in Hub.
          unfold sum_le in Hub.
          rewrite Hchj in Hub; apply Hub. }
        { unfold compose, sum_ideal in Hub.
          specialize (Hub O); simpl in Hub.
          destruct (ch O) eqn:HchO.
          { destruct Hub. }
          assert (HC: inr b ⊑ inl a).
          { rewrite <- HchO; apply Hsup. }
          inv HC. }
    + destruct H0.
      specialize (continuous_ideal i).
      simpl in continuous_ideal; unfold flip in continuous_ideal.
      set (ch' := fun i => match ch i with
                       | inl _ => b
                       | inr y => y
                       end).
      assert (Hch': directed ch').
      { intros n m; specialize (Hch n m); destruct Hch as [k [Hk Hk']].
        unfold ch'.
        exists k.
        destruct (ch k).
        { assert (ch n ⊑ inr b) by apply Hsup.
          destruct (ch n).
          - inv H0.
          - inv Hk. }
        destruct (ch n).
        { inv Hk. }
        destruct (ch m).
        { inv Hk'. }
        split; auto. }
      specialize (continuous_ideal ch' Hch' b (inr_supremum _ _ Hsup)).
      split.
      * intro j; simpl; unfold compose.
        unfold sum_le.
        destruct (ch j) eqn:Hchj; simpl.
        { assert (HC: inl a ⊑ inr b).
          { rewrite <- Hchj; apply Hsup. }
          inv HC. }
        apply monotone_ideal.
        assert (Heq: @inr A B b0 ⊑ inr b).
        { rewrite <- Hchj; apply Hsup. }
        apply Heq.
      * intros [a'|b'] Hub.
        { unfold compose, sum_ideal in Hub.
          specialize (Hub O); simpl in Hub.
          destruct (ch O) eqn:HchO.
          2: { destruct Hub. }
          assert (HC: inl a ⊑ inr b).
          { rewrite <- HchO; apply Hsup. }
          inv HC. }
        { simpl; unfold sum_le.
          eapply continuous_ideal.
          intro j; unfold compose.
          specialize (Hub j); unfold compose in Hub.
          unfold ch'.
          destruct (ch j) eqn:Hchj.
          { assert (HC: inl a ⊑ inr b).
            { rewrite <- Hchj; apply Hsup. }
            inv HC. }
          rewrite <- Hchj in Hub.
          simpl in Hub.
          unfold sum_le in Hub.
          rewrite Hchj in Hub; apply Hub. }
  - intros [a|b].
    + apply supremum_inl.
      destruct H; eauto.
    + apply supremum_inr.
      destruct H0; eauto.
Qed.
