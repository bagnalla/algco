(** * Product algebraic CPO. *)

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

Create HintDb prod.

#[global]
  Instance Compact_prod {A B} `{Compact A} `{Compact B} : Compact (A * B).
Proof.
  constructor.
  intros [a b] f Hf Hsup.
  destruct H0.
  assert (Hsupa: supremum a (fst ∘ f)).
  { eapply supremum_fst; eauto. }
  specialize (compact_spec a (fst ∘ f) (directed_fst _ Hf) Hsupa).
  destruct compact_spec as [n Hn].
  destruct H2.
  assert (Hsupb: supremum b (snd ∘ f)).
  { eapply supremum_snd; eauto. }
  specialize (compact_spec b (snd ∘ f) (directed_snd _ Hf) Hsupb).
  destruct compact_spec as [m Hm].
  unfold compose in *.
  unfold directed in Hf.
  specialize (Hf n m).
  destruct Hf as [k [Hk Hk']].
  exists k.
  destruct (f n) eqn:Hfn.
  destruct (f m) eqn:Hfm.
  simpl in *.
  destruct (f k) eqn:Hfk.
  destruct Hk, Hk'; simpl in *.
  f_equal.
  - split; split; simpl; eauto.
    + destruct Hsupa as [Hub Hlub].
      specialize (Hub k).
      simpl in Hub.
      rewrite Hfk in Hub; auto.
    + destruct Hsupb as [Hub Hlub].
      specialize (Hub k).
      simpl in Hub.
      rewrite Hfk in Hub; auto.
    + rewrite <- Hn; auto.
    + rewrite <- Hm; auto.
Qed.

Definition prod_incl {A bA B bB} (inclA : bA -> A) (inclB : bB -> B) (x : bA * bB) : A * B :=
  (inclA (fst x), inclB (snd x)).

Definition prod_ideal {A bA B bB} (idealA : A -> nat -> bA) (idealB : B -> nat -> bB)
  (x : A * B) (i : nat) : bA * bB :=
  (idealA (fst x) i, idealB (snd x) i).

#[global]
 Instance Dense_prod {A bA B bB} `{Dense A bA} `{Dense B bB} : Dense (A * B) (bA * bB) :=
  { incl := prod_incl incl incl
  ; ideal := prod_ideal ideal ideal }.

#[global]
  Instance aCPO_prod {A bA B bB} `{aCPO A bA} `{aCPO B bB} : aCPO (A * B) (bA * bB).
Proof.
  constructor.
  - intros [a b] [a' b']; split.
    + intros [Ha Hb]; split; apply monotone_incl; auto.
    + intros [Ha Hb]; split; apply incl_order; auto.
  - intros [a b] i; split; apply chain_ideal.
  - intros [a b] [a' b'] [Ha Hb]; split; apply monotone_ideal; auto.
  - intros i f Hf [a b] Hsup; simpl.
    unfold flip, prod_ideal; simpl.
    apply supremum_prod; unfold compose; simpl.
    + apply continuous_ideal.
      * apply directed_fst; auto.
      * eapply supremum_fst; eauto.
    + apply continuous_ideal.
      * apply directed_snd; auto.
      * eapply supremum_snd; eauto.
  - intros []; apply supremum_prod; apply supremum_ideal.
Qed.

Definition fpair {A B C D} (f : A -> C) (g : B -> D) (ab : A * B) : C * D :=
  (f (fst ab), g (snd ab)).

Lemma antimonotone_fpair {A B C} `{OType A} `{OType B} `{OType C} (f : A -> C) (g : B -> C) :
  antimonotone f ->
  antimonotone g ->
  antimonotone (fpair f g).
Proof.
  unfold fpair.
  intros Hf Hg [a b] [a' b'] [Ha Hb]; split; simpl in *.
  - apply Hf; auto.
  - apply Hg; auto.
Qed.

Lemma cocontinuous_fpair {A B C} `{OType A} `{OType B} `{OType C} (f : A -> C) (g : B -> C) :
  cocontinuous f ->
  cocontinuous g ->
  cocontinuous (fpair f g).
Proof.
  unfold fpair.
  intros Hf Hg ch Hch [a b] Hsup; simpl.
  apply infimum_prod; unfold compose; simpl.
  - apply Hf.
    + apply directed_fst; auto.
    + eapply supremum_fst; eauto.
  - apply Hg.
    + apply directed_snd; auto.
    + eapply supremum_snd; eauto.
Qed.

Definition cooppair {A bA B bB C D} `{aCPO A bA} `{aCPO B bB} `{lCPO C} `{lCPO D}
  (f : bA -> C) (g : bB -> D) : A * B -> C * D :=
  coop (fpair f g).

Definition conj' (PQ : Prop * Prop) : Prop :=
  fst PQ /\ snd PQ.

Lemma monotone_conj' :
  monotone conj'.
Proof. intros [P Q] [P' Q'] [H0 H1] [HP HQ]; split; auto. Qed.

Lemma dec_continuous_conj' :
  dec_continuous conj'.
Proof.
  unfold conj'.
  intros ch Hch [P Q] Hinf; simpl.
  apply infimum_conj.
  - eapply infimum_fst; eauto.
  - eapply infimum_snd; eauto.
Qed.

(* Definition conj_prop {A B} (P : A -> Prop) (Q : B -> Prop) : A * B -> Prop := *)
(*   conj' ∘ fpair P Q. *)

Lemma antimonotone_conj_fpair {A B} `{OType A} `{OType B} (P : A -> Prop) (Q : B -> Prop) :
  antimonotone P ->
  antimonotone Q ->
  antimonotone (conj' ∘ fpair P Q).
Proof.
  intros HP HQ.
  apply antimonotone_monotone_compose.
  - apply antimonotone_fpair; auto.
  - apply monotone_conj'.
Qed.

Section prod.
  Context {A bA B bB} `{aCPO A bA} `{aCPO B bB}.
  
  Definition coopconj (P : bA -> Prop) (Q : bB -> Prop) : A * B -> Prop :=
    coop (conj' ∘ fpair P Q).
  
  Lemma coopconj_spec (P : bA -> Prop) (Q : bB -> Prop) (a : A) (b : B) :
    antimonotone P ->
    antimonotone Q ->
    coopconj P Q (a, b) <-> coop P a /\ coop Q b.
  Proof.
    intros HP HQ.
    split.
    - intro HPQ; split.
      + cointro; auto.
        intro i; coelim HPQ.
        * destruct HPQ as [Ha _]; apply Ha.
        * apply antimonotone_conj_fpair; auto.
      + cointro; auto.
        intro i; coelim HPQ.
        * destruct HPQ as [_ Hb]; apply Hb.
        * apply antimonotone_conj_fpair; auto.
    - intros [Ha Hb].
      cointro.
      { apply antimonotone_conj_fpair; auto. }
      intro i; split; simpl.
      + coelim Ha; eauto.
      + coelim Hb; eauto.
  Qed.
  
  (** Not sure why this hangs without type annotations. *)
  Lemma incl_ideal_prod (a : A) (b : B) (i : nat) :
    (@incl A bA _ _ _ (@ideal A bA _ _ _ a i), @incl B bB _ _ _ (@ideal B bB _ _ _ b i)) =
      @incl (A*B) (bA*bB) _ _ _ (@ideal (A*B) (bA*bB) _ _ _ (a, b) i).
  Proof. reflexivity. Qed.

  Theorem co_unique_cocontinuous_R {C} `{CPO C}
    (P : A * B -> Prop) (f : A -> C) (g : basis B -> C) (a : A) (b : B) :
    cocontinuous P ->
    continuous f ->
    monotone g ->
    P (a, b) ->
    ((forall i, P (incl (ideal a i), incl (ideal b i))) ->
     forall i, f (incl (ideal a i)) === g (ideal b i)) ->
    f a === co g b.
  Proof.
    unfold basis in *; intros HP Hf Hg HPa Hgf.
    symmetry.
    apply supremum_sup.
    split.
    - intro i; unfold compose.
      rewrite <- Hgf.
      2: { intro j; rewrite incl_ideal_prod.
           apply cocontinuous_incl_ideal; auto. }
      apply continuous_monotone; auto.
      apply incl_ideal_le.
    - intros c Hc.
      simpl in *.
      destruct H as [? ? ? ? Hsup].
      pose proof (Hsup a) as Ha.
      apply Hf in Ha.
      2: { apply directed_f_ideal; auto.
           apply monotone_incl. }
      destruct Ha as [Hub Hlub].
      apply Hlub.
      intro i; unfold compose.
      unfold compose in *.
      rewrite Hgf.
      2: { intro j; rewrite incl_ideal_prod.
           apply cocontinuous_incl_ideal; auto. }
      eauto.
  Qed.

  Corollary Proper_co_P {C} `{CPO C}
    (f : basis A -> C) (g : basis B -> C) (P : basis A * basis B -> Prop) (a : A) (b : B) :
    antimonotone P ->
    monotone f ->
    monotone g ->
    (forall a' b', P (a', b') -> f a' === g b') ->
    coop P (a, b) ->
    co f a === co g b.
  Proof.
    intros HP Hf Hg Hfg HPa.
    apply co_unique_cocontinuous_R with (P := coop P); eauto with aCPO order.
    intros Hi i.
    rewrite co_incl'; auto.
    apply Hfg.
    eapply coop_elim in HPa; auto; apply HPa.
  Qed.

  Corollary Proper_co_P_ext {C} `{o : OType C} `{@CPO _ o} `{@ExtType _ o}
    (f : basis A -> C) (g : basis B -> C) (P : basis A * basis B -> Prop) (a : A) (b : B) :
    antimonotone P ->
    monotone f ->
    monotone g ->
    (forall a' b', P (a', b') -> f a' = g b') ->
    coop P (a, b) ->
    co f a = co g b.
  Proof.
    intros HP Hf Hg Hfg HPa.
    apply ext; eapply Proper_co_P; eauto.
    intros x y Hxy; erewrite Hfg; eauto; reflexivity.
  Qed.

  Theorem co_unique_general {C} `{CPO C} (f : A -> C) (g : basis B -> C) (a : A) (b : B) :
    continuous f ->
    monotone g ->
    (forall i, f (incl (ideal a i)) === g (ideal b i)) ->
    f a === co g b.
  Proof.
    unfold basis, compose in *; intros Hf Hg Hfg.
    symmetry.
    apply supremum_sup.
    split.
    - intro i; unfold compose.
      rewrite <- Hfg.
      apply continuous_monotone; auto.
      apply incl_ideal_le.
    - intros c Hc.
      destruct H as [? ? ? ? Hsup].
      pose proof (Hsup a) as Ha.
      apply Hf in Ha.
      2: { apply directed_f_ideal; auto.
           apply monotone_incl. }
      destruct Ha as [Hub Hlub].
      apply Hlub.
      intro i; unfold compose.
      etransitivity.
      2: { apply Hc. }
      rewrite Hfg.
      unfold compose.
      reflexivity.
  Qed.

  Corollary Proper_co_general {C} `{CPO C}
    (f : basis A -> C) (g : basis B -> C) (a : A) (b : B) :
    monotone f ->
    monotone g ->
    (forall i, f (ideal a i) === g (ideal b i)) ->
    co f a === co g b.
  Proof.
    intros Hf Hg Hfg.
    apply co_unique_general; auto with aCPO.
    intro i.
    rewrite <- Hfg.
    rewrite co_incl'; auto; reflexivity.
  Qed.

  Corollary Proper_co_general_ext {C} `{o : OType C} `{@CPO _ o} `{@ExtType _ o}
    (f : basis A -> C) (g : basis B -> C) (a : A) (b : B) :
    monotone f ->
    monotone g ->
    (forall i, f (ideal a i) = g (ideal b i)) ->
    co f a = co g b.
  Proof.
    intros Hf Hg Hfg.
    apply ext; eapply Proper_co_general; auto.
    intro i; rewrite Hfg; reflexivity.
  Qed.
End prod.
