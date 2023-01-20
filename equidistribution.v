(** * Equidistribution theorems for cotrees, itrees, CF trees, and cpGCL. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
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
  colist
  cotree
  cpo
  misc
  mu
  order
  prod
  eR
  (* set *)
  tactics
.

Local Open Scope eR_scope.
Local Open Scope order_scope.
(* Local Open Scope set_scope. *)

Inductive is_stream_prefix {A} : list A -> colist A -> Prop :=
| is_stream_prefix_nil : forall s, is_stream_prefix [] s
| is_stream_prefix_cons : forall x l s,
    is_stream_prefix l s ->
    is_stream_prefix (x :: l) (cocons x s).

Lemma is_stream_prefix_consistent_pair {A} (a b : list A) (l : colist A) :
  is_stream_prefix a l ->
  is_stream_prefix b l ->
  list_le a b \/ list_le b a.
Proof.
  revert b l; induction a; simpl; intros b l Ha Hb.
  { left; constructor. }
  inv Ha; inv Hb.
  { right; constructor. }
  eapply IHa in H1; eauto.
  destruct H1 as [H|H].
  - left; constructor; auto.
  - right; constructor; auto.
Qed.

(* Definition bitstring_set (l : list bool) : set (colist bool) := *)
(*   is_stream_prefix l. *)

(* #[global] *)
(*   Instance ToSet_bitstring : ToSet (list bool) (colist bool) := *)
(*   { to_set := bitstring_set }. *)

Definition bitstring_measure (l : list bool) : eR :=
  1 / 2 ^ length l.

Lemma list_le_stream_prefix_trans {A} (a b : list A) (c : colist A) :
  list_le a b ->
  is_stream_prefix b c ->
  is_stream_prefix a c.
Proof.
  revert b c; induction a; intros b c Hab Hbc.
  { constructor. }
  inv Hab; inv Hbc.
  constructor; eapply IHa; eauto.
Qed.

Lemma is_stream_prefix_inj {A} (l : list A) :
  is_stream_prefix l (inj l).
Proof. induction l; constructor; auto. Qed.
                       
(* Lemma bitstring_incomparable_disjoint (a b : list bool) : *)
(*   incomparable a b <-> partition [[ a ]] [[ b ]]. *)
(* Proof. *)
(*   unfold incomparable, disjoint, to_set; simpl. *)
(*   unfold bitstring_set. *)
(*   split. *)
(*   - intros Hinc l. *)
(*     contra HC; apply Hinc. *)
(*     apply Classical_Prop.not_or_and in HC. *)
(*     destruct HC as [H0 H1]. *)
(*     apply Classical_Prop.NNPP in H0. *)
(*     apply Classical_Prop.NNPP in H1. *)
(*     eapply is_stream_prefix_consistent_pair; eauto. *)
(*   - intros H [HC|HC]. *)
(*     + specialize (H (inj b)). *)
(*       destruct H as [H|H]. *)
(*       * apply H. *)
(*         eapply list_le_stream_prefix_trans; eauto. *)
(*         apply is_stream_prefix_inj. *)
(*       * apply H, is_stream_prefix_inj. *)
(*     + specialize (H (inj a)). *)
(*       destruct H as [H|H]. *)
(*       * apply H, is_stream_prefix_inj. *)
(*       * apply H. *)
(*         eapply list_le_stream_prefix_trans; eauto. *)
(*         apply is_stream_prefix_inj. *)
(* Qed. *)

(* Lemma bitstream_ext a b : *)
(*   [[ a ]] = [[ b ]] -> *)
(*   a = b. *)
(* Proof. *)
(*   simpl; unfold bitstring_set. *)
(*   intro Hab. *)
(*   apply eq_set_eq in Hab. *)
(*   unfold set_eq in Hab. *)
(*   revert Hab; revert b; induction a; intros b Hab. *)
(*   - specialize (Hab conil). *)
(*     destruct Hab as [H0 H1]. *)
(*     specialize (H0 is_stream_prefix_nil). *)
(*     inv H0; auto. *)
(*   - destruct b. *)
(*     { specialize (Hab conil). *)
(*       destruct Hab as [H0 H1]. *)
(*       specialize (H1 is_stream_prefix_nil). *)
(*       inv H1. } *)
(*     pose proof Hab as Hab'. *)
(*     specialize (Hab (cocons a (inj a0))). *)
(*     destruct Hab as [H0 H1]. *)
(*     assert (H: is_stream_prefix (a :: a0) (cocons a (inj a0))). *)
(*     { constructor; apply is_stream_prefix_inj. } *)
(*     apply H0 in H; clear H0. *)
(*     inv H; f_equal. *)
(*     apply IHa. *)
(*     intro l; specialize (Hab' (cocons a l)); destruct Hab' as [H0 H1']. *)
(*     split; intro H. *)
(*     + specialize (H0 (is_stream_prefix_cons H)); inv H0; auto. *)
(*     + specialize (H1' (is_stream_prefix_cons H)); inv H1'; auto. *)
(* Qed. *)

(* Lemma bitstream_measure_proper a b : *)
(*   [[ a ]] = [[ b ]] -> *)
(*   bitstring_measure a = bitstring_measure b. *)
(* Proof. intro Hab; apply bitstream_ext in Hab; subst; reflexivity. Qed. *)

(* #[global] *)
(*   Program *)
(*   Instance Measurable_bitstring : Measurable (list bool) (colist bool) := *)
(*   { mu := bitstring_measure }. *)
(* Next Obligation. apply bitstream_measure_proper; auto. Qed. *)

Definition Sigma01 : Type := cotree bool (list bool).

(* Definition measure {A T} `{Measurable A T} (U : cotree bool A) : eR := *)
(*   tcosum mu U. *)

(* Lemma coset_le_cotree_all_some (a b : Sigma01) : *)
(*   [[ a ]] ⊑ [[ b ]] -> *)
(*   cotree_all (fun x => cotree_some (fun y => y ⊑ x) b) a. *)
(* Proof. *)
(* Admitted. *)

(* Lemma kdfg {A} (t : cotree bool A) : *)
(*   cotree_all (fun x => cotree_some (eq x) cobot) t -> *)
(*   t = cobot. *)
(* Proof with eauto with cotree order. *)
(*   intro Hall. *)
(*   destruct t; auto; apply coop_elim with (i := S (S O)) in Hall... *)
(*   - unfold atree_all in Hall. simpl in Hall. *)
(*     apply cotree_some_bot in Hall; contradiction. *)
(*   - unfold atree_all in Hall. simpl in Hall. *)
(*     unfold compose in Hall. *)
(*     simpl in Hall. *)

(** IDEA: define stream of all bitstreams, then general construction
    of Sigma01 stream of cotree by filtering out elements of the
    stream not in the cotree. Prove their elements coincide and both
    are partitionings, and that those together imply their measures
    are equal. *)

(* #[global] *)
(*   Program *)
(*   Instance Measurable_Sigma01 : Measurable Sigma01 (colist bool) := *)
(*   { mu := measure }. *)
(* Next Obligation. *)
(*   apply eq_set_eq in H. *)
(*   unfold set_eq in H. *)
(*   unfold bitstring_set in H. *)

(*   apply Proper_co_general_ext; eauto with mu order. *)
(*   intro i. *)
(*   simpl; unfold flip. *)
(*   revert Hab Hba; induction i; intros Hab Hba; simpl. *)
(*   { reflexivity. } *)
(*   destruct a. *)
(*   - destruct b; auto. *)
(*     + apply cotree_all_elim_leaf in Hba. *)
(*       apply cotree_some_bot in Hba; contradiction. *)
(*     + unfold asum. simpl. *)
(*       unfold compose in *. *)
      
(*       eapply IHi in Hba; auto. *)
(*       destruct i. *)
(*       { eRauto. } *)
(*       simpl in *. *)

(*       pose proof Hba as Hba'. *)
(*       apply cotree_all_elim_node with (b:=true) in Hba. *)
(*       apply cotree_all_elim_node with (b:=false) in Hba'. *)
  


(* Qed. *)


(** TODO: generalize to class of measurable types (ToSet with
    measure). *)
(* Definition measure (U : Sigma01) : eR := *)
(*   mu (fun bs => 1 / 2 ^ length bs) U. *)
(* #[global] Hint Unfold measure : mu. *)

(* Lemma dfgdfg (U V : Sigma01) : *)
(*   [[ U ]] = [[ V ]] -> *)
(*   measure U = measure V. *)

Definition cotree_union {A} (U V : cotree bool A) : cotree bool A :=
  conode (fun b : bool => if b then U else V).

Lemma Sigma01_union_pairwise_disjoint (U V : Sigma01) :
  cotree_pairwise_disjoint U ->
  cotree_pairwise_disjoint V ->
  cotree_disjoint U V ->
  cotree_pairwise_disjoint (cotree_union U V).
Proof with eauto with cotree order.
  intros HU HV [HVU HUV].
  apply coop_intro...
  intro i; simpl; unfold flip.
  unfold cotree_union.
  destruct i.
  { constructor. }
  apply coop_elim with (i:=i) in HU...
  apply coop_elim with (i:=i) in HV...
  apply coop_elim with (i:=i) in HVU...
  apply coop_elim with (i:=i) in HUV...
  simpl in *; unfold flip in *.
  constructor.
  - intros []; auto.
  - split; eapply atree_all_impl; eauto; simpl;
      intros bs Hbs; apply coop_elim with (i:=i) in Hbs...
Qed.

Definition alist_union {A} : list (cotree bool A) -> cotree bool A :=
  fold ⊥ cotree_union.

#[global]
  Instance monotone_alist_union {A}
  : Proper (leq ==> leq) (@alist_union A).
Proof.
  unfold alist_union.
  intro a; induction a; intros b Hab; unfold flip; simpl.
  { constructor. }
  unfold cotree_union.
  inv Hab; simpl.
  constructor; intros [].
  - reflexivity.
  - apply IHa; auto.
Qed.
#[global] Hint Resolve monotone_alist_union : colist.

Definition colist_union {A} : colist (cotree bool A) -> cotree bool A :=
  co alist_union.
  
Inductive alist_pairwise_disjoint {A} `{OType A} : list (cotree bool A) -> Prop :=
| alist_pairwise_disjoint_nil : alist_pairwise_disjoint []
| alist_pairwise_disjoint_cons : forall t l,
    (* cotree_pairwise_disjoint t -> *)
    alist_pairwise_disjoint l ->
    list_forall (cotree_disjoint t) l ->
    alist_pairwise_disjoint (t :: l).

#[global]
  Instance antimonotone_alist_pairwise_disjoint {A} `{OType A}
  : Proper (leq ==> flip leq) (@alist_pairwise_disjoint A _).
Proof.
  intro a; induction a; intros b Hab Hb.
  { constructor. }
  inv Hab; inv Hb.
  constructor; auto.
  - eapply IHa; eauto.
  - eapply antimonotone_list_forall; eauto.
Qed.
#[global] Hint Resolve antimonotone_alist_pairwise_disjoint : colist.

Definition colist_pairwise_disjoint {A} `{OType A} : colist (cotree bool A) -> Prop :=
  coop alist_pairwise_disjoint.

Lemma continuous_pair_plus :
  wcontinuous (fun f : bool -> eR => f false + f true).
Proof.
  intros ch Hch f Hsup; unfold compose.
  apply supremum_sum.
  { intro i; apply Hch. }
  { intro i; apply Hch. }
  { apply apply_supremum; auto. }
  { apply apply_supremum; auto. }
Qed.

(* Lemma countable_additivity (l : colist Sigma01) : *)
(*   measure (colist_union l) = cosum (comap measure l). *)
(* Proof with eauto with order colist cotree aCPO mu eR. *)
(*   unfold colist_union. *)
(*   rewrite co_co_ext... *)
(*   2: { apply continuous_wcontinuous, continuous_co, monotone_asum. } *)
(*   unfold comap, cofold. *)
(*   rewrite co_co_ext with (g := cosum)... *)
(*   2: { apply continuous_wcontinuous, continuous_co... } *)
(*   eapply Proper_co_ext; eauto. *)
(*   { apply monotone_compose. *)
(*     - apply monotone_alist_union. *)
(*     - apply continuous_monotone, continuous_co, monotone_asum. } *)
(*   { apply monotone_compose. *)
(*     - apply monotone_amap. *)
(*     - apply continuous_monotone, continuous_co... } *)
(*   clear l; unfold compose. *)
(*   unfold alist_union. *)
(*   unfold measure, tcosum, asum, cosum, cofold. *)
(*   ext b; induction b; simpl. *)
(*   { rewrite co_tfold_bot', co_fold_nil'; reflexivity. } *)
(*   unfold cotree_union. *)
(*   rewrite co_tfold_node'... *)
(*   2: { apply continuous_pair_plus. } *)
(*   unfold compose. *)
(*   unfold map_f in *. *)
(*   rewrite co_fold_cons'... *)
(*   2: { intro; apply continuous_eRplus. } *)
(*   rewrite eRplus_comm. *)
(*   f_equal; apply IHb. *)
(* Qed. *)

(* Lemma countable_additivity (l : colist Sigma01) : *)
(*   colist_pairwise_disjoint l -> *)
(*   measure (colist_union l) = cosum (comap measure l). *)
(* Proof with eauto with order colist cotree aCPO mu eR. *)
(*   intro Hpart. *)
(*   unfold colist_union. *)
(*   rewrite co_co_ext... *)
(*   2: { apply continuous_wcontinuous, continuous_co... } *)
(*   unfold comap, cofold. *)
(*   rewrite co_co_ext with (g := cosum)... *)
(*   2: { apply continuous_wcontinuous, continuous_co... } *)
(*   eapply Proper_co_P_ext; eauto. *)
(*   { apply antimonotone_alist_pairwise_disjoint. } *)
(*   { apply monotone_compose. *)
(*     - apply monotone_alist_union. *)
(*     - apply continuous_monotone, continuous_co, monotone_amu. } *)
(*   { apply monotone_compose. *)
(*     - apply monotone_amap. *)
(*     - apply continuous_monotone, continuous_co, monotone_asum. } *)
(*   clear l Hpart; unfold compose. *)
(*   unfold alist_union. *)
(*   unfold measure, mu, amu, cosum, cofold. *)
(*   intro b; induction b; simpl; intro Hpart. *)
(*   { rewrite co_tfold_bot', co_fold_nil'; reflexivity. } *)
(*   unfold cotree_union. *)
(*   rewrite co_tfold_node'... *)
(*   2: { apply continuous_pair_plus. } *)
(*   unfold compose. *)
(*   inv Hpart. *)
(*   unfold map_f in *. *)
(*   rewrite co_fold_cons'... *)
(*   2: { intro; apply continuous_eRplus. } *)
(*   apply IHb in H1. *)
(*   rewrite eRplus_comm. *)
(*   f_equal; apply H1. *)
(* Qed. *)

Fixpoint count {A} (P : A -> Prop) (l : list A) : nat :=
  match l with
  | [] => O
  | x :: xs => if classicT (P x) then S (count P xs) else count P xs
  end.

Definition freq {A} (P : A -> Prop) (l : list A) :=
  INeR (count P l) / INeR (length l).

Definition in_Sigma01 (U : Sigma01) (s : colist bool) : Prop :=
  cotree_some (fun l => is_stream_prefix l s) U.

Definition mu (U : Sigma01) : eR :=
  tcosum bitstring_measure U.

Definition uniform (bitstreams : nat -> colist bool) : Prop :=
  forall U : Sigma01,
    cotree_pairwise_disjoint U ->
    converges (freq (in_Sigma01 U) ∘ seq_prefix bitstreams) (mu U).

Inductive produces {A} (P : A -> Prop) : colist bool -> cotree bool A -> Prop :=
| produces_leaf : forall bs x, P x -> produces P bs (coleaf x)
| produces_node : forall b bs k,
    produces P bs (k b) ->
    produces P (cocons b bs) (conode k).

Lemma list_rel_count {A B} (P : A -> Prop) (Q : B -> Prop) (l1 : list A) (l2 : list B) :
  list_rel (fun x y => P x <-> Q y) l1 l2 ->
  count P l1 = count Q l2.
Proof.
  induction 1; simpl; auto.
  repeat destruct_classic; auto.
  - apply H in p; congruence.
  - apply H in q; congruence.
Qed.

Lemma produces_in_sigma01 {A} (x : A) (bs : colist bool) (P : A -> bool) (t : cotree bool A) :
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
      destruct Hsome as [l [H1 H2] ].
      apply atree_some_exists in H1.
      destruct H1 as [l' [Hsome Hl] ]; subst.
      inv H2.
      { destruct i; simpl in Hsome.
        - inv Hsome.
        - destruct Hsome as [c H0].
          unfold compose in H0. simpl in H0.
          rewrite tprefix_map in H0.
          apply atree_some_map in H0.
          unfold compose in H0.
          apply atree_some_exists in H0.
          destruct H0 as [l [H0 Heq] ].
          inv Heq. }
      destruct i.
      { inv Hsome. }
      { simpl in Hsome; unfold flip in Hsome; simpl in Hsome.
        unfold compose in Hsome.
        destruct Hsome as [c H1].
        unfold compose in H1.
        rewrite tprefix_map in H1.
        apply atree_some_map in H1.
        apply atree_some_exists in H1.
        destruct H1 as [l' [Hsome Hl'] ].
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
    { bitstreams : nat -> colist bool
    ; bitstreams_uniform : uniform bitstreams }.

(** Cotree sampling theorem. *)
Section cotree_equidistribution.
  Context (env : SamplingEnvironment) (A : Type) (t : cotree bool A) (P : A -> bool).

  Variable samples : nat -> A.
  Hypothesis bitstreams_samples : forall i, produces (eq (samples i)) (env.(bitstreams) i) t.

  Lemma cotree_freq_bitstreams_samples (n : nat) :
    freq (in_Sigma01 (cotree_preimage P t)) (seq_prefix env.(bitstreams) n) =
      freq (fun x : A => is_true (P x)) (seq_prefix samples n).
  Proof.
    unfold freq; f_equal.
    2: { f_equal; rewrite 2!length_seq_prefix; reflexivity. }
    f_equal; apply list_rel_count, list_rel_prefix.
    intro i; specialize (@bitstreams_samples i).
    apply produces_in_sigma01; auto.
  Qed.

  Theorem cotree_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ seq_prefix samples)
      (cotwp (fun s => if P s then 1 else 0) t).
  Proof.
    intros eps Heps.
    pose proof env.(bitstreams_uniform) as Huniform.
    specialize (Huniform _ (pairwise_disjoint_cotree_preimage P t) _ Heps).
    destruct Huniform as [n0 Huniform].
    exists n0; intros n Hn; specialize (Huniform n Hn).
    unfold compose in *.
    rewrite cotwp_tcosum_preimage'.
    unfold mu in Huniform.
    rewrite <- cotree_freq_bitstreams_samples; apply Huniform.
  Qed.
End cotree_equidistribution.

Print Assumptions cotree_samples_equidistributed.
