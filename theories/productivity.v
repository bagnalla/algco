(** * Observation-indexed totality and productivity. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
.

Local Open Scope program_scope.

From algco Require Import
  aCPO
  colist
  order
  tactics
.

Local Open Scope order_scope.

(** An observation-indexed value is total when it answers every finite
    request.  An approximation chain covers its requests when each request is
    answered at some finite stage. *)
Definition observation_total {Request A : Type}
  (observes : Request -> A -> Prop) (x : A) : Prop :=
  forall request, observes request x.

Definition covers {Request A : Type}
  (observes : Request -> A -> Prop) (approx : nat -> A) : Prop :=
  forall request, exists n, observes request (approx n).

(** A continuous Prop-valued predicate is an upward-closed, omega-Scott-open
    observation in the terminology documented in [order.v]: if it holds at a
    directed supremum, it already holds at one finite stage.  Consequently,
    coverage of a chain is equivalent to observational totality of its
    supremum.  Totality itself is generally an infinite conjunction of such
    observations and need not be Scott-open. *)
Lemma observation_total_supremum_iff_covers
  {Request A : Type} `{OType A}
  (observes : Request -> A -> Prop)
  (Hobserves : forall request, continuous (observes request))
  (approx : nat -> A) (x : A) :
  directed approx ->
  supremum x approx ->
  (observation_total observes x <-> covers observes approx).
Proof.
  intros Hdirected Hsupremum.
  unfold observation_total, covers.
  split; intros Htotal request.
  - specialize (Hobserves request approx Hdirected x Hsupremum).
    apply supremum_Prop' in Hobserves.
    unfold compose in Hobserves.
    apply Hobserves, Htotal.
  - specialize (Hobserves request approx Hdirected x Hsupremum).
    apply supremum_Prop' in Hobserves.
    unfold compose in Hobserves.
    apply Hobserves, Htotal.
Qed.

(** For a continuous function out of an algebraic CPO, the canonical ideal
    chain covers all output observations exactly when the result on the full
    input is observationally total. *)
Lemma observation_total_ideal_iff_covers
  {Request A B C : Type} `{aCPO A B} `{OType C}
  (observes : Request -> C -> Prop)
  (Hobserves : forall request, continuous (observes request))
  (f : A -> C) (x : A) :
  continuous f ->
  (observation_total observes (f x) <->
   covers observes ((f ∘ incl) ∘ ideal x)).
Proof.
  intro Hf.
  apply observation_total_supremum_iff_covers; auto.
  - apply directed_f_ideal.
    intros a b Hab; unfold compose.
    apply continuous_monotone; auto.
    apply monotone_incl; auto.
  - apply Hf.
    + apply directed_f_ideal, monotone_incl.
    + apply supremum_ideal.
Qed.

(** A frontier step is stronger than arbitrary strict growth: it advances the
    next observation depth.  [recurring_frontier] permits a chain either to
    reach a total stage or to take another frontier step arbitrarily far after
    the current stage. *)
Definition recurring_frontier {A : Type}
  (observes : nat -> A -> Prop) (frontier : A -> A -> Prop)
  (approx : nat -> A) : Prop :=
  forall m,
    observation_total observes (approx m) \/
    exists n, (m <= n)%nat /\ frontier (approx n) (approx (S n)).

Lemma recurring_frontier_covers
  {A : Type} `{OType A}
  (observes : nat -> A -> Prop) (frontier : A -> A -> Prop)
  (approx : nat -> A) :
  chain approx ->
  (forall depth, monotone (observes depth)) ->
  (forall x, observes O x) ->
  (forall depth x y,
      observes depth x ->
      frontier x y ->
      observes (S depth) y) ->
  recurring_frontier observes frontier approx ->
  covers observes approx.
Proof.
  intros Hchain Hmonotone Hzero Hadvance Hprogress depth.
  induction depth as [|depth IH].
  - exists O; apply Hzero.
  - destruct IH as [m Hm].
    specialize (Hprogress m).
    destruct Hprogress as [Htotal | [n [Hmn Hfrontier]]].
    + exists m; apply Htotal.
    + exists (S n).
      apply (Hadvance depth (approx n) (approx (S n))).
      * apply (Hmonotone depth (approx m) (approx n)).
        -- apply chain_leq; auto.
        -- exact Hm.
      * exact Hfrontier.
Qed.

Corollary recurring_frontier_total_supremum
  {A : Type} `{OType A}
  (observes : nat -> A -> Prop)
  (Hobserves : forall depth, continuous (observes depth))
  (frontier : A -> A -> Prop) (approx : nat -> A) (x : A) :
  chain approx ->
  supremum x approx ->
  (forall y, observes O y) ->
  (forall depth y z,
      observes depth y ->
      frontier y z ->
      observes (S depth) z) ->
  recurring_frontier observes frontier approx ->
  observation_total observes x.
Proof.
  intros Hchain Hsupremum Hzero Hadvance Hprogress.
  apply (proj2
    (observation_total_supremum_iff_covers
      Hobserves (chain_directed approx Hchain) Hsupremum)).
  eapply recurring_frontier_covers; eauto.
  intro depth; apply continuous_monotone, Hobserves.
Qed.

(** ** Colist observations *)

(** Request [n] asks for the first [n] constructors.  Depth zero is always
    observable; observing one more level requires exposing one more [cocons].
    Since colist elements themselves are not ordered, an exposed constructor
    also has its final payload. *)
Inductive colist_observes {A : Type} : nat -> colist A -> Prop :=
| colist_observes_zero : forall l,
    colist_observes O l
| colist_observes_succ : forall n a l,
    colist_observes n l ->
    colist_observes (S n) (cocons a l).

Lemma nth'_monotone {A : Type} (P : A -> Prop) (n : nat) :
  monotone (@nth' A P n).
Proof.
  intros l1 l2 Hle Hnth.
  revert l2 Hle.
  induction Hnth; intros l2 Hle; inv Hle; constructor; auto.
Qed.

(** A finite colist observation of a directed supremum occurs at a finite
    stage. *)
Lemma nth'_supremum_stage {A : Type} (P : A -> Prop)
  (n : nat) (l : colist A) (approx : nat -> colist A) :
  directed approx ->
  supremum l approx ->
  nth' P n l ->
  exists i, nth' P n (approx i).
Proof.
  intros Hdirected Hsupremum Hnth.
  revert approx Hdirected Hsupremum.
  induction Hnth; intros approx Hdirected Hsupremum.
  - apply supremum_cocons' in Hsupremum.
    destruct Hsupremum as [i [l' [Hi _]]].
    exists i; rewrite Hi; constructor; auto.
  - assert (Hstep_supremum : supremum l (step ∘ approx)).
    { eapply supremum_step_cons; eauto. }
    assert (Hstep_directed : directed (step ∘ approx)).
    { apply directed_step; auto. }
    specialize (IHHnth _ Hstep_directed Hstep_supremum).
    destruct IHHnth as [i Hi].
    exists i; unfold compose in Hi.
    destruct (approx i); simpl in Hi.
    + inv Hi.
    + constructor; auto.
Qed.

Lemma continuous_nth' {A : Type} (P : A -> Prop) (n : nat) :
  continuous (@nth' A P n).
Proof.
  intros approx Hdirected l Hsupremum.
  apply supremum_Prop.
  split.
  - intro Hnth.
    destruct (nth'_supremum_stage Hdirected Hsupremum Hnth) as [i Hi].
    exists i; exact Hi.
  - intros [i Hi].
    unfold compose in Hi.
    destruct Hsupremum as [Hupper _].
    eapply nth'_monotone; eauto.
Qed.

Lemma colist_observes_succ_iff_nth' {A : Type}
  (n : nat) (l : colist A) :
  colist_observes (S n) l <-> nth' (const True) n l.
Proof.
  revert l; induction n; intros l; split; intro Hobserve.
  - inv Hobserve; constructor; apply I.
  - inv Hobserve; constructor; constructor.
  - inv Hobserve; constructor; apply IHn; auto.
  - inv Hobserve; constructor; apply IHn; auto.
Qed.

Lemma colist_observes_monotone {A : Type} (n : nat) :
  monotone (@colist_observes A n).
Proof.
  intros l1 l2 Hle Hobserve.
  revert l2 Hle.
  induction Hobserve; intros l2 Hle.
  - constructor.
  - inv Hle; constructor; auto.
Qed.

Lemma colist_observation_supremum_stage {A : Type}
  (n : nat) (l : colist A) (approx : nat -> colist A) :
  directed approx ->
  supremum l approx ->
  colist_observes n l ->
  exists i, colist_observes n (approx i).
Proof.
  intros Hdirected Hsupremum Hobserve.
  destruct n as [|n].
  - exists O; constructor.
  - apply colist_observes_succ_iff_nth' in Hobserve.
    destruct (nth'_supremum_stage Hdirected Hsupremum Hobserve) as [i Hi].
    exists i; apply colist_observes_succ_iff_nth'; exact Hi.
Qed.

Lemma continuous_colist_observes {A : Type} (n : nat) :
  continuous (@colist_observes A n).
Proof.
  intros approx Hdirected l Hsupremum.
  apply supremum_Prop.
  split.
  - intro Hobserve.
    destruct (colist_observation_supremum_stage
      Hdirected Hsupremum Hobserve) as [i Hi].
    exists i; exact Hi.
  - intros [i Hi].
    unfold compose in Hi.
    destruct Hsupremum as [Hupper _].
    eapply colist_observes_monotone; eauto.
Qed.

Lemma colist_observation_total_iff_productive {A : Type} (l : colist A) :
  observation_total (@colist_observes A) l <-> productive l.
Proof.
  rewrite <- productive'_productive.
  unfold observation_total, productive'.
  split.
  - intros Hobserve n.
    apply colist_observes_succ_iff_nth', Hobserve.
  - intros Hproductive [|n].
    + constructor.
    + apply colist_observes_succ_iff_nth', Hproductive.
Qed.

(** [colist_frontier l l'] means that [l'] replaces the unique hole at the
    end of the finite prefix [l] with one constructor, preserving the prefix
    already exposed by [l]. *)
Inductive colist_frontier {A : Type} : colist A -> colist A -> Prop :=
| colist_frontier_here : forall a l,
    colist_frontier conil (cocons a l)
| colist_frontier_later : forall a l1 l2,
    colist_frontier l1 l2 ->
    colist_frontier (cocons a l1) (cocons a l2).

Lemma colist_frontier_le {A : Type} (l1 l2 : colist A) :
  colist_frontier l1 l2 -> l1 ⊑ l2.
Proof. intro Hfrontier; induction Hfrontier; constructor; auto. Qed.

Lemma colist_frontier_advances {A : Type}
  (n : nat) (l1 l2 : colist A) :
  colist_observes n l1 ->
  colist_frontier l1 l2 ->
  colist_observes (S n) l2.
Proof.
  intros Hobserve Hfrontier.
  revert l2 Hfrontier.
  induction Hobserve; intros l2 Hfrontier.
  - destruct Hfrontier; constructor; constructor.
  - inv Hfrontier; constructor; auto.
Qed.

Corollary colist_recurring_frontier_productive
  {A : Type} (approx : nat -> colist A) (l : colist A) :
  chain approx ->
  supremum l approx ->
  recurring_frontier (@colist_observes A) colist_frontier approx ->
  productive l.
Proof.
  intros Hchain Hsupremum Hprogress.
  apply (proj1 (@colist_observation_total_iff_productive A l)).
  eapply recurring_frontier_total_supremum; eauto.
  - apply continuous_colist_observes.
  - intro x; constructor.
  - apply colist_frontier_advances.
Qed.

Corollary colist_productive_supremum_iff_covers
  {A : Type} (approx : nat -> colist A) (l : colist A) :
  directed approx ->
  supremum l approx ->
  (productive l <-> covers (@colist_observes A) approx).
Proof.
  intros Hdirected Hsupremum.
  rewrite <- colist_observation_total_iff_productive.
  apply observation_total_supremum_iff_covers; auto.
  apply continuous_colist_observes.
Qed.

Corollary colist_productive_ideal_iff_covers
  {A B C : Type} `{aCPO A B}
  (f : A -> colist C) (x : A) :
  continuous f ->
  (productive (f x) <->
   covers (@colist_observes C) ((f ∘ incl) ∘ ideal x)).
Proof.
  intro Hf.
  rewrite <- colist_observation_total_iff_productive.
  apply observation_total_ideal_iff_covers; auto.
  apply continuous_colist_observes.
Qed.
