(** * Native [comap] through the descriptor-indexed colist presentation. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  List
  Morphisms
.

From algco Require Import
  aCPO
  colist
  cpo
  misc
  order
.

From algco.generic Require Import
  colist_instance
  indexed_container
  indexed_colist_instance
  indexed_fold
  native_colist_presentation
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.

(** The native constructors determine a shape-indexed algebra.  Its fold is
    the common container fold, not a colist-specific copy of the recursion
    and shifted-supremum machinery. *)
Definition colist_fold_algebra {A B : Type}
  (z : B) (step : A -> B -> B) :
  indexed_algebra (colist_pointed_container A) B :=
  fun s =>
    match s as t return (colist_position t -> B) -> B with
    | colist_hole_shape => fun _ => z
    | colist_cons_shape a => fun children => step a (children tt)
    end.

Definition indexed_fold {A B : Type} (z : B) (step : A -> B -> B) :
  indexed_colist_basis A -> B :=
  basis_fold (colist_fold_algebra z step).

(** The generic structural fold computes exactly as the familiar native list
    fold after crossing the one-time presentation boundary. *)
Lemma indexed_fold_native {A B : Type} (z : B) (step : A -> B -> B)
  (b : indexed_colist_basis A) :
  indexed_fold z step b = fold z step (indexed_basis_to_list b).
Proof.
  destruct b as [x].
  unfold indexed_fold, basis_fold, indexed_basis_to_list.
  induction x as [s children IH]; destruct s as [|a]; simpl.
  - reflexivity.
  - specialize (IH tt); simpl in IH; rewrite IH; reflexivity.
Qed.

Lemma monotone_indexed_fold {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) :
  (forall l, z ⊑ fold z step l) ->
  (forall a, Proper (leq ==> leq) (step a)) ->
  Proper (leq ==> leq) (indexed_fold z step).
Proof.
  intros Hz Hstep.
  apply (@monotone_basis_fold (colist_pointed_container A) B _ z
    (colist_fold_algebra z step)).
  - intros children; reflexivity.
  - intro b.
    pose proof (indexed_fold_native z step b) as Hfold.
    unfold indexed_fold in Hfold; rewrite Hfold; apply Hz.
  - intros [|a]; simpl.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; apply Hstep, Hxy.
Qed.

(** The basis computation remains the ordinary structurally recursive list
    map.  Only the one-time specialization conversion mentions the wrapper. *)
Definition indexed_amap {A B : Type} (f : A -> B) :
  indexed_colist_basis A -> colist B :=
  fun b => amap f (indexed_basis_to_list b).

#[global]
Instance monotone_indexed_amap {A B : Type} (f : A -> B) :
  Proper (leq ==> leq) (indexed_amap f).
Proof.
  intros x y Hxy; apply monotone_amap.
  apply presented_monotone_indexed_basis_to_list; exact Hxy.
Qed.

Definition indexed_co_fold {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) : colist A -> B :=
  fun l =>
    value_fold (colist_fold_algebra z step)
      (colist_to_indexed_value l).

(** Continuous extension is taken using the generic [aCPO] instance for the
    indexed input carrier.  The result stays native. *)
Definition indexed_comap_value {A B : Type} (f : A -> B) :
  indexed_colist_value A -> colist B :=
  value_fold
    (colist_fold_algebra (bot : colist B) (map_f f)).

Definition indexed_comap {A B : Type} (f : A -> B) :
  colist A -> colist B :=
  fun l => indexed_comap_value f (colist_to_indexed_value l).

Lemma continuous_indexed_comap_value {A B : Type} (f : A -> B) :
  continuous (indexed_comap_value f).
Proof.
  unfold indexed_comap_value, value_fold.
  apply continuous_co.
  apply monotone_indexed_fold.
  - intro l; apply bot_le.
  - intro a; apply continuous_monotone, continuous_cocons.
Qed.

Lemma continuous_indexed_comap {A B : Type} (f : A -> B) :
  continuous (indexed_comap f).
Proof.
  change
    (continuous
      (compose (indexed_comap_value f) (@colist_to_indexed_value A))).
  apply continuous_compose.
  - apply presented_continuous_colist_to_indexed_value.
  - apply continuous_indexed_comap_value.
Qed.

(** The approximation sequence seen by the basis computation is exactly the
    native prefix sequence. *)
Lemma indexed_amap_ideal {A B : Type} (f : A -> B)
  (l : colist A) (n : nat) :
  indexed_amap f (ideal (colist_to_indexed_value l) n) =
  amap f (prefix n l).
Proof.
  unfold indexed_amap.
  rewrite indexed_basis_to_list_ideal_colist; reflexivity.
Qed.

Lemma directed_indexed_fold_ideal {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) (l : colist A) :
  (forall xs, z ⊑ fold z step xs) ->
  (forall a, Proper (leq ==> leq) (step a)) ->
  directed
    (fun i =>
      indexed_fold z step (ideal (colist_to_indexed_value l) i)).
Proof.
  intros Hz Hstep.
  change (directed
    (compose (indexed_fold z step)
      (ideal (colist_to_indexed_value l)))).
  apply monotone_directed.
  - apply monotone_indexed_fold; assumption.
  - apply chain_directed, chain_ideal.
Qed.

(** Native constructor equations now specialize the single generic container
    layer theorem. *)
Lemma indexed_co_fold_nil {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B) :
  indexed_co_fold z step conil === z.
Proof.
  unfold indexed_co_fold.
  rewrite colist_to_indexed_value_nil.
  apply (@value_fold_bottom
    (colist_pointed_container A) B _ _ _ _ z
    (colist_fold_algebra z step)
    (fun p : Empty_set => match p with end)).
  intros children; reflexivity.
Qed.

Lemma indexed_co_fold_cons {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B) (a : A) (l : colist A) :
  (forall xs, z ⊑ fold z step xs) ->
  (forall x, continuous (step x)) ->
  z ⊑ step a z ->
  indexed_co_fold z step (cocons a l) ===
  step a (indexed_co_fold z step l).
Proof.
  intros Hz Hstep Hza; clear Hza.
  unfold indexed_co_fold.
  rewrite colist_to_indexed_value_cons.
  apply (@value_fold_layer
    (colist_pointed_container A) B _ _ _ _ z
    (colist_fold_algebra z step) (colist_cons_shape a)
    (fun _ : unit => colist_to_indexed_value l)).
  - intros children; reflexivity.
  - intro b.
    pose proof (indexed_fold_native z step b) as Hfold.
    unfold indexed_fold in Hfold; rewrite Hfold; apply Hz.
  - intros [|x]; simpl.
    + apply continuous_wcontinuous, continuous_const.
    + intros ch Hch limit Hsup.
      apply (Hstep x).
      * apply chain_directed; intro i; apply Hch.
      * apply apply_supremum; exact Hsup.
Qed.

Lemma indexed_co_fold_nil' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@CPO B o}
  (z : B) (step : A -> B -> B) :
  indexed_co_fold z step conil = z.
Proof. apply ext, indexed_co_fold_nil. Qed.

Lemma indexed_co_fold_cons' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@CPO B o}
  (z : B) (step : A -> B -> B) (a : A) (l : colist A) :
  (forall xs, z ⊑ fold z step xs) ->
  (forall x, continuous (step x)) ->
  z ⊑ step a z ->
  indexed_co_fold z step (cocons a l) =
  step a (indexed_co_fold z step l).
Proof. intros Hz Hstep Hza; apply ext, indexed_co_fold_cons; auto. Qed.

Definition indexed_cofold {A B : Type} `{PType B}
  (step : A -> B -> B) : colist A -> B :=
  indexed_co_fold ⊥ step.

Lemma indexed_cofold_nil' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@PType B o} `{@CPO B o}
  (step : A -> B -> B) :
  indexed_cofold step conil = ⊥.
Proof. apply indexed_co_fold_nil'. Qed.

Lemma indexed_cofold_cons' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@PType B o} `{@CPO B o}
  (step : A -> B -> B) (a : A) (l : colist A) :
  (forall x, continuous (step x)) ->
  indexed_cofold step (cocons a l) =
  step a (indexed_cofold step l).
Proof.
  intro Hstep; apply indexed_co_fold_cons'.
  - intro xs; apply bot_le.
  - exact Hstep.
  - apply bot_le.
Qed.

(** The operation-level equations now have the same shape as the existing
    [comap] proofs.  Neither appeals to the old implementation. *)
Lemma indexed_comap_nil {A B : Type} (f : A -> B) :
  indexed_comap f conil = conil.
Proof.
  change (indexed_cofold (map_f f) conil = (⊥ : colist B)).
  apply indexed_cofold_nil'.
Qed.

Lemma indexed_comap_cons {A B : Type} (f : A -> B)
  (a : A) (l : colist A) :
  indexed_comap f (cocons a l) =
  cocons (f a) (indexed_comap f l).
Proof.
  change
    (indexed_cofold (map_f f) (cocons a l) =
      cocons (f a) (indexed_cofold (map_f f) l)).
  apply (indexed_cofold_cons' (map_f f) a l).
  intro x; apply continuous_cocons.
Qed.

(** The generic extension agrees exactly with its basis computation. *)
Lemma indexed_comap_value_incl {A B : Type} (f : A -> B)
  (b : indexed_colist_basis A) :
  indexed_comap_value f (incl b) = indexed_amap f b.
Proof.
  unfold indexed_comap_value, value_fold.
  transitivity
    (indexed_fold (bot : colist B) (map_f f) b).
  - apply co_incl'_ext.
    apply monotone_indexed_fold.
    + intro l; apply bot_le.
    + intro a; apply continuous_monotone, continuous_cocons.
  - rewrite indexed_fold_native; reflexivity.
Qed.

Lemma amap_inj_map {A B : Type} (f : A -> B) (l : list A) :
  amap f l = inj (List.map f l).
Proof.
  unfold amap, map_f.
  induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Corollary indexed_comap_value_incl_list {A B : Type}
  (f : A -> B) (l : list A) :
  indexed_comap_value f (incl (list_to_indexed_basis l)) =
  inj (List.map f l).
Proof.
  rewrite indexed_comap_value_incl.
  unfold indexed_amap.
  rewrite indexed_basis_to_list_to_basis.
  apply amap_inj_map.
Qed.

(** Public finite computation follows from the direct constructor equations. *)
Corollary indexed_comap_inj {A B : Type} (f : A -> B) (l : list A) :
  indexed_comap f (inj l) = inj (List.map f l).
Proof.
  induction l as [|a l IH]; simpl.
  - apply indexed_comap_nil.
  - rewrite indexed_comap_cons, IH; reflexivity.
Qed.

(** The old implementation is used only as a regression oracle after the new
    computation laws have been established independently. *)
Theorem indexed_comap_eq_comap {A B : Type} (f : A -> B)
  (l : colist A) :
  indexed_comap f l = comap f l.
Proof.
  apply colist_ext; revert l; cofix CH; intros [|a l].
  - rewrite indexed_comap_nil, comap_nil; constructor.
  - rewrite indexed_comap_cons, comap_cons; constructor; apply CH.
Qed.
