(** * Native [cotree_map] through the descriptor-indexed presentation. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  FunctionalExtensionality
  Morphisms
.

From algco Require Import
  aCPO
  cotree
  cpo
  misc
  order
.

From algco.generic Require Import
  cotree_instance
  indexed_container
  indexed_cotree_instance
  indexed_fold
  native_cotree_presentation
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

(** The three native constructors determine one shape-indexed algebra. *)
Definition cotree_fold_algebra {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_algebra (cotree_pointed_container A) B :=
  fun s =>
    match s as t return (cotree_position t -> B) -> B with
    | cotree_bottom_shape => fun _ => z
    | cotree_leaf_shape a => fun _ => leaf a
    | cotree_node_shape => node
    end.

Definition indexed_tfold {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_cotree_basis A -> B :=
  basis_fold (cotree_fold_algebra z leaf node).

Lemma indexed_tfold_native {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (b : indexed_cotree_basis A) :
  indexed_tfold z leaf node b =
  tfold z leaf node (indexed_basis_to_atree b).
Proof.
  destruct b as [x].
  unfold indexed_tfold, basis_fold, indexed_basis_to_atree.
  induction x as [s children IH]; destruct s as [|a|]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply functional_extensionality; intro b.
    specialize (IH b); simpl in IH; exact IH.
Qed.

Lemma monotone_indexed_tfold {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  (forall t, z ⊑ tfold z leaf node t) ->
  Proper (leq ==> leq) node ->
  Proper (leq ==> leq) (indexed_tfold z leaf node).
Proof.
  intros Hz Hnode.
  apply (@monotone_basis_fold (cotree_pointed_container A) B _ z
    (cotree_fold_algebra z leaf node)).
  - intros children; reflexivity.
  - intro b.
    pose proof (indexed_tfold_native z leaf node b) as Hfold.
    unfold indexed_tfold in Hfold; rewrite Hfold; apply Hz.
  - intros [|a|]; simpl.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; reflexivity.
    + exact Hnode.
Qed.

Definition indexed_co_tfold {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  cotree bool A -> B :=
  fun t =>
    value_fold (cotree_fold_algebra z leaf node)
      (cotree_to_indexed_value t).

Definition indexed_tcofold {A B : Type} `{PType B}
  (leaf : A -> B) (node : (bool -> B) -> B) :
  cotree bool A -> B :=
  indexed_co_tfold ⊥ leaf node.

Lemma directed_indexed_tfold_ideal {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (t : cotree bool A) :
  (forall x, z ⊑ tfold z leaf node x) ->
  Proper (leq ==> leq) node ->
  directed
    (fun i =>
      indexed_tfold z leaf node
        (ideal (cotree_to_indexed_value t) i)).
Proof.
  intros Hz Hnode.
  change (directed
    (compose (indexed_tfold z leaf node)
      (ideal (cotree_to_indexed_value t)))).
  apply monotone_directed.
  - apply monotone_indexed_tfold; assumption.
  - apply chain_directed, chain_ideal.
Qed.

(** The reusable constructor equations now specialize the common container
    bottom, nullary-layer, and general-layer theorems. *)
Lemma indexed_co_tfold_bot {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_co_tfold z leaf node cobot === z.
Proof.
  unfold indexed_co_tfold.
  rewrite cotree_to_indexed_value_bottom.
  apply (@value_fold_bottom
    (cotree_pointed_container A) B _ _ _ _ z
    (cotree_fold_algebra z leaf node)
    (fun p : Empty_set => match p with end)).
  intros children; reflexivity.
Qed.

Lemma indexed_co_tfold_leaf {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A) :
  z ⊑ leaf a ->
  indexed_co_tfold z leaf node (coleaf a) === leaf a.
Proof.
  intro Hza.
  unfold indexed_co_tfold.
  rewrite cotree_to_indexed_value_leaf.
  apply (@value_fold_nullary
    (cotree_pointed_container A) B _ _ _ _ z
    (cotree_fold_algebra z leaf node) (cotree_leaf_shape a)
    (fun p : Empty_set => match p with end)
    (fun p : Empty_set => match p with end)).
  - intros children; reflexivity.
  - exact Hza.
  - intros x y Hxy; reflexivity.
Qed.

Lemma indexed_co_tfold_node {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> cotree bool A) :
  wcontinuous node ->
  (forall t, z ⊑ tfold z leaf node t) ->
  z ⊑ node (fun _ => z) ->
  indexed_co_tfold z leaf node (conode children) ===
  node (indexed_co_tfold z leaf node ∘ children).
Proof.
  intros Hnode Hz Hzn; clear Hzn.
  unfold indexed_co_tfold.
  rewrite cotree_to_indexed_value_node.
  apply (@value_fold_layer
    (cotree_pointed_container A) B _ _ _ _ z
    (cotree_fold_algebra z leaf node) cotree_node_shape
    (fun b : bool => cotree_to_indexed_value (children b))).
  - intros bottom_children; reflexivity.
  - intro b.
    pose proof (indexed_tfold_native z leaf node b) as Hfold.
    unfold indexed_tfold in Hfold; rewrite Hfold; apply Hz.
  - intros [|a|]; simpl.
    + apply continuous_wcontinuous, continuous_const.
    + apply continuous_wcontinuous, continuous_const.
    + exact Hnode.
Qed.

Lemma indexed_co_tfold_bot' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@CPO B o}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_co_tfold z leaf node cobot = z.
Proof. apply ext, indexed_co_tfold_bot. Qed.

Lemma indexed_co_tfold_leaf' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@CPO B o}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A) :
  z ⊑ leaf a ->
  indexed_co_tfold z leaf node (coleaf a) = leaf a.
Proof. intro Hza; apply ext, indexed_co_tfold_leaf; exact Hza. Qed.

Lemma indexed_co_tfold_node' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@CPO B o}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> cotree bool A) :
  wcontinuous node ->
  (forall t, z ⊑ tfold z leaf node t) ->
  z ⊑ node (fun _ => z) ->
  indexed_co_tfold z leaf node (conode children) =
  node (indexed_co_tfold z leaf node ∘ children).
Proof.
  intros Hnode Hz Hzn; apply ext, indexed_co_tfold_node; assumption.
Qed.

Lemma indexed_tcofold_bot' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@PType B o} `{@CPO B o}
  (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_tcofold leaf node cobot = ⊥.
Proof. apply indexed_co_tfold_bot'. Qed.

Lemma indexed_tcofold_leaf' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@PType B o} `{@CPO B o}
  (leaf : A -> B) (node : (bool -> B) -> B) (a : A) :
  indexed_tcofold leaf node (coleaf a) = leaf a.
Proof. apply indexed_co_tfold_leaf', bot_le. Qed.

Lemma indexed_tcofold_node' {A B : Type}
  {o : OType B} `{@ExtType B o} `{@PType B o} `{@CPO B o}
  (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> cotree bool A) :
  wcontinuous node ->
  indexed_tcofold leaf node (conode children) =
  node (indexed_tcofold leaf node ∘ children).
Proof.
  intro Hnode; apply indexed_co_tfold_node'.
  - exact Hnode.
  - intro t; apply bot_le.
  - apply bot_le.
Qed.

(** Keep the node algebra explicit at call sites; Coq otherwise infers it as
    an implicit argument from the equation's right-hand side. *)
Arguments indexed_tcofold_node' {A B o H H0 H1}
  leaf node children _.

(** ** Native cotree map *)

Definition indexed_atree_cotree_map {A B : Type} (f : A -> B) :
  indexed_cotree_basis A -> cotree bool B :=
  fun b => atree_cotree_map f (indexed_basis_to_atree b).

#[global]
Instance monotone_indexed_atree_cotree_map {A B : Type} (f : A -> B) :
  Proper (leq ==> leq) (indexed_atree_cotree_map f).
Proof.
  intros x y Hxy; apply monotone_atree_cotree_map.
  apply presented_monotone_indexed_basis_to_atree; exact Hxy.
Qed.

Definition indexed_cotree_map_value {A B : Type} (f : A -> B) :
  indexed_cotree_value A -> cotree bool B :=
  value_fold
    (cotree_fold_algebra (bot : cotree bool B)
      (@coleaf bool B ∘ f) (@conode bool B)).

Definition indexed_cotree_map {A B : Type} (f : A -> B) :
  cotree bool A -> cotree bool B :=
  fun t => indexed_cotree_map_value f (cotree_to_indexed_value t).

Lemma continuous_indexed_cotree_map_value {A B : Type} (f : A -> B) :
  continuous (indexed_cotree_map_value f).
Proof.
  unfold indexed_cotree_map_value, value_fold.
  apply continuous_co.
  apply monotone_indexed_tfold.
  - intro t; apply bot_le.
  - apply continuous_monotone, continuous_conode.
Qed.

Lemma continuous_indexed_cotree_map {A B : Type} (f : A -> B) :
  continuous (indexed_cotree_map f).
Proof.
  change
    (continuous
      (compose (indexed_cotree_map_value f) (@cotree_to_indexed_value A))).
  apply continuous_compose.
  - apply presented_continuous_cotree_to_indexed_value.
  - apply continuous_indexed_cotree_map_value.
Qed.

Lemma indexed_cotree_map_bot {A B : Type} (f : A -> B) :
  indexed_cotree_map f cobot = cobot.
Proof.
  change
    (indexed_tcofold (@coleaf bool B ∘ f) (@conode bool B) cobot =
      (⊥ : cotree bool B)).
  apply indexed_tcofold_bot'.
Qed.

Lemma indexed_cotree_map_leaf {A B : Type} (f : A -> B) (a : A) :
  indexed_cotree_map f (coleaf a) = coleaf (f a).
Proof.
  change
    (indexed_tcofold (@coleaf bool B ∘ f) (@conode bool B) (coleaf a) =
      coleaf (f a)).
  apply
    (indexed_tcofold_leaf' (@coleaf bool B ∘ f) (@conode bool B) a).
Qed.

Lemma indexed_cotree_map_node {A B : Type} (f : A -> B)
  (children : bool -> cotree bool A) :
  indexed_cotree_map f (conode children) =
  conode (indexed_cotree_map f ∘ children).
Proof.
  change
    (indexed_tcofold (@coleaf bool B ∘ f) (@conode bool B)
      (conode children) =
    conode
      (indexed_tcofold (@coleaf bool B ∘ f) (@conode bool B) ∘
        children)).
  apply
    (indexed_tcofold_node'
      (@coleaf bool B ∘ f) (@conode bool B) children).
  apply continuous_wcontinuous, continuous_conode.
Qed.

Lemma indexed_cotree_map_value_incl {A B : Type}
  (f : A -> B) (b : indexed_cotree_basis A) :
  indexed_cotree_map_value f (incl b) = indexed_atree_cotree_map f b.
Proof.
  unfold indexed_cotree_map_value, value_fold.
  transitivity
    (indexed_tfold (bot : cotree bool B)
      (@coleaf bool B ∘ f) (@conode bool B) b).
  - apply co_incl'_ext.
    apply monotone_indexed_tfold.
    + intro t; apply bot_le.
    + apply continuous_monotone, continuous_conode.
  - rewrite indexed_tfold_native; reflexivity.
Qed.

Lemma atree_cotree_map_tinj_map {A B : Type}
  (f : A -> B) (t : atree bool A) :
  atree_cotree_map f t = tinj (atree_map f t).
Proof.
  unfold atree_cotree_map.
  induction t as [|a|children IH]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply functional_extensionality; intro b; apply IH.
Qed.

Corollary indexed_cotree_map_value_incl_atree {A B : Type}
  (f : A -> B) (t : atree bool A) :
  indexed_cotree_map_value f (incl (atree_to_indexed_basis t)) =
  tinj (atree_map f t).
Proof.
  rewrite indexed_cotree_map_value_incl.
  unfold indexed_atree_cotree_map.
  rewrite indexed_basis_to_atree_to_basis.
  apply atree_cotree_map_tinj_map.
Qed.

Corollary indexed_cotree_map_tinj {A B : Type}
  (f : A -> B) (t : atree bool A) :
  indexed_cotree_map f (tinj t) = tinj (atree_map f t).
Proof.
  induction t as [|a|children IH]; simpl.
  - apply indexed_cotree_map_bot.
  - apply indexed_cotree_map_leaf.
  - rewrite indexed_cotree_map_node; f_equal.
    apply functional_extensionality; intro b; apply IH.
Qed.

(** The existing implementation is used only as a final regression oracle. *)
Theorem indexed_cotree_map_eq_cotree_map {A B : Type} (f : A -> B)
  (t : cotree bool A) :
  indexed_cotree_map f t = cotree_map f t.
Proof.
  apply cotree_ext; revert t; cofix CH; intros [|a|children].
  - rewrite indexed_cotree_map_bot, cotree_map_bot; constructor.
  - rewrite indexed_cotree_map_leaf, cotree_map_leaf; constructor.
  - rewrite indexed_cotree_map_node, cotree_map_node.
    constructor; intro b; apply CH.
Qed.
