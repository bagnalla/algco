(** * Colist and Boolean-cotree signatures assembled from container
    combinators. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
  List
  Morphisms
.

From algco Require Import
  cpo
  order
.

From algco.generic Require Import
  container
  container_combinators
  indexed_container
  indexed_container_combinators
  indexed_fold
  pointed_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

(** ** Linear example *)

Definition composed_colist_signature (A : Type) : finitary_container :=
  finitary_product
    (finitary_constant A)
    (finitary_recursive unit_index).

Definition composed_colist_descriptor (A : Type) : pointed_container :=
  finitary_point (composed_colist_signature A).

Definition composed_colist_bottom_shape (A : Type) :
  shape (pc_container (composed_colist_descriptor A)) :=
  inl tt.

Arguments composed_colist_bottom_shape A : clear implicits.

Definition composed_colist_cons_shape {A : Type} (a : A) :
  shape (pc_container (composed_colist_descriptor A)) :=
  inr (a, tt).

Definition composed_colist_tail_position {A : Type} (a : A) :
  position (pc_container (composed_colist_descriptor A))
    (composed_colist_cons_shape a) :=
  inr tt.

Arguments composed_colist_tail_position {A} a.

Definition composed_colist_children {A X : Type} (a : A) (x : X) :
  position (pc_container (composed_colist_descriptor A))
    (composed_colist_cons_shape a) -> X :=
  fun p =>
    match p with
    | inl impossible => match impossible with end
    | inr _ => x
    end.

Arguments composed_colist_children {A X} a x.

Definition composed_colist_algebra {A B : Type}
  (z : B) (step : A -> B -> B) :
  indexed_algebra (composed_colist_descriptor A) B.
Proof.
  intros [u | [a u]] children.
  - exact z.
  - exact (step a (children (inr tt))).
Defined.

Definition composed_colist_value_fold {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) :
  Value (composed_colist_descriptor A) -> B :=
  value_fold (composed_colist_algebra z step).

Lemma composed_colist_basis_fold_bottom {A B : Type}
  (z : B) (step : A -> B -> B)
  (children : position
    (pc_container (composed_colist_descriptor A))
    (composed_colist_bottom_shape A) ->
    Basis (composed_colist_descriptor A)) :
  basis_fold (composed_colist_algebra z step)
    (in_basis (composed_colist_bottom_shape A) children) = z.
Proof. reflexivity. Qed.

Lemma composed_colist_basis_fold_cons {A B : Type}
  (z : B) (step : A -> B -> B) (a : A)
  (children : position
    (pc_container (composed_colist_descriptor A))
    (composed_colist_cons_shape a) ->
    Basis (composed_colist_descriptor A)) :
  basis_fold (composed_colist_algebra z step)
    (in_basis (composed_colist_cons_shape a) children) =
  step a
    (basis_fold (composed_colist_algebra z step)
      (children (composed_colist_tail_position a))).
Proof. reflexivity. Qed.

Lemma composed_colist_value_fold_bottom {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B)
  (children : position
    (pc_container (composed_colist_descriptor A))
    (composed_colist_bottom_shape A) ->
    Value (composed_colist_descriptor A)) :
  composed_colist_value_fold z step
    (in_value (composed_colist_bottom_shape A) children) === z.
Proof.
  unfold composed_colist_value_fold.
  apply (@value_fold_bottom
    (composed_colist_descriptor A) B _ _ _ _ z
    (composed_colist_algebra z step) children).
  intros bottom_children; reflexivity.
Qed.

Lemma composed_colist_value_fold_cons {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B) (a : A)
  (tail : Value (composed_colist_descriptor A)) :
  (forall b : Basis (composed_colist_descriptor A),
    z ⊑ basis_fold (composed_colist_algebra z step) b) ->
  (forall x, continuous (step x)) ->
  composed_colist_value_fold z step
    (in_value (composed_colist_cons_shape a)
      (composed_colist_children a tail)) ===
  step a (composed_colist_value_fold z step tail).
Proof.
  intros Hbase Hstep.
  unfold composed_colist_value_fold.
  apply (@value_fold_layer
    (composed_colist_descriptor A) B _ _ _ _ z
    (composed_colist_algebra z step) (composed_colist_cons_shape a)
    (composed_colist_children a tail)).
  - intros bottom_children; reflexivity.
  - exact Hbase.
  - intros [u | [x u]]; simpl.
    + apply continuous_wcontinuous, continuous_const.
    + intros ch Hch limit Hsup.
      apply (Hstep x).
      * apply chain_directed; intro i.
        apply Hch.
      * apply apply_supremum; exact Hsup.
Qed.

Example composed_colist_cons_position_count {A : Type} (a : A) :
  length (enumerate_positions (composed_colist_cons_shape a)) = 1.
Proof. reflexivity. Qed.

(** ** Branching example *)

Definition composed_cotree_signature (A : Type) : finitary_container :=
  finitary_sum
    (finitary_constant A)
    (finitary_recursive bool_index).

Definition composed_cotree_descriptor (A : Type) : pointed_container :=
  finitary_point (composed_cotree_signature A).

Definition composed_cotree_bottom_shape (A : Type) :
  shape (pc_container (composed_cotree_descriptor A)) :=
  inl tt.

Arguments composed_cotree_bottom_shape A : clear implicits.

Definition composed_cotree_leaf_shape {A : Type} (a : A) :
  shape (pc_container (composed_cotree_descriptor A)) :=
  inr (inl a).

Definition composed_cotree_node_shape (A : Type) :
  shape (pc_container (composed_cotree_descriptor A)) :=
  inr (inr tt).

Arguments composed_cotree_node_shape A : clear implicits.

Definition composed_cotree_algebra {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  indexed_algebra (composed_cotree_descriptor A) B.
Proof.
  intros [u | [a | u]] children.
  - exact z.
  - exact (leaf a).
  - exact (node children).
Defined.

Definition composed_cotree_value_fold {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  Value (composed_cotree_descriptor A) -> B :=
  value_fold (composed_cotree_algebra z leaf node).

Lemma composed_cotree_basis_fold_bottom {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : position
    (pc_container (composed_cotree_descriptor A))
    (composed_cotree_bottom_shape A) ->
    Basis (composed_cotree_descriptor A)) :
  basis_fold (composed_cotree_algebra z leaf node)
    (in_basis (composed_cotree_bottom_shape A) children) = z.
Proof. reflexivity. Qed.

Lemma composed_cotree_basis_fold_leaf {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A)
  (children : position
    (pc_container (composed_cotree_descriptor A))
    (composed_cotree_leaf_shape a) ->
    Basis (composed_cotree_descriptor A)) :
  basis_fold (composed_cotree_algebra z leaf node)
    (in_basis (composed_cotree_leaf_shape a) children) = leaf a.
Proof. reflexivity. Qed.

Lemma composed_cotree_basis_fold_node {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> Basis (composed_cotree_descriptor A)) :
  basis_fold (composed_cotree_algebra z leaf node)
    (in_basis (composed_cotree_node_shape A) children) =
  node (fun b =>
    basis_fold (composed_cotree_algebra z leaf node) (children b)).
Proof. reflexivity. Qed.

Lemma composed_cotree_value_fold_bottom {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : position
    (pc_container (composed_cotree_descriptor A))
    (composed_cotree_bottom_shape A) ->
    Value (composed_cotree_descriptor A)) :
  composed_cotree_value_fold z leaf node
    (in_value (composed_cotree_bottom_shape A) children) === z.
Proof.
  unfold composed_cotree_value_fold.
  apply (@value_fold_bottom
    (composed_cotree_descriptor A) B _ _ _ _ z
    (composed_cotree_algebra z leaf node) children).
  intros bottom_children; reflexivity.
Qed.

Lemma composed_cotree_value_fold_leaf {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A)
  (children : position
    (pc_container (composed_cotree_descriptor A))
    (composed_cotree_leaf_shape a) ->
    Value (composed_cotree_descriptor A)) :
  z ⊑ leaf a ->
  composed_cotree_value_fold z leaf node
    (in_value (composed_cotree_leaf_shape a) children) === leaf a.
Proof.
  intro Hbase.
  unfold composed_cotree_value_fold.
  apply (@value_fold_nullary
    (composed_cotree_descriptor A) B _ _ _ _ z
    (composed_cotree_algebra z leaf node) (composed_cotree_leaf_shape a)
    children (fun p => match p with end)).
  - intros bottom_children; reflexivity.
  - exact Hbase.
  - intros x y Hxy; reflexivity.
Qed.

Lemma composed_cotree_value_fold_node {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> Value (composed_cotree_descriptor A)) :
  (forall b : Basis (composed_cotree_descriptor A),
    z ⊑ basis_fold (composed_cotree_algebra z leaf node) b) ->
  wcontinuous node ->
  composed_cotree_value_fold z leaf node
    (in_value (composed_cotree_node_shape A) children) ===
  node (fun b => composed_cotree_value_fold z leaf node (children b)).
Proof.
  intros Hbase Hnode.
  unfold composed_cotree_value_fold.
  apply (@value_fold_layer
    (composed_cotree_descriptor A) B _ _ _ _ z
    (composed_cotree_algebra z leaf node) (composed_cotree_node_shape A)
    children).
  - intros bottom_children; reflexivity.
  - exact Hbase.
  - intros [u | [a | u]]; simpl.
    + apply continuous_wcontinuous, continuous_const.
    + apply continuous_wcontinuous, continuous_const.
    + exact Hnode.
Qed.

Example composed_cotree_leaf_position_count {A : Type} (a : A) :
  length (enumerate_positions (composed_cotree_leaf_shape a)) = 0.
Proof. reflexivity. Qed.

Example composed_cotree_node_position_count {A : Type} :
  length (enumerate_positions (composed_cotree_node_shape A)) = 2.
Proof. reflexivity. Qed.
