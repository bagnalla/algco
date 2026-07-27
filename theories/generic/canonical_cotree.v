(** * A canonical Boolean-cotree API over descriptor-indexed fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
  FunctionalExtensionality
  Morphisms
.

From algco Require Import
  aCPO
  cpo
  order
.

From algco.generic Require Import
  container
  container_combinator_examples
  indexed_container
  indexed_fold
  pointed_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

Definition cotree_basis (A : Type) : Type :=
  Basis (composed_cotree_descriptor A).

Definition cotree (A : Type) : Type :=
  Value (composed_cotree_descriptor A).

Arguments cotree_basis A : clear implicits.
Arguments cotree A : clear implicits.

Definition bbottom {A : Type} : cotree_basis A :=
  (bot : cotree_basis A).

Definition bleaf {A : Type} (a : A) : cotree_basis A :=
  in_basis (composed_cotree_leaf_shape a)
    (fun p => match p with end).

Definition bnode {A : Type} (children : bool -> cotree_basis A) :
  cotree_basis A :=
  in_basis (composed_cotree_node_shape A) children.

Definition cobottom {A : Type} : cotree A :=
  (bot : cotree A).

Definition coleaf {A : Type} (a : A) : cotree A :=
  in_value (composed_cotree_leaf_shape a)
    (fun p => match p with end).

Definition conode {A : Type} (children : bool -> cotree A) : cotree A :=
  in_value (composed_cotree_node_shape A) children.

Lemma bbottom_is_bottom {A : Type} :
  @bbottom A = (bot : cotree_basis A).
Proof. reflexivity. Qed.

Lemma cobottom_is_bottom {A : Type} : @cobottom A = (bot : cotree A).
Proof. reflexivity. Qed.

Lemma in_value_bottom_eq_cobottom {A : Type}
  (children : position
    (pc_container (composed_cotree_descriptor A))
    (composed_cotree_bottom_shape A) -> cotree A) :
  in_value (composed_cotree_bottom_shape A) children = @cobottom A.
Proof.
  unfold cobottom, in_value.
  change
    ({| value_carrier :=
          in_nu (composed_cotree_bottom_shape A)
            (fun p => value_carrier (children p)) |} =
     {| value_carrier := nu_bottom (composed_cotree_descriptor A) |}).
  f_equal; unfold nu_bottom; f_equal.
  apply functional_extensionality; intro p; destruct p.
Qed.

Lemma monotone_bnode {A : Type} : monotone (@bnode A).
Proof. intros x y Hxy; apply monotone_in_basis; exact Hxy. Qed.

Lemma monotone_conode {A : Type} : monotone (@conode A).
Proof. intros x y Hxy; apply monotone_in_value; exact Hxy. Qed.

Lemma continuous_conode {A : Type} : continuous (@conode A).
Proof.
  unfold conode.
  apply (@continuous_in_value
    (composed_cotree_descriptor A) _
    (composed_cotree_node_shape A)); discriminate.
Qed.

(** Bottom and leaf child functions are propositionally unique rather than
    definitionally unique in intensional Coq.  Functional extensionality is
    confined to this one facade theorem; the client-facing induction cases are
    the expected bottom, leaf, and Boolean-node cases. *)
Theorem cotree_basis_ind {A : Type} (P : cotree_basis A -> Prop) :
  P bbottom ->
  (forall a, P (bleaf a)) ->
  (forall children, (forall b, P (children b)) -> P (bnode children)) ->
  forall x, P x.
Proof.
  intros Hbottom Hleaf Hnode x.
  apply (@basis_induction (composed_cotree_descriptor A) P).
  intros [u | [a | u]] children IH.
  - destruct u.
    assert (Hlayer :
      in_basis (composed_cotree_bottom_shape A) children = @bbottom A).
    { unfold bbottom, in_basis.
      change
        ({| basis_carrier :=
              in_mu (composed_cotree_bottom_shape A)
                (fun p => basis_carrier (children p)) |} =
         {| basis_carrier := mu_bottom (composed_cotree_descriptor A) |}).
      f_equal; unfold mu_bottom; f_equal.
      apply functional_extensionality; intro p; destruct p.
    }
    change (P (in_basis (composed_cotree_bottom_shape A) children)).
    rewrite Hlayer; exact Hbottom.
  - assert (Hlayer :
      in_basis (composed_cotree_leaf_shape a) children = bleaf a).
    { unfold bleaf, in_basis; f_equal; f_equal.
      apply functional_extensionality; intro p; destruct p.
    }
    change (P (in_basis (composed_cotree_leaf_shape a) children)).
    rewrite Hlayer; apply Hleaf.
  - destruct u.
    change (P (bnode children)).
    apply Hnode; exact IH.
Qed.

Inductive cotree_view (A : Type) : Type :=
| view_bottom
| view_leaf (value : A)
| view_node (children : bool -> cotree A).

Arguments view_bottom {A}.
Arguments view_leaf {A} value.
Arguments view_node {A} children.

Definition observe {A : Type} (x : cotree A) : cotree_view A.
Proof.
  destruct x as [[s children]].
  destruct s as [u | [a | u]].
  - exact view_bottom.
  - exact (view_leaf a).
  - exact (view_node (fun b => {| value_carrier := children b |})).
Defined.

Lemma observe_cobottom {A : Type} :
  observe (@cobottom A) = view_bottom.
Proof. reflexivity. Qed.

Lemma observe_coleaf {A : Type} (a : A) :
  observe (coleaf a) = view_leaf a.
Proof. reflexivity. Qed.

Lemma observe_conode {A : Type} (children : bool -> cotree A) :
  observe (conode children) = view_node children.
Proof.
  unfold observe, conode, in_value; simpl.
  f_equal; apply functional_extensionality; intro b.
  destruct (children b); reflexivity.
Qed.

Definition prefix {A : Type} (n : nat) (x : cotree A) : cotree_basis A :=
  value_ideal x n.

Definition basis_inclusion {A : Type} (x : cotree_basis A) : cotree A :=
  basis_incl x.

Lemma prefix_chain {A : Type} (x : cotree A) :
  chain (fun n => prefix n x).
Proof.
  intro n; exact
    (@chain_value_ideal (composed_cotree_descriptor A) x n).
Qed.

Definition cotree_basis_fold {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  cotree_basis A -> B :=
  basis_fold (composed_cotree_algebra z leaf node).

Lemma cotree_basis_fold_bottom {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  cotree_basis_fold z leaf node (@bbottom A) = z.
Proof. reflexivity. Qed.

Lemma cotree_basis_fold_leaf {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A) :
  cotree_basis_fold z leaf node (bleaf a) = leaf a.
Proof. reflexivity. Qed.

Lemma cotree_basis_fold_node {A B : Type}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> cotree_basis A) :
  cotree_basis_fold z leaf node (bnode children) =
  node (fun b => cotree_basis_fold z leaf node (children b)).
Proof. reflexivity. Qed.

Lemma monotone_cotree_basis_fold {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  (forall x : cotree_basis A, z ⊑ cotree_basis_fold z leaf node x) ->
  Proper (leq ==> leq) node ->
  monotone (cotree_basis_fold z leaf node).
Proof.
  intros Hbase Hnode.
  apply (@monotone_basis_fold
    (composed_cotree_descriptor A) B _ z
    (composed_cotree_algebra z leaf node)).
  - intros children; reflexivity.
  - exact Hbase.
  - intros [u | [a | u]]; simpl.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; reflexivity.
    + exact Hnode.
Qed.

Definition cotree_value_fold {A B : Type} `{OType B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) : cotree A -> B :=
  composed_cotree_value_fold z leaf node.

Lemma cotree_value_fold_bottom {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) :
  cotree_value_fold z leaf node (@cobottom A) === z.
Proof.
  unfold cotree_value_fold.
  rewrite <- (in_value_bottom_eq_cobottom
    (children := fun p => match p with end)).
  apply composed_cotree_value_fold_bottom.
Qed.

Lemma cotree_value_fold_leaf {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B) (a : A) :
  z ⊑ leaf a ->
  cotree_value_fold z leaf node (coleaf a) === leaf a.
Proof.
  intro Hbase; unfold cotree_value_fold, coleaf.
  apply composed_cotree_value_fold_leaf; exact Hbase.
Qed.

Lemma cotree_value_fold_node {A B : Type} `{CPO B}
  (z : B) (leaf : A -> B) (node : (bool -> B) -> B)
  (children : bool -> cotree A) :
  (forall x : cotree_basis A, z ⊑ cotree_basis_fold z leaf node x) ->
  wcontinuous node ->
  cotree_value_fold z leaf node (conode children) ===
  node (fun b => cotree_value_fold z leaf node (children b)).
Proof.
  unfold cotree_value_fold, conode, cotree_basis_fold.
  apply composed_cotree_value_fold_node.
Qed.

Definition basis_map {A B : Type} (f : A -> B) :
  cotree_basis A -> cotree_basis B :=
  cotree_basis_fold bbottom (fun a => bleaf (f a)) bnode.

Lemma basis_map_bottom {A B : Type} (f : A -> B) :
  basis_map f (@bbottom A) = @bbottom B.
Proof. reflexivity. Qed.

Lemma basis_map_leaf {A B : Type} (f : A -> B) (a : A) :
  basis_map f (bleaf a) = bleaf (f a).
Proof. reflexivity. Qed.

Lemma basis_map_node {A B : Type} (f : A -> B)
  (children : bool -> cotree_basis A) :
  basis_map f (bnode children) =
  bnode (fun b => basis_map f (children b)).
Proof. reflexivity. Qed.

Lemma monotone_basis_map {A B : Type} (f : A -> B) :
  monotone (basis_map f).
Proof.
  unfold basis_map.
  apply monotone_cotree_basis_fold.
  - intro x; rewrite bbottom_is_bottom; apply bot_le.
  - apply monotone_bnode.
Qed.

Lemma basis_map_id {A : Type} (x : cotree_basis A) :
  basis_map (fun a => a) x = x.
Proof.
  induction x using cotree_basis_ind.
  - reflexivity.
  - reflexivity.
  - rewrite basis_map_node.
    f_equal; apply functional_extensionality; intro b; apply H.
Qed.

Definition comap {A B : Type} (f : A -> B) : cotree A -> cotree B :=
  cotree_value_fold cobottom (fun a => coleaf (f a)) conode.

Lemma continuous_comap {A B : Type} (f : A -> B) :
  continuous (comap f).
Proof.
  unfold comap, cotree_value_fold, composed_cotree_value_fold, value_fold.
  apply continuous_co.
  apply monotone_cotree_basis_fold.
  - intro x; rewrite cobottom_is_bottom; apply bot_le.
  - apply monotone_conode.
Qed.

Lemma comap_bottom {A B : Type} (f : A -> B) :
  comap f (@cobottom A) === @cobottom B.
Proof. unfold comap; apply cotree_value_fold_bottom. Qed.

Lemma comap_leaf {A B : Type} (f : A -> B) (a : A) :
  comap f (coleaf a) === coleaf (f a).
Proof.
  change
    (cotree_value_fold (@cobottom B) (fun x => coleaf (f x)) conode
      (coleaf a) === coleaf (f a)).
  apply (@cotree_value_fold_leaf A (cotree B) _ _
    (@cobottom B) (fun x => coleaf (f x)) conode a).
  rewrite cobottom_is_bottom; apply bot_le.
Qed.

Lemma comap_node {A B : Type} (f : A -> B)
  (children : bool -> cotree A) :
  comap f (conode children) === conode (fun b => comap f (children b)).
Proof.
  change
    (cotree_value_fold (@cobottom B) (fun a => coleaf (f a)) conode
      (conode children) ===
     conode
       (fun b =>
         cotree_value_fold (@cobottom B) (fun a => coleaf (f a)) conode
           (children b))).
  apply (@cotree_value_fold_node A (cotree B) _ _
    (@cobottom B) (fun a => coleaf (f a)) conode children).
  - intro x; rewrite cobottom_is_bottom; apply bot_le.
  - apply continuous_wcontinuous, continuous_conode.
Qed.
