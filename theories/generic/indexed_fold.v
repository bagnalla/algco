(** * Generic folds over descriptor-indexed container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
  Morphisms
.

From algco Require Import
  aCPO
  cpo
  misc
  order
.

From algco.generic Require Import
  container
  indexed_container
  pointed_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

(** An algebra supplies one result constructor for every container shape. *)
Definition indexed_algebra (S : pointed_container) (B : Type) : Type :=
  forall s : shape (pc_container S),
    (position (pc_container S) s -> B) -> B.

(** Structural recursion is defined on the raw initial algebra and exposed
    through the descriptor-indexed basis wrapper. *)
Fixpoint raw_basis_fold {S : pointed_container} {B : Type}
  (alg : indexed_algebra S B) (x : mu (pc_container S)) : B :=
  match x with
  | in_mu s children =>
      alg s (fun p => raw_basis_fold alg (children p))
  end.

Definition basis_fold {S : pointed_container} {B : Type}
  (alg : indexed_algebra S B) (x : Basis S) : B :=
  raw_basis_fold alg (basis_carrier x).

Lemma basis_fold_in {S : pointed_container} {B : Type}
  (alg : indexed_algebra S B)
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Basis S) :
  basis_fold alg (in_basis s children) =
  alg s (fun p => basis_fold alg (children p)).
Proof. reflexivity. Qed.

(** Monotonicity needs exactly the conditions visible in the concrete colist
    and cotree folds: the designated bottom layer denotes a base result [z],
    that result lies below every finite fold, and every other algebra branch
    is monotone in its recursive children. *)
Lemma monotone_basis_fold {S : pointed_container} {B : Type} `{OType B}
  (z : B) (alg : indexed_algebra S B) :
  (forall children, alg (bottom_shape S) children === z) ->
  (forall x : Basis S, z ⊑ basis_fold alg x) ->
  (forall s, Proper (leq ==> leq) (alg s)) ->
  Proper (leq ==> leq) (basis_fold alg).
Proof.
  intros Hbottom Hbase Halg [x] [y] Hxy.
  change (mu_le S x y) in Hxy.
  induction Hxy as
    [children y | s children1 children2 Hchildren IH].
  - simpl. etransitivity.
    + apply (proj1 (Hbottom _)).
    + apply (Hbase {| basis_carrier := y |}).
  - simpl. apply Halg; exact IH.
Qed.

(** Continuous extension of the structural basis fold.  The [aCPO] instance
    is selected from the descriptor-indexed carrier and its capabilities. *)
Definition value_fold {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S} `{OType B}
  (alg : indexed_algebra S B) : Value S -> B :=
  co (basis_fold alg).

Lemma chain_value_ideal {S : pointed_container} (x : Value S) :
  chain (value_ideal x).
Proof.
  destruct x as [x]; intro n.
  change (mu_le S (truncate_nu n x) (truncate_nu (Datatypes.S n) x)).
  apply truncate_nu_step.
Qed.

Lemma value_fold_supremum {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S} `{CPO B}
  (alg : indexed_algebra S B) :
  monotone (basis_fold alg) ->
  forall x : Value S,
    supremum (value_fold alg x)
      (fun n => basis_fold alg (value_ideal x n)).
Proof.
  intros Hmono x.
  change
    (supremum
      (sup (fun n => basis_fold alg (value_ideal x n)))
      (fun n => basis_fold alg (value_ideal x n))).
  apply sup_spec.
  change (directed (basis_fold alg ∘ value_ideal x)).
  apply monotone_directed.
  - exact Hmono.
  - apply chain_directed.
    exact (@chain_value_ideal S x).
Qed.

(** The designated bottom value has a constant fold sequence.  This theorem
    needs no monotonicity or continuity assumptions on the other shapes. *)
Lemma value_fold_bottom {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S} `{CPO B}
  (z : B) (alg : indexed_algebra S B)
  (children : position (pc_container S) (bottom_shape S) -> Value S) :
  (forall children, alg (bottom_shape S) children === z) ->
  value_fold alg (in_value (bottom_shape S) children) === z.
Proof.
  intro Hbottom.
  unfold value_fold, co, compose, basis.
  apply supremum_sup, supremum_const', equ_arrow; intro n.
  destruct n; unfold value_ideal, basis_fold; simpl; apply Hbottom.
Qed.

(** A nonbottom nullary layer becomes visible after the first approximation.
    This weakened rule avoids imposing continuity conditions on unrelated
    recursive shapes merely to compute a leaf. *)
Lemma value_fold_nullary {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S} `{CPO B}
  (z : B) (alg : indexed_algebra S B)
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Value S)
  (position_absurd : position (pc_container S) s -> False) :
  (forall bottom_children, alg (bottom_shape S) bottom_children === z) ->
  z ⊑ alg s (fun p => False_rect B (position_absurd p)) ->
  Proper (leq ==> leq) (alg s) ->
  value_fold alg (in_value s children) ===
  alg s (fun p => value_fold alg (children p)).
Proof.
  intros Hbottom Hbase Halg.
  change
    (sup
      (fun n => basis_fold alg (value_ideal (in_value s children) n)) ===
    alg s (fun p => value_fold alg (children p))).
  apply supremum_sup.
  apply supremum_eventually_constant_at.
  - intro n; destruct n.
    + unfold value_ideal, basis_fold; simpl.
      etransitivity.
      * apply (proj1 (Hbottom _)).
      * etransitivity; [exact Hbase |].
        apply Halg; intro p; destruct (position_absurd p).
    + unfold value_ideal, basis_fold; simpl.
      apply Halg; intro p; destruct (position_absurd p).
  - exists 1; intros n Hn; destruct n.
    + inversion Hn.
    + unfold value_ideal, basis_fold; simpl.
      split; apply Halg; intro p; destruct (position_absurd p).
Qed.

(** One generic shifted-supremum argument supplies the layer equation.  The
    child approximants form a pointwise chain; weak continuity of the current
    algebra branch transports its pointwise supremum through that branch. *)
Lemma value_fold_layer {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S} `{CPO B}
  (z : B) (alg : indexed_algebra S B)
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Value S) :
  (forall bottom_children, alg (bottom_shape S) bottom_children === z) ->
  (forall x : Basis S, z ⊑ basis_fold alg x) ->
  (forall t, wcontinuous (alg t)) ->
  value_fold alg (in_value s children) ===
  alg s (fun p => value_fold alg (children p)).
Proof.
  intros Hbottom Hbase Hcontinuous.
  assert (Hmono : monotone (basis_fold alg)).
  {
    apply (@monotone_basis_fold S B _ z alg); auto.
    intro t; apply wcontinuous_monotone, Hcontinuous.
  }
  unfold value_fold, co, compose, basis.
  apply supremum_sup.
  apply shift_supremum'' with
    (f := fun i =>
      alg s
        (fun p => basis_fold alg (value_ideal (children p) i))).
  - apply Hmono.
    exact (@chain_value_ideal S (in_value s children) 0).
  - apply Hcontinuous.
    + intros i p; apply Hmono.
      exact (@chain_value_ideal S (children p) i).
    + apply supremum_apply; intro p.
      apply value_fold_supremum; exact Hmono.
  - apply equ_arrow; intro i.
    unfold shift, value_ideal, basis_fold; reflexivity.
Qed.

(** Pointed folds discharge the global lower-bound premise automatically. *)
Corollary pointed_value_fold_layer {S : pointed_container} {B : Type}
  `{DecidableBottom S} `{FinitePositions S}
  {o : OType B} `{@PType B o} `{@CPO B o}
  (alg : indexed_algebra S B)
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Value S) :
  (forall bottom_children,
    alg (bottom_shape S) bottom_children === bot) ->
  (forall t, wcontinuous (alg t)) ->
  value_fold alg (in_value s children) ===
  alg s (fun p => value_fold alg (children p)).
Proof.
  intros Hbottom Hcontinuous.
  apply (@value_fold_layer S B _ _ _ _ (bot : B) alg s children);
    auto.
  intro x; apply bot_le.
Qed.
