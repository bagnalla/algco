(** * A canonical colist API over descriptor-indexed fixed points. *)

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

(** These are the public carriers, not wrappers around a second colist
    representation. *)
Definition colist_basis (A : Type) : Type :=
  Basis (composed_colist_descriptor A).

Definition colist (A : Type) : Type :=
  Value (composed_colist_descriptor A).

Arguments colist_basis A : clear implicits.
Arguments colist A : clear implicits.

Definition bnil {A : Type} : colist_basis A :=
  (bot : colist_basis A).

Definition bcons {A : Type} (a : A) (tail : colist_basis A) :
  colist_basis A :=
  in_basis (composed_colist_cons_shape a)
    (composed_colist_children a tail).

Definition conil {A : Type} : colist A :=
  (bot : colist A).

Definition cocons {A : Type} (a : A) (tail : colist A) : colist A :=
  in_value (composed_colist_cons_shape a)
    (composed_colist_children a tail).

Lemma bnil_is_bottom {A : Type} : @bnil A = (bot : colist_basis A).
Proof. reflexivity. Qed.

Lemma conil_is_bottom {A : Type} : @conil A = (bot : colist A).
Proof. reflexivity. Qed.

Lemma in_value_bottom_eq_conil {A : Type}
  (children : position
    (pc_container (composed_colist_descriptor A))
    (composed_colist_bottom_shape A) -> colist A) :
  in_value (composed_colist_bottom_shape A) children = @conil A.
Proof.
  unfold conil, in_value.
  change
    ({| value_carrier :=
          in_nu (composed_colist_bottom_shape A)
            (fun p => value_carrier (children p)) |} =
     {| value_carrier := nu_bottom (composed_colist_descriptor A) |}).
  f_equal; unfold nu_bottom; f_equal.
  apply functional_extensionality; intro p; destruct p.
Qed.

Lemma monotone_bcons {A : Type} (a : A) : monotone (bcons a).
Proof.
  intros x y Hxy; apply monotone_in_basis; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hxy.
Qed.

Lemma monotone_cocons {A : Type} (a : A) : monotone (cocons a).
Proof.
  intros x y Hxy; apply monotone_in_value; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hxy.
Qed.

Lemma continuous_colist_children {A : Type} (a : A) :
  continuous (fun tail : colist A => composed_colist_children a tail).
Proof.
  intros d Hdirected limit Hsup.
  apply supremum_apply; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hsup.
Qed.

Lemma continuous_cocons {A : Type} (a : A) : continuous (cocons a).
Proof.
  unfold cocons.
  change
    (continuous
      ((@in_value (composed_colist_descriptor A)
          (composed_colist_cons_shape a)) ∘
       (fun tail : colist A => composed_colist_children a tail))).
  apply continuous_compose.
  - apply continuous_colist_children.
  - apply continuous_in_value; discriminate.
Qed.

(** The desired list-like induction principle.  Functional extensionality is
    used once here to identify arbitrary container child functions over empty
    and singleton position types with the named constructors.  Client proofs
    see only the two familiar cases. *)
Theorem colist_basis_ind {A : Type} (P : colist_basis A -> Prop) :
  P bnil ->
  (forall a tail, P tail -> P (bcons a tail)) ->
  forall x, P x.
Proof.
  intros Hnil Hcons x.
  apply (@basis_induction (composed_colist_descriptor A) P).
  intros [u | [a u]] children IH.
  - destruct u.
    assert (Hbottom :
      in_basis (composed_colist_bottom_shape A) children = @bnil A).
    { unfold bnil, in_basis.
      change
        ({| basis_carrier :=
              in_mu (composed_colist_bottom_shape A)
                (fun p => basis_carrier (children p)) |} =
         {| basis_carrier := mu_bottom (composed_colist_descriptor A) |}).
      f_equal; unfold mu_bottom; f_equal.
      apply functional_extensionality; intro p; destruct p.
    }
    change (P (in_basis (composed_colist_bottom_shape A) children)).
    rewrite Hbottom; exact Hnil.
  - destruct u.
    set (tail := children (composed_colist_tail_position a)).
    assert (Hlayer :
      in_basis (composed_colist_cons_shape a) children = bcons a tail).
    { unfold bcons, tail, in_basis; f_equal; f_equal.
      apply functional_extensionality; intro p.
      destruct p as [p | u].
      * destruct p.
      * destruct u; reflexivity.
    }
    change (P (in_basis (composed_colist_cons_shape a) children)).
    rewrite Hlayer; apply Hcons; unfold tail; apply IH.
Qed.

(** A one-layer observation is a view of the canonical coinductive carrier,
    not a second recursive representation. *)
Inductive colist_view (A : Type) : Type :=
| view_nil
| view_cons (head : A) (tail : colist A).

Arguments view_nil {A}.
Arguments view_cons {A} head tail.

Definition observe {A : Type} (x : colist A) : colist_view A.
Proof.
  destruct x as [[s children]].
  destruct s as [u | [a u]].
  - exact view_nil.
  - exact (view_cons a {| value_carrier := children (inr tt) |}).
Defined.

Lemma observe_conil {A : Type} : observe (@conil A) = view_nil.
Proof. reflexivity. Qed.

Lemma observe_cocons {A : Type} (a : A) (tail : colist A) :
  observe (cocons a tail) = view_cons a tail.
Proof.
  unfold observe, cocons, composed_colist_children, in_value; simpl.
  destruct tail; reflexivity.
Qed.

Definition prefix {A : Type} (n : nat) (x : colist A) : colist_basis A :=
  value_ideal x n.

Definition basis_inclusion {A : Type} (x : colist_basis A) : colist A :=
  basis_incl x.

Lemma prefix_chain {A : Type} (x : colist A) :
  chain (fun n => prefix n x).
Proof.
  intro n; exact
    (@chain_value_ideal (composed_colist_descriptor A) x n).
Qed.

Definition colist_basis_fold {A B : Type}
  (z : B) (step : A -> B -> B) : colist_basis A -> B :=
  basis_fold (composed_colist_algebra z step).

Lemma colist_basis_fold_nil {A B : Type}
  (z : B) (step : A -> B -> B) :
  colist_basis_fold z step (@bnil A) = z.
Proof. reflexivity. Qed.

Lemma colist_basis_fold_cons {A B : Type}
  (z : B) (step : A -> B -> B) (a : A) (tail : colist_basis A) :
  colist_basis_fold z step (bcons a tail) =
  step a (colist_basis_fold z step tail).
Proof. reflexivity. Qed.

Lemma monotone_colist_basis_fold {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) :
  (forall x : colist_basis A, z ⊑ colist_basis_fold z step x) ->
  (forall a, Proper (leq ==> leq) (step a)) ->
  monotone (colist_basis_fold z step).
Proof.
  intros Hbase Hstep.
  apply (@monotone_basis_fold
    (composed_colist_descriptor A) B _ z
    (composed_colist_algebra z step)).
  - intros children; reflexivity.
  - exact Hbase.
  - intros [u | [a u]]; destruct u; simpl.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; apply Hstep, Hxy.
Qed.

Definition colist_value_fold {A B : Type} `{OType B}
  (z : B) (step : A -> B -> B) : colist A -> B :=
  composed_colist_value_fold z step.

Lemma colist_value_fold_nil {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B) :
  colist_value_fold z step (@conil A) === z.
Proof.
  unfold colist_value_fold.
  rewrite <- (in_value_bottom_eq_conil
    (children := fun p => match p with end)).
  apply composed_colist_value_fold_bottom.
Qed.

Lemma colist_value_fold_cons {A B : Type} `{CPO B}
  (z : B) (step : A -> B -> B) (a : A) (tail : colist A) :
  (forall x : colist_basis A, z ⊑ colist_basis_fold z step x) ->
  (forall x, continuous (step x)) ->
  colist_value_fold z step (cocons a tail) ===
  step a (colist_value_fold z step tail).
Proof.
  unfold colist_value_fold, cocons, colist_basis_fold.
  apply composed_colist_value_fold_cons.
Qed.

Definition basis_map {A B : Type} (f : A -> B) :
  colist_basis A -> colist_basis B :=
  colist_basis_fold bnil (fun a tail => bcons (f a) tail).

Lemma basis_map_nil {A B : Type} (f : A -> B) :
  basis_map f (@bnil A) = @bnil B.
Proof. reflexivity. Qed.

Lemma basis_map_cons {A B : Type} (f : A -> B)
  (a : A) (tail : colist_basis A) :
  basis_map f (bcons a tail) = bcons (f a) (basis_map f tail).
Proof. reflexivity. Qed.

Lemma monotone_basis_map {A B : Type} (f : A -> B) :
  monotone (basis_map f).
Proof.
  unfold basis_map.
  apply monotone_colist_basis_fold.
  - intro x; rewrite bnil_is_bottom; apply bot_le.
  - intro a; apply monotone_bcons.
Qed.

(** A representative client proof uses only the named induction cases and
    computation rules. *)
Lemma basis_map_id {A : Type} (x : colist_basis A) :
  basis_map (fun a => a) x = x.
Proof.
  induction x using colist_basis_ind.
  - reflexivity.
  - rewrite basis_map_cons, IHx; reflexivity.
Qed.

Definition comap {A B : Type} (f : A -> B) : colist A -> colist B :=
  colist_value_fold conil (fun a tail => cocons (f a) tail).

Lemma continuous_comap {A B : Type} (f : A -> B) :
  continuous (comap f).
Proof.
  unfold comap, colist_value_fold, composed_colist_value_fold, value_fold.
  apply continuous_co.
  apply monotone_colist_basis_fold.
  - intro x; rewrite conil_is_bottom; apply bot_le.
  - intro a; apply monotone_cocons.
Qed.

Lemma comap_nil {A B : Type} (f : A -> B) :
  comap f (@conil A) === @conil B.
Proof.
  unfold comap; apply colist_value_fold_nil.
Qed.

Lemma comap_cons {A B : Type} (f : A -> B)
  (a : A) (tail : colist A) :
  comap f (cocons a tail) === cocons (f a) (comap f tail).
Proof.
  change
    (colist_value_fold (@conil B) (fun x t => cocons (f x) t)
      (cocons a tail) ===
     cocons (f a)
       (colist_value_fold (@conil B) (fun x t => cocons (f x) t) tail)).
  apply (@colist_value_fold_cons A (colist B) _ _
    (@conil B) (fun x t => cocons (f x) t) a tail).
  - intro x; rewrite conil_is_bottom; apply bot_le.
  - intro x; apply continuous_cocons.
Qed.
