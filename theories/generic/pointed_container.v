(** * Approximation for pointed containers. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Program.Equality
.

From algco Require Import
  order
.

From algco.generic Require Import
  container
.

(** A pointed container designates a nullary shape as the least approximation
    hole of a partial carrier.  Nullarity is supplied as data so that the
    generic constructions do not need decidable equality on shapes.  A
    semantic signature can acquire this structure through an explicit lift. *)
Record pointed_container : Type :=
  { pc_container : container
  ; bottom_shape : shape pc_container
  ; bottom_position_absurd : position pc_container bottom_shape -> False
  }.

Definition mu_bottom (C : pointed_container) : mu (pc_container C) :=
  in_mu (bottom_shape C)
    (fun p => False_rect _ (bottom_position_absurd C p)).

Definition nu_bottom (C : pointed_container) : nu (pc_container C) :=
  in_nu (bottom_shape C)
    (fun p => False_rect _ (bottom_position_absurd C p)).

(** The approximation order has a least pointed layer.  Two other layers are
    comparable only when they have the same shape, after which their recursive
    positions are compared pointwise.  The two constructors intentionally
    overlap at the bottom shape; this keeps the relation independent of shape
    equality and does not change which values are related. *)
Inductive mu_le (C : pointed_container) :
  mu (pc_container C) -> mu (pc_container C) -> Prop :=
| mu_le_bottom : forall children y,
    mu_le C (in_mu (bottom_shape C) children) y
| mu_le_same : forall s children1 children2,
    (forall p, mu_le C (children1 p) (children2 p)) ->
    mu_le C (in_mu s children1) (in_mu s children2).

Arguments mu_le_bottom {C} children y.
Arguments mu_le_same {C} s children1 children2 children_le.

CoInductive nu_le (C : pointed_container) :
  nu (pc_container C) -> nu (pc_container C) -> Prop :=
| nu_le_bottom : forall children y,
    nu_le C (in_nu (bottom_shape C) children) y
| nu_le_same : forall s children1 children2,
    (forall p, nu_le C (children1 p) (children2 p)) ->
    nu_le C (in_nu s children1) (in_nu s children2).

Arguments nu_le_bottom {C} children y.
Arguments nu_le_same {C} s children1 children2 children_le.

Lemma mu_le_refl {C : pointed_container} (x : mu (pc_container C)) :
  mu_le C x x.
Proof.
  induction x as [s children IH].
  constructor; exact IH.
Qed.

Lemma mu_le_trans {C : pointed_container}
  (x y z : mu (pc_container C)) :
  mu_le C x y -> mu_le C y z -> mu_le C x z.
Proof.
  intro Hxy; revert z.
  induction Hxy as [children y | s children1 children2 Hchildren IH].
  - intros z Hyz; constructor.
  - intros z Hyz; dependent destruction Hyz.
    + constructor.
    + constructor; intro p; eapply IH; eauto.
Qed.

Lemma nu_le_refl {C : pointed_container} (x : nu (pc_container C)) :
  nu_le C x x.
Proof.
  revert x; cofix CH; intros [s children].
  constructor; intro p; apply CH.
Qed.

Lemma nu_le_trans {C : pointed_container}
  (x y z : nu (pc_container C)) :
  nu_le C x y -> nu_le C y z -> nu_le C x z.
Proof.
  revert x y z; cofix CH; intros x y z Hxy Hyz.
  destruct Hxy as [children y | s children1 children2 Hchildren12].
  - constructor.
  - dependent destruction Hyz.
    + constructor.
    + constructor; intro p; eapply CH; eauto.
Qed.

#[global]
Instance Reflexive_mu_le (C : pointed_container) : Reflexive (mu_le C).
Proof. intro x; apply mu_le_refl. Qed.

#[global]
Instance Transitive_mu_le (C : pointed_container) : Transitive (mu_le C).
Proof. intros x y z; apply mu_le_trans. Qed.

#[global]
Instance PreOrder_mu_le (C : pointed_container) : PreOrder (mu_le C).
Proof. constructor; typeclasses eauto. Qed.

#[global]
Instance OType_container_mu (C : pointed_container) :
  OType (mu (pc_container C)) :=
  {| leq := mu_le C |}.

#[global]
Instance PType_container_mu (C : pointed_container) :
  PType (mu (pc_container C)).
Proof.
  refine {| bot := mu_bottom C |}.
  intro x; unfold mu_bottom; constructor.
Defined.

#[global]
Instance Reflexive_nu_le (C : pointed_container) : Reflexive (nu_le C).
Proof. intro x; apply nu_le_refl. Qed.

#[global]
Instance Transitive_nu_le (C : pointed_container) : Transitive (nu_le C).
Proof. intros x y z; apply nu_le_trans. Qed.

#[global]
Instance PreOrder_nu_le (C : pointed_container) : PreOrder (nu_le C).
Proof. constructor; typeclasses eauto. Qed.

#[global]
Instance OType_container_nu (C : pointed_container) :
  OType (nu (pc_container C)) :=
  {| leq := nu_le C |}.

#[global]
Instance PType_container_nu (C : pointed_container) :
  PType (nu (pc_container C)).
Proof.
  refine {| bot := nu_bottom C |}.
  intro x; unfold nu_bottom; constructor.
Defined.

(** Structurally include a finite basis element into the coinductive value
    type. *)
Fixpoint incl_mu {C : pointed_container} (x : mu (pc_container C)) :
  nu (pc_container C) :=
  match x with
  | in_mu s children => in_nu s (fun p => incl_mu (children p))
  end.

(** Observe at most [n] layers.  Depth zero is the descriptor's distinguished
    approximation hole. *)
Fixpoint truncate_nu {C : pointed_container} (n : nat)
  (x : nu (pc_container C)) : mu (pc_container C) :=
  match n with
  | O => mu_bottom C
  | S n' =>
      match x with
      | in_nu s children => in_mu s (fun p => truncate_nu n' (children p))
      end
  end.

Lemma incl_mu_monotone {C : pointed_container}
  (x y : mu (pc_container C)) :
  mu_le C x y -> nu_le C (incl_mu x) (incl_mu y).
Proof.
  intro Hxy.
  induction Hxy as [children y | s children1 children2 Hchildren IH].
  - simpl; constructor.
  - simpl; constructor; exact IH.
Qed.

Lemma incl_mu_reflects {C : pointed_container}
  (x y : mu (pc_container C)) :
  nu_le C (incl_mu x) (incl_mu y) -> mu_le C x y.
Proof.
  revert y.
  induction x as [sx childrenx IH]; intros [sy childreny] Hxy; simpl in Hxy.
  dependent destruction Hxy.
  - constructor.
  - constructor; intro p; apply IH, H.
Qed.

Theorem incl_mu_order_iff {C : pointed_container}
  (x y : mu (pc_container C)) :
  mu_le C x y <-> nu_le C (incl_mu x) (incl_mu y).
Proof. split; [apply incl_mu_monotone | apply incl_mu_reflects]. Qed.

Lemma truncate_nu_monotone {C : pointed_container} (n : nat)
  (x y : nu (pc_container C)) :
  nu_le C x y -> mu_le C (truncate_nu n x) (truncate_nu n y).
Proof.
  revert x y; induction n as [|n IH]; intros x y Hxy; simpl.
  - constructor.
  - destruct Hxy as [children y | s children1 children2 Hchildren].
    + constructor.
    + constructor; intro p; apply IH, Hchildren.
Qed.

Lemma truncate_nu_step {C : pointed_container} (n : nat)
  (x : nu (pc_container C)) :
  mu_le C (truncate_nu n x) (truncate_nu (S n) x).
Proof.
  revert x; induction n as [|n IH]; intros x; simpl.
  - constructor.
  - destruct x as [s children]; constructor; intro p; apply IH.
Qed.

Lemma incl_truncate_nu_le {C : pointed_container} (n : nat)
  (x : nu (pc_container C)) :
  nu_le C (incl_mu (truncate_nu n x)) x.
Proof.
  revert x; induction n as [|n IH]; intros x; simpl.
  - constructor.
  - destruct x as [s children]; constructor; intro p; apply IH.
Qed.

Lemma chain_truncate_nu {C : pointed_container}
  (x : nu (pc_container C)) :
  chain (fun n => truncate_nu n x).
Proof. intro n; apply truncate_nu_step. Qed.

Lemma chain_incl_truncate_nu {C : pointed_container}
  (x : nu (pc_container C)) :
  chain (fun n => incl_mu (truncate_nu n x)).
Proof. intro n; apply incl_mu_monotone, truncate_nu_step. Qed.

Lemma truncate_incl_mu_le {C : pointed_container} (n : nat)
  (x : mu (pc_container C)) :
  mu_le C (truncate_nu n (incl_mu x)) x.
Proof.
  apply incl_mu_reflects, incl_truncate_nu_le.
Qed.
