(** * Container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Program.Equality
.

(** A container describes one strictly positive layer by its constructor
    shapes and the recursive positions belonging to each shape. *)
Record container : Type :=
  { shape : Type
  ; position : shape -> Type
  }.

Definition extension (C : container) (X : Type) : Type :=
  { s : shape C & position C s -> X }.

Definition extension_map {C : container} {A B : Type}
  (f : A -> B) (layer : extension C A) : extension C B :=
  match layer with
  | existT _ s children => existT _ s (fun p => f (children p))
  end.

(** The initial-algebra carrier of a container. *)
Inductive mu (C : container) : Type :=
| in_mu : forall s : shape C, (position C s -> mu C) -> mu C.

Arguments in_mu {C} s children.

(** The final-coalgebra carrier intended by a container.  Its universal
    property is not asserted here; [nu_equiv] below is its structural
    bisimilarity. *)
CoInductive nu (C : container) : Type :=
| in_nu : forall s : shape C, (position C s -> nu C) -> nu C.

Arguments in_nu {C} s children.

Definition out_mu {C : container} (x : mu C) : extension C (mu C) :=
  match x with
  | in_mu s children => existT _ s children
  end.

Definition out_nu {C : container} (x : nu C) : extension C (nu C) :=
  match x with
  | in_nu s children => existT _ s children
  end.

Definition unfold_nu {C : container} (x : nu C) : nu C :=
  match x with
  | in_nu s children => in_nu s children
  end.

Lemma unfold_nu_eq {C : container} (x : nu C) :
  x = unfold_nu x.
Proof. destruct x; reflexivity. Qed.

(** Two generic coinductive values are bisimilar when they expose the same
    shape and have pointwise bisimilar recursive children. *)
CoInductive nu_equiv {C : container} : nu C -> nu C -> Prop :=
| nu_equiv_in : forall s children1 children2,
    (forall p, nu_equiv (children1 p) (children2 p)) ->
    nu_equiv (in_nu s children1) (in_nu s children2).

Lemma nu_equiv_refl {C : container} (x : nu C) :
  nu_equiv x x.
Proof.
  revert x; cofix CH; intros [s children].
  constructor; intro p; apply CH.
Qed.

Lemma nu_equiv_sym {C : container} (x y : nu C) :
  nu_equiv x y ->
  nu_equiv y x.
Proof.
  revert x y; cofix CH; intros x y Hxy.
  destruct Hxy as [s children1 children2 Hchildren].
  constructor; intro p; apply CH, Hchildren.
Qed.

Lemma nu_equiv_trans {C : container} (x y z : nu C) :
  nu_equiv x y ->
  nu_equiv y z ->
  nu_equiv x z.
Proof.
  revert x y z; cofix CH; intros x y z Hxy Hyz.
  destruct Hxy as [s children1 children2 Hchildren12].
  dependent destruction Hyz.
  constructor; intro p.
  eapply CH; eauto.
Qed.
