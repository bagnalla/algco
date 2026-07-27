(** * Compositional constructors for finitary containers. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  List
.

Import ListNotations.

From algco.generic Require Import
  container
  finitary_container
  pointed_container
.

(** A finite recursive index is explicit data rather than a typeclass.  This
    keeps the computational enumeration chosen by a signature visible and
    avoids global search for finiteness evidence. *)
Record finite_index : Type :=
  { index_carrier : Type
  ; index_enumeration : list index_carrier
  ; index_enumeration_complete : forall i, In i index_enumeration
  }.

Definition unit_index : finite_index.
Proof.
  refine
    {| index_carrier := unit
     ; index_enumeration := [tt]
    |}.
  intros []; simpl; auto.
Defined.

Definition bool_index : finite_index.
Proof.
  refine
    {| index_carrier := bool
     ; index_enumeration := [false; true]
    |}.
  intros []; simpl; auto.
Defined.

(** These are ordinary semantic container combinators.  There is no syntax
    tree and no interpretation function: each constructor immediately
    returns the container it denotes. *)
Definition constant_container (A : Type) : container :=
  {| shape := A
   ; position := fun _ => Empty_set
  |}.

Definition recursive_container (I : Type) : container :=
  {| shape := unit
   ; position := fun _ => I
  |}.

Definition sum_position (C D : container)
  (s : shape C + shape D) : Type :=
  match s with
  | inl c => position C c
  | inr d => position D d
  end.

Definition sum_container (C D : container) : container :=
  {| shape := shape C + shape D
   ; position := sum_position C D
  |}.

Definition product_position (C D : container)
  (s : shape C * shape D) : Type :=
  position C (fst s) + position D (snd s).

Definition product_container (C D : container) : container :=
  {| shape := shape C * shape D
   ; position := product_position C D
  |}.

Definition point_position (C : container)
  (s : unit + shape C) : Type :=
  match s with
  | inl _ => Empty_set
  | inr c => position C c
  end.

Definition point_container (C : container) : pointed_container.
Proof.
  refine
    {| pc_container :=
         {| shape := unit + shape C
          ; position := point_position C
         |}
     ; bottom_shape := inl tt
    |}.
  intros p; exact (match p with end).
Defined.

(** The semantic finitary bundle remembers only the position evidence needed
    by the existing compactness construction.  Shapes themselves may be
    infinite: constant payloads never contribute recursive positions. *)
Record finitary_container : Type :=
  { fc_container : container
  ; fc_position_enumeration : forall s : shape fc_container,
      list (position fc_container s)
  ; fc_position_enumeration_complete : forall
      (s : shape fc_container) (p : position fc_container s),
      In p (fc_position_enumeration s)
  }.

Definition finitary_constant (A : Type) : finitary_container.
Proof.
  refine
    {| fc_container := constant_container A
     ; fc_position_enumeration := fun _ => []
    |}.
  intros s p; destruct p.
Defined.

Definition finitary_recursive (I : finite_index) : finitary_container.
Proof.
  refine
    {| fc_container := recursive_container (index_carrier I)
     ; fc_position_enumeration := fun _ => index_enumeration I
    |}.
  intros s p; apply index_enumeration_complete.
Defined.

Definition finitary_sum (C D : finitary_container) : finitary_container.
Proof.
  refine
    {| fc_container := sum_container (fc_container C) (fc_container D)
     ; fc_position_enumeration :=
         fun s =>
           match s as s0
             return list (position
               (sum_container (fc_container C) (fc_container D)) s0)
           with
           | inl c => fc_position_enumeration C c
           | inr d => fc_position_enumeration D d
           end
    |}.
  intros [c | d] p; simpl in *.
  - apply fc_position_enumeration_complete.
  - apply fc_position_enumeration_complete.
Defined.

Definition finitary_product (C D : finitary_container) :
  finitary_container.
Proof.
  refine
    {| fc_container := product_container (fc_container C) (fc_container D)
     ; fc_position_enumeration :=
         fun s =>
           map (@inl
             (position (fc_container C) (fst s))
             (position (fc_container D) (snd s)))
             (fc_position_enumeration C (fst s)) ++
           map (@inr
             (position (fc_container C) (fst s))
             (position (fc_container D) (snd s)))
             (fc_position_enumeration D (snd s))
    |}.
  intros [c d] [p | p]; simpl in *; apply in_or_app.
  - left; apply in_map, fc_position_enumeration_complete.
  - right; apply in_map, fc_position_enumeration_complete.
Defined.

(** Pointing adds the fresh approximation hole used by the partial completion.
    Keeping the finitary input as an argument in the descriptor head lets the
    two generic capability instances resolve without reconstructing a bundle
    from a projected carrier. *)
Definition finitary_point (C : finitary_container) : pointed_container :=
  point_container (fc_container C).

Definition finitary_point_bottom_dec (C : finitary_container)
  (s : shape (pc_container (finitary_point C))) :
  {s = bottom_shape (finitary_point C)} +
  {s <> bottom_shape (finitary_point C)}.
Proof.
  destruct s as [[] | s].
  - left; reflexivity.
  - right; discriminate.
Defined.

Definition finitary_point_position_enumeration (C : finitary_container)
  (s : shape (pc_container (finitary_point C))) :
  list (position (pc_container (finitary_point C)) s) :=
  match s as s0
    return list (position (pc_container (finitary_point C)) s0)
  with
  | inl _ => []
  | inr c => fc_position_enumeration C c
  end.

Lemma finitary_point_position_enumeration_complete
  (C : finitary_container)
  (s : shape (pc_container (finitary_point C)))
  (p : position (pc_container (finitary_point C)) s) :
  In p (@finitary_point_position_enumeration C s).
Proof.
  destruct s as [u | c].
  - destruct p.
  - apply fc_position_enumeration_complete.
Qed.

(** The same evidence can be bundled for clients of the older raw-container
    interface. *)
Definition bundled_finitary_point (C : finitary_container) :
  finitary_pointed_container :=
  {| fpc_decidable :=
       {| dpc_pointed := finitary_point C
        ; bottom_shape_dec := @finitary_point_bottom_dec C
       |}
   ; position_enum := @finitary_point_position_enumeration C
   ; position_enum_complete :=
       @finitary_point_position_enumeration_complete C
  |}.
