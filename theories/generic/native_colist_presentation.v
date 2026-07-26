(** * Native presentation of descriptor-indexed colists. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
.

From algco Require Import
  colist
  order
.

From algco.generic Require Import
  colist_instance
  indexed_colist_instance
  native_presentation
  pointed_container
  scott_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.

(** The conversions and datatype-specific order facts are the honest
    presentation obligations.  Conversion monotonicity and continuity are
    deliberately not used to construct these records. *)
Definition colist_native_basis_presentation (A : Type) :
  NativeBasisPresentation (colist_pointed_container A) (list A).
Proof.
  refine
    {| native_basis_to := @list_to_indexed_basis A
     ; native_basis_from := @indexed_basis_to_list A
    |}.
  - intro l.
    rewrite indexed_basis_to_list_to_basis; reflexivity.
  - intros [x] [y].
    apply mu_le_iff_list_le.
Defined.

Arguments colist_native_basis_presentation A : clear implicits.

Definition colist_native_value_presentation (A : Type) :
  NativeValuePresentation (colist_pointed_container A) (colist A).
Proof.
  refine
    {| native_value_to := @colist_to_indexed_value A
     ; native_value_from := @indexed_value_to_colist A
    |}.
  - intro l.
    apply colist_eq_equ, nu_to_colist_colist_to_nu.
  - intros [x] [y].
    apply nu_le_iff_colist_le.
Defined.

Arguments colist_native_value_presentation A : clear implicits.

Definition colist_native_presentation (A : Type) :
  NativePresentation
    (colist_pointed_container A) (list A) (colist A) :=
  {| native_basis_presentation := colist_native_basis_presentation A
   ; native_value_presentation := colist_native_value_presentation A
  |}.

Arguments colist_native_presentation A : clear implicits.

Definition colist_native_approximation (A : Type) :
  NativeApproximation
    (colist_pointed_container A) (list A) (colist A)
    (colist_native_basis_presentation A)
    (colist_native_value_presentation A).
Proof.
  refine
    {| native_inclusion := @inj A
     ; native_truncation := @prefix A
    |}.
  - apply indexed_value_to_colist_incl_list.
  - apply indexed_basis_to_list_ideal_colist.
Defined.

Arguments colist_native_approximation A : clear implicits.

(** The repeated wrapper-level facts are now generic corollaries. *)
Corollary presented_monotone_indexed_basis_to_list {A : Type} :
  monotone (@indexed_basis_to_list A).
Proof.
  exact
    (@monotone_native_basis_from
      (colist_pointed_container A) (list A) _
      (colist_native_basis_presentation A)).
Qed.

Corollary presented_monotone_colist_to_indexed_value {A : Type} :
  monotone (@colist_to_indexed_value A).
Proof.
  exact
    (@monotone_native_value_to
      (colist_pointed_container A) (colist A) _
      (colist_native_value_presentation A)).
Qed.

Corollary presented_continuous_colist_to_indexed_value {A : Type} :
  continuous (@colist_to_indexed_value A).
Proof.
  exact
    (@continuous_native_value_to
      (colist_pointed_container A) (colist A) _
      (colist_native_value_presentation A)).
Qed.

Corollary presented_prefix_chain {A : Type} (l : colist A) :
  chain (fun n => prefix n l).
Proof.
  exact
    (@native_truncation_chain
      (colist_pointed_container A) (list A) (colist A) _ _
      (colist_native_basis_presentation A)
      (colist_native_value_presentation A)
      (colist_native_approximation A) l).
Qed.

Corollary presented_inj_scott_compact {A : Type} (l : list A) :
  scott_compact (inj l).
Proof.
  exact
    (@native_inclusion_scott_compact
      (colist_pointed_container A) (list A) (colist A) _ _
      (colist_native_basis_presentation A)
      (colist_native_value_presentation A)
      (colist_native_approximation A)
      (@DecidableBottom_colist A) (@FinitePositions_colist A) l).
Qed.
