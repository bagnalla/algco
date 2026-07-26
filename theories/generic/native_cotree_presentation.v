(** * Native presentation of descriptor-indexed Boolean cotrees. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
.

From algco Require Import
  cotree
  order
.

From algco.generic Require Import
  cotree_instance
  indexed_cotree_instance
  native_presentation
  pointed_container
  scott_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.

Definition cotree_native_basis_presentation (A : Type) :
  NativeBasisPresentation (cotree_pointed_container A) (atree bool A).
Proof.
  refine
    {| native_basis_to := @atree_to_indexed_basis A
     ; native_basis_from := @indexed_basis_to_atree A
    |}.
  - intro t.
    rewrite indexed_basis_to_atree_to_basis; reflexivity.
  - intros [x] [y].
    apply mu_le_iff_atree_le.
Defined.

Arguments cotree_native_basis_presentation A : clear implicits.

Definition cotree_native_value_presentation (A : Type) :
  NativeValuePresentation (cotree_pointed_container A) (cotree bool A).
Proof.
  refine
    {| native_value_to := @cotree_to_indexed_value A
     ; native_value_from := @indexed_value_to_cotree A
    |}.
  - intro t.
    apply cotree_eq_equ, nu_to_cotree_cotree_to_nu.
  - intros [x] [y].
    apply nu_le_iff_cotree_le.
Defined.

Arguments cotree_native_value_presentation A : clear implicits.

Definition cotree_native_presentation (A : Type) :
  NativePresentation
    (cotree_pointed_container A) (atree bool A) (cotree bool A) :=
  {| native_basis_presentation := cotree_native_basis_presentation A
   ; native_value_presentation := cotree_native_value_presentation A
  |}.

Arguments cotree_native_presentation A : clear implicits.

Definition cotree_native_approximation (A : Type) :
  NativeApproximation
    (cotree_pointed_container A) (atree bool A) (cotree bool A)
    (cotree_native_basis_presentation A)
    (cotree_native_value_presentation A).
Proof.
  refine
    {| native_inclusion := @tinj bool A
     ; native_truncation := @tprefix bool A
    |}.
  - apply indexed_value_to_cotree_incl_atree.
  - apply indexed_basis_to_atree_ideal_cotree.
Defined.

Arguments cotree_native_approximation A : clear implicits.

Corollary presented_monotone_indexed_basis_to_atree {A : Type} :
  monotone (@indexed_basis_to_atree A).
Proof.
  exact
    (@monotone_native_basis_from
      (cotree_pointed_container A) (atree bool A) _
      (cotree_native_basis_presentation A)).
Qed.

Corollary presented_monotone_cotree_to_indexed_value {A : Type} :
  monotone (@cotree_to_indexed_value A).
Proof.
  exact
    (@monotone_native_value_to
      (cotree_pointed_container A) (cotree bool A) _
      (cotree_native_value_presentation A)).
Qed.

Corollary presented_continuous_cotree_to_indexed_value {A : Type} :
  continuous (@cotree_to_indexed_value A).
Proof.
  exact
    (@continuous_native_value_to
      (cotree_pointed_container A) (cotree bool A) _
      (cotree_native_value_presentation A)).
Qed.

Corollary presented_tprefix_chain {A : Type} (t : cotree bool A) :
  chain (fun n => tprefix n t).
Proof.
  exact
    (@native_truncation_chain
      (cotree_pointed_container A) (atree bool A) (cotree bool A) _ _
      (cotree_native_basis_presentation A)
      (cotree_native_value_presentation A)
      (cotree_native_approximation A) t).
Qed.

Corollary presented_tinj_scott_compact {A : Type} (t : atree bool A) :
  scott_compact (tinj t).
Proof.
  exact
    (@native_inclusion_scott_compact
      (cotree_pointed_container A) (atree bool A) (cotree bool A) _ _
      (cotree_native_basis_presentation A)
      (cotree_native_value_presentation A)
      (cotree_native_approximation A)
      (@DecidableBottom_cotree A) (@FinitePositions_cotree A) t).
Qed.
