(** * Descriptor-indexed wrapper specialization for colists. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  List
.

From algco Require Import
  aCPO
  colist
  cpo
  order
.

From algco.generic Require Import
  indexed_container
  colist_instance
  scott_container
.

(** The specialization registers only capabilities of the stable pointed
    descriptor.  All carrier and algebraicity instances remain generic. *)
#[global]
Instance DecidableBottom_colist (A : Type) :
  DecidableBottom (colist_pointed_container A).
Proof.
  constructor; exact (@colist_bottom_shape_dec A).
Defined.

#[global]
Instance FinitePositions_colist (A : Type) :
  FinitePositions (colist_pointed_container A).
Proof.
  exact
    (@Build_FinitePositions (colist_pointed_container A)
      (@colist_position_enum A) (@colist_position_enum_complete A)).
Defined.

Definition indexed_colist_basis (A : Type) : Type :=
  Basis (colist_pointed_container A).

Definition indexed_colist_value (A : Type) : Type :=
  Value (colist_pointed_container A).

(** Native conversions cross the wrapper exactly once. *)
Definition list_to_indexed_basis {A : Type} (l : list A) :
  indexed_colist_basis A :=
  @Build_Basis (colist_pointed_container A) (list_to_mu l).

Definition indexed_basis_to_list {A : Type} (x : indexed_colist_basis A) :
  list A :=
  mu_to_list (basis_carrier x).

Definition colist_to_indexed_value {A : Type} (l : colist A) :
  indexed_colist_value A :=
  @Build_Value (colist_pointed_container A) (colist_to_nu l).

Definition indexed_value_to_colist {A : Type} (x : indexed_colist_value A) :
  colist A :=
  nu_to_colist (value_carrier x).

Lemma indexed_basis_to_list_to_basis {A : Type} (l : list A) :
  indexed_basis_to_list (list_to_indexed_basis l) = l.
Proof. apply mu_to_list_list_to_mu. Qed.

Lemma list_to_indexed_basis_to_list {A : Type} (x : indexed_colist_basis A) :
  list_to_indexed_basis (indexed_basis_to_list x) = x.
Proof.
  destruct x as [x]; unfold list_to_indexed_basis, indexed_basis_to_list.
  f_equal; apply list_to_mu_mu_to_list.
Qed.

Lemma indexed_value_to_colist_to_value {A : Type} (l : colist A) :
  indexed_value_to_colist (colist_to_indexed_value l) = l.
Proof. apply nu_to_colist_colist_to_nu_eq. Qed.

(** High-level approximation operations compute as their native colist
    counterparts without naming any wrapper instance. *)
Lemma indexed_value_to_colist_incl_list {A : Type} (l : list A) :
  indexed_value_to_colist (incl (list_to_indexed_basis l)) = inj l.
Proof. apply nu_to_colist_incl_list. Qed.

Lemma indexed_basis_to_list_ideal_colist {A : Type}
  (n : nat) (l : colist A) :
  indexed_basis_to_list (ideal (colist_to_indexed_value l) n) =
  prefix n l.
Proof. apply mu_to_list_truncate_colist. Qed.

Corollary indexed_incl_list_scott_compact {A : Type} (l : list A) :
  scott_compact (incl (list_to_indexed_basis l)).
Proof.
  change (scott_compact (basis_incl (list_to_indexed_basis l))).
  apply basis_incl_scott_compact; typeclasses eauto.
Qed.

(** Durable typeclass smoke tests.  No concrete [OType], [Compact], [CPO],
    [Dense], or [aCPO] instance is declared for this specialization. *)
Example indexed_colist_basis_pointed_resolves (A : Type) :
  PType (Basis (colist_pointed_container A)).
Proof. typeclasses eauto. Qed.

Example indexed_colist_value_pointed_resolves (A : Type) :
  PType (Value (colist_pointed_container A)).
Proof. typeclasses eauto. Qed.

Example indexed_colist_acpo_resolves (A : Type) :
  aCPO
    (Value (colist_pointed_container A))
    (Basis (colist_pointed_container A)).
Proof. typeclasses eauto. Qed.
