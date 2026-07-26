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
  pointed_container
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

Lemma monotone_indexed_basis_to_list {A : Type} :
  monotone (@indexed_basis_to_list A).
Proof.
  intros [x] [y] Hxy; apply mu_le_to_list_le; exact Hxy.
Qed.

Definition colist_to_indexed_value {A : Type} (l : colist A) :
  indexed_colist_value A :=
  @Build_Value (colist_pointed_container A) (colist_to_nu l).

Definition indexed_value_to_colist {A : Type} (x : indexed_colist_value A) :
  colist A :=
  nu_to_colist (value_carrier x).

(** The native-to-indexed conversion is an order embedding and preserves the
    sequential suprema used by [co].  These lemmas are part of the one-time
    specialization boundary rather than obligations for each operation. *)
Lemma monotone_colist_to_indexed_value {A : Type} :
  monotone (@colist_to_indexed_value A).
Proof.
  intros x y Hxy.
  change
    (nu_le (colist_pointed_container A) (colist_to_nu x) (colist_to_nu y)).
  apply colist_le_to_nu_le.
  pose proof (@nu_to_colist_colist_to_nu A x) as Hx.
  pose proof (@nu_to_colist_colist_to_nu A y) as Hy.
  apply colist_eq_equ in Hx; apply colist_eq_equ in Hy.
  destruct Hx as [Hcx _]; destruct Hy as [_ Hyc].
  etransitivity; [exact Hcx |].
  etransitivity; [exact Hxy | exact Hyc].
Qed.

Lemma continuous_colist_to_indexed_value {A : Type} :
  continuous (@colist_to_indexed_value A).
Proof.
  intros d Hdirected limit Hsup; split.
  - intro i; apply monotone_colist_to_indexed_value, (proj1 Hsup).
  - intros [ub] Hub.
    change
      (nu_le (colist_pointed_container A) (colist_to_nu limit) ub).
    apply colist_le_to_nu_le.
    pose proof (@nu_to_colist_colist_to_nu A limit) as Hlimit.
    apply colist_eq_equ in Hlimit; destruct Hlimit as [Hconverted _].
    etransitivity; [exact Hconverted |].
    apply (proj2 Hsup); intro i.
    specialize (Hub i).
    change
      (nu_le (colist_pointed_container A) (colist_to_nu (d i)) ub)
      in Hub.
    apply nu_le_to_colist_le in Hub.
    pose proof (@nu_to_colist_colist_to_nu A (d i)) as Hi.
    apply colist_eq_equ in Hi; destruct Hi as [_ Hnative].
    etransitivity; [exact Hnative | exact Hub].
Qed.

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
