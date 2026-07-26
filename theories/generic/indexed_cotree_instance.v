(** * Descriptor-indexed wrapper specialization for Boolean cotrees. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  List
.

From algco Require Import
  aCPO
  cotree
  cpo
  order
.

From algco.generic Require Import
  cotree_instance
  indexed_container
  pointed_container
  scott_container
.

(** As for colists, the specialization registers only capabilities of the
    stable descriptor. *)
#[global]
Instance DecidableBottom_cotree (A : Type) :
  DecidableBottom (cotree_pointed_container A).
Proof.
  constructor; exact (@cotree_bottom_shape_dec A).
Defined.

#[global]
Instance FinitePositions_cotree (A : Type) :
  FinitePositions (cotree_pointed_container A).
Proof.
  exact
    (@Build_FinitePositions (cotree_pointed_container A)
      (@cotree_position_enum A) (@cotree_position_enum_complete A)).
Defined.

Definition indexed_cotree_basis (A : Type) : Type :=
  Basis (cotree_pointed_container A).

Definition indexed_cotree_value (A : Type) : Type :=
  Value (cotree_pointed_container A).

(** Native conversions cross the wrapper at the specialization boundary. *)
Definition atree_to_indexed_basis {A : Type} (t : atree bool A) :
  indexed_cotree_basis A :=
  @Build_Basis (cotree_pointed_container A) (atree_to_mu t).

Definition indexed_basis_to_atree {A : Type}
  (x : indexed_cotree_basis A) : atree bool A :=
  mu_to_atree (basis_carrier x).

Lemma monotone_indexed_basis_to_atree {A : Type} :
  monotone (@indexed_basis_to_atree A).
Proof.
  intros [x] [y] Hxy; apply mu_le_to_atree_le; exact Hxy.
Qed.

Definition cotree_to_indexed_value {A : Type} (t : cotree bool A) :
  indexed_cotree_value A :=
  @Build_Value (cotree_pointed_container A) (cotree_to_nu t).

Definition indexed_value_to_cotree {A : Type}
  (x : indexed_cotree_value A) : cotree bool A :=
  nu_to_cotree (value_carrier x).

(** Native cotrees and the indexed value carrier have the same approximation
    order.  The bridge uses coinductive equivalence rather than [cotree_ext],
    so continuity does not acquire an unnecessary equality axiom. *)
Lemma monotone_cotree_to_indexed_value {A : Type} :
  monotone (@cotree_to_indexed_value A).
Proof.
  intros x y Hxy.
  change
    (nu_le (cotree_pointed_container A) (cotree_to_nu x) (cotree_to_nu y)).
  apply cotree_le_to_nu_le.
  pose proof (@nu_to_cotree_cotree_to_nu A x) as Hx.
  pose proof (@nu_to_cotree_cotree_to_nu A y) as Hy.
  apply cotree_eq_equ in Hx; apply cotree_eq_equ in Hy.
  destruct Hx as [Hcx _]; destruct Hy as [_ Hyc].
  etransitivity; [exact Hcx |].
  etransitivity; [exact Hxy | exact Hyc].
Qed.

Lemma continuous_cotree_to_indexed_value {A : Type} :
  continuous (@cotree_to_indexed_value A).
Proof.
  intros d Hdirected limit Hsup; split.
  - intro i; apply monotone_cotree_to_indexed_value, (proj1 Hsup).
  - intros [ub] Hub.
    change
      (nu_le (cotree_pointed_container A) (cotree_to_nu limit) ub).
    apply cotree_le_to_nu_le.
    pose proof (@nu_to_cotree_cotree_to_nu A limit) as Hlimit.
    apply cotree_eq_equ in Hlimit; destruct Hlimit as [Hconverted _].
    etransitivity; [exact Hconverted |].
    apply (proj2 Hsup); intro i.
    specialize (Hub i).
    change
      (nu_le (cotree_pointed_container A) (cotree_to_nu (d i)) ub)
      in Hub.
    apply nu_le_to_cotree_le in Hub.
    pose proof (@nu_to_cotree_cotree_to_nu A (d i)) as Hi.
    apply cotree_eq_equ in Hi; destruct Hi as [_ Hnative].
    etransitivity; [exact Hnative | exact Hub].
Qed.

Lemma indexed_basis_to_atree_to_basis {A : Type} (t : atree bool A) :
  indexed_basis_to_atree (atree_to_indexed_basis t) = t.
Proof. apply mu_to_atree_atree_to_mu. Qed.

Lemma atree_to_indexed_basis_to_atree {A : Type}
  (x : indexed_cotree_basis A) :
  atree_to_indexed_basis (indexed_basis_to_atree x) = x.
Proof.
  destruct x as [x]; unfold atree_to_indexed_basis, indexed_basis_to_atree.
  f_equal; apply atree_to_mu_mu_to_atree.
Qed.

Lemma indexed_value_to_cotree_to_value {A : Type} (t : cotree bool A) :
  indexed_value_to_cotree (cotree_to_indexed_value t) = t.
Proof. apply nu_to_cotree_cotree_to_nu_eq. Qed.

(** Generic inclusion and ideal expose the native finite-tree operations. *)
Lemma indexed_value_to_cotree_incl_atree {A : Type}
  (t : atree bool A) :
  indexed_value_to_cotree (incl (atree_to_indexed_basis t)) = tinj t.
Proof.
  change
    (nu_to_cotree
      (incl_mu (C := cotree_pointed_container A) (atree_to_mu t)) =
    tinj t).
  rewrite nu_to_cotree_incl_mu, mu_to_atree_atree_to_mu; reflexivity.
Qed.

Lemma indexed_basis_to_atree_ideal_cotree {A : Type}
  (n : nat) (t : cotree bool A) :
  indexed_basis_to_atree (ideal (cotree_to_indexed_value t) n) =
  tprefix n t.
Proof. apply mu_to_atree_truncate_cotree. Qed.

Corollary indexed_incl_atree_scott_compact {A : Type}
  (t : atree bool A) :
  scott_compact (incl (atree_to_indexed_basis t)).
Proof.
  change (scott_compact (basis_incl (atree_to_indexed_basis t))).
  apply basis_incl_scott_compact; typeclasses eauto.
Qed.

(** No concrete wrapper algebraicity instance is declared here. *)
Example indexed_cotree_basis_pointed_resolves (A : Type) :
  PType (Basis (cotree_pointed_container A)).
Proof. typeclasses eauto. Qed.

Example indexed_cotree_value_pointed_resolves (A : Type) :
  PType (Value (cotree_pointed_container A)).
Proof. typeclasses eauto. Qed.

Example indexed_cotree_acpo_resolves (A : Type) :
  aCPO
    (Value (cotree_pointed_container A))
    (Basis (cotree_pointed_container A)).
Proof. typeclasses eauto. Qed.
