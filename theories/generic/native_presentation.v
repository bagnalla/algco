(** * Native presentations of indexed container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
  Morphisms
.

From algco Require Import
  order
.

From algco.generic Require Import
  container
  indexed_container
  indexed_fold
  pointed_container
  scott_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

(** Container bisimilarity implies mutual approximation for every choice of
    pointed shape.  Native specializations already prove their generic value
    round trips by bisimulation, so this bridge keeps those presentation laws
    independent of equality axioms. *)
Lemma nu_equiv_nu_le {S : pointed_container}
  (x y : nu (pc_container S)) :
  nu_equiv x y -> nu_le S x y.
Proof.
  revert x y; cofix CH; intros x y Hxy.
  destruct Hxy as [s children1 children2 Hchildren].
  constructor; intro p; apply CH, Hchildren.
Qed.

Lemma value_equiv_of_nu_equiv {S : pointed_container} (x y : Value S) :
  nu_equiv (value_carrier x) (value_carrier y) -> x === y.
Proof.
  intro Hxy; split; apply nu_equiv_nu_le.
  - exact Hxy.
  - apply nu_equiv_sym; exact Hxy.
Qed.

(** Basis and value presentations are deliberately separate.  A basis
    round-trip proof for a function-branching inductive tree may use
    functional extensionality, while the value-order bridge does not.  A
    combined proof record would make that basis assumption appear in every
    theorem using only the value projection. *)
Record NativeBasisPresentation
  (S : pointed_container) (NativeBasis : Type) `{OType NativeBasis} : Type :=
  { native_basis_to : NativeBasis -> Basis S
  ; native_basis_from : Basis S -> NativeBasis
  ; native_basis_roundtrip : forall b,
      native_basis_from (native_basis_to b) === b
  ; indexed_basis_order_iff : forall x y,
      x ⊑ y <-> native_basis_from x ⊑ native_basis_from y
  }.

Arguments NativeBasisPresentation S NativeBasis {H}.
Arguments native_basis_to {S NativeBasis H} _ _.
Arguments native_basis_from {S NativeBasis H} _ _.
Arguments native_basis_roundtrip {S NativeBasis H} _ _.
Arguments indexed_basis_order_iff {S NativeBasis H} _ _ _.

Section BasisPresentationConsequences.
  Context {S : pointed_container} {NativeBasis : Type}.
  Context `{OType NativeBasis}.
  Variable P : NativeBasisPresentation S NativeBasis.

  Lemma monotone_native_basis_from : monotone (native_basis_from P).
  Proof.
    intros x y Hxy.
    apply (proj1 (indexed_basis_order_iff P x y)); exact Hxy.
  Qed.

  Lemma indexed_basis_roundtrip (x : Basis S) :
    native_basis_to P (native_basis_from P x) === x.
  Proof.
    split; apply (proj2 (indexed_basis_order_iff P _ _)).
    - exact (proj1 (native_basis_roundtrip P (native_basis_from P x))).
    - exact (proj2 (native_basis_roundtrip P (native_basis_from P x))).
  Qed.

  Lemma native_basis_below_iff (b : NativeBasis) (x : Basis S) :
    native_basis_to P b ⊑ x <-> b ⊑ native_basis_from P x.
  Proof.
    split; intro Hbelow.
    - etransitivity.
      + exact (proj2 (native_basis_roundtrip P b)).
      + apply (proj1 (indexed_basis_order_iff P _ _)); exact Hbelow.
    - apply (proj2 (indexed_basis_order_iff P _ _)).
      etransitivity.
      + exact (proj1 (native_basis_roundtrip P b)).
      + exact Hbelow.
  Qed.

  Lemma monotone_native_basis_to : monotone (native_basis_to P).
  Proof.
    intros x y Hxy.
    apply (proj2
      (native_basis_below_iff x (x := native_basis_to P y))).
    etransitivity; [exact Hxy |].
    exact (proj2 (native_basis_roundtrip P y)).
  Qed.

  Lemma native_basis_to_order_iff (x y : NativeBasis) :
    x ⊑ y <-> native_basis_to P x ⊑ native_basis_to P y.
  Proof.
    split.
    - apply monotone_native_basis_to.
    - intro Hxy.
      etransitivity.
      + exact (proj2 (native_basis_roundtrip P x)).
      + etransitivity.
        * apply monotone_native_basis_from; exact Hxy.
        * exact (proj1 (native_basis_roundtrip P y)).
  Qed.
End BasisPresentationConsequences.

(** The value presentation contains only the laws needed to transport order
    and suprema.  Round trips use preorder equivalence rather than Coq
    equality, so no native coinductive extensionality axiom is required. *)
Record NativeValuePresentation
  (S : pointed_container) (NativeValue : Type) `{OType NativeValue} : Type :=
  { native_value_to : NativeValue -> Value S
  ; native_value_from : Value S -> NativeValue
  ; native_value_roundtrip : forall v,
      native_value_from (native_value_to v) === v
  ; indexed_value_order_iff : forall x y,
      x ⊑ y <-> native_value_from x ⊑ native_value_from y
  }.

Arguments NativeValuePresentation S NativeValue {H}.
Arguments native_value_to {S NativeValue H} _ _.
Arguments native_value_from {S NativeValue H} _ _.
Arguments native_value_roundtrip {S NativeValue H} _ _.
Arguments indexed_value_order_iff {S NativeValue H} _ _ _.

Section ValuePresentationConsequences.
  Context {S : pointed_container} {NativeValue : Type}.
  Context `{OType NativeValue}.
  Variable P : NativeValuePresentation S NativeValue.

  Lemma monotone_native_value_from : monotone (native_value_from P).
  Proof.
    intros x y Hxy.
    apply (proj1 (indexed_value_order_iff P x y)); exact Hxy.
  Qed.

  Lemma indexed_value_roundtrip (x : Value S) :
    native_value_to P (native_value_from P x) === x.
  Proof.
    split; apply (proj2 (indexed_value_order_iff P _ _)).
    - exact (proj1 (native_value_roundtrip P (native_value_from P x))).
    - exact (proj2 (native_value_roundtrip P (native_value_from P x))).
  Qed.

  Lemma native_value_below_iff (v : NativeValue) (x : Value S) :
    native_value_to P v ⊑ x <-> v ⊑ native_value_from P x.
  Proof.
    split; intro Hbelow.
    - etransitivity.
      + exact (proj2 (native_value_roundtrip P v)).
      + apply (proj1 (indexed_value_order_iff P _ _)); exact Hbelow.
    - apply (proj2 (indexed_value_order_iff P _ _)).
      etransitivity.
      + exact (proj1 (native_value_roundtrip P v)).
      + exact Hbelow.
  Qed.

  Lemma monotone_native_value_to : monotone (native_value_to P).
  Proof.
    intros x y Hxy.
    apply (proj2
      (native_value_below_iff x (x := native_value_to P y))).
    etransitivity; [exact Hxy |].
    exact (proj2 (native_value_roundtrip P y)).
  Qed.

  Lemma native_value_to_order_iff (x y : NativeValue) :
    x ⊑ y <-> native_value_to P x ⊑ native_value_to P y.
  Proof.
    split.
    - apply monotone_native_value_to.
    - intro Hxy.
      etransitivity.
      + exact (proj2 (native_value_roundtrip P x)).
      + etransitivity.
        * apply monotone_native_value_from; exact Hxy.
        * exact (proj1 (native_value_roundtrip P y)).
  Qed.

  (** The mixed below law transports arbitrary supplied suprema, not merely
      the canonical omega-chain used by [co]. *)
  Lemma native_value_to_preserves_supremum {I : Type}
    (d : I -> NativeValue) (limit : NativeValue) :
    supremum limit d ->
    supremum (native_value_to P limit) (native_value_to P ∘ d).
  Proof.
    intros [Hub Hleast]; split.
    - intro i; apply monotone_native_value_to, Hub.
    - intros ub Hub_to.
      apply (proj2 (native_value_below_iff limit (x := ub))).
      apply Hleast; intro i.
      apply (proj1 (native_value_below_iff (d i) (x := ub))).
      apply Hub_to.
  Qed.

  Corollary continuous_native_value_to : continuous (native_value_to P).
  Proof.
    intros d Hdirected limit Hsup.
    apply native_value_to_preserves_supremum; exact Hsup.
  Qed.

  (** Standard Scott compactness is invariant under the presented order
      equivalence.  This proof works for arbitrary inhabited directed
      families, independently of the sequence-based [continuous] corollary. *)
  Lemma native_value_from_scott_compact (x : Value S) :
    scott_compact x -> scott_compact (native_value_from P x).
  Proof.
    intros Hcompact I d Hinhabited Hdirected limit Hsup Hbelow.
    assert (Hdirected_to : directed (native_value_to P ∘ d)).
    {
      intros i j.
      destruct (Hdirected i j) as [k [Hik Hjk]].
      exists k; split; apply monotone_native_value_to; assumption.
    }
    assert (Hsup_to :
      supremum (native_value_to P limit) (native_value_to P ∘ d)).
    {
      apply native_value_to_preserves_supremum; exact Hsup.
    }
    assert (Hxlimit : x ⊑ native_value_to P limit).
    {
      etransitivity.
      - exact (proj2 (indexed_value_roundtrip (x := x))).
      - apply monotone_native_value_to; exact Hbelow.
    }
    destruct
      (Hcompact I (native_value_to P ∘ d) Hinhabited Hdirected_to
        (native_value_to P limit) Hsup_to Hxlimit) as [i Hi].
    exists i.
    etransitivity.
    - apply monotone_native_value_from; exact Hi.
    - exact (proj1 (native_value_roundtrip P (d i))).
  Qed.
End ValuePresentationConsequences.

(** An umbrella package is useful as data, but generic theorems intentionally
    consume its basis or value part separately to preserve assumption
    locality. *)
Record NativePresentation
  (S : pointed_container) (NativeBasis NativeValue : Type)
  `{OType NativeBasis} `{OType NativeValue} : Type :=
  { native_basis_presentation : NativeBasisPresentation S NativeBasis
  ; native_value_presentation : NativeValuePresentation S NativeValue
  }.

Arguments NativePresentation S NativeBasis NativeValue {H H0}.

(** Exact native approximation operations are kept outside the order core.
    Their equations are useful as rewrite rules, but a branching native type
    may need functional extensionality to prove them.  Keeping them in this
    extension prevents that assumption from leaking into conversion
    continuity. *)
Record NativeApproximation
  (S : pointed_container) (NativeBasis NativeValue : Type)
  `{OType NativeBasis} `{OType NativeValue}
  (BP : NativeBasisPresentation S NativeBasis)
  (VP : NativeValuePresentation S NativeValue) : Type :=
  { native_inclusion : NativeBasis -> NativeValue
  ; native_truncation : nat -> NativeValue -> NativeBasis
  ; native_inclusion_commutes : forall b,
      native_value_from VP (basis_incl (native_basis_to BP b)) =
      native_inclusion b
  ; native_truncation_commutes : forall n v,
      native_basis_from BP (value_ideal (native_value_to VP v) n) =
      native_truncation n v
  }.

Arguments NativeApproximation
  S NativeBasis NativeValue {H H0} BP VP.

Arguments native_inclusion
  {S NativeBasis NativeValue H H0 BP VP} _ _.
Arguments native_truncation
  {S NativeBasis NativeValue H H0 BP VP} _ _ _.

Section ApproximationConsequences.
  Context {S : pointed_container} {NativeBasis NativeValue : Type}.
  Context `{OType NativeBasis} `{OType NativeValue}.
  Variable BP : NativeBasisPresentation S NativeBasis.
  Variable VP : NativeValuePresentation S NativeValue.
  Variable A : NativeApproximation S NativeBasis NativeValue BP VP.

  Lemma native_truncation_chain (v : NativeValue) :
    chain (fun n => native_truncation A n v).
  Proof.
    intro n.
    rewrite <- (native_truncation_commutes A n v).
    rewrite <- (native_truncation_commutes A (Datatypes.S n) v).
    apply monotone_native_basis_from.
    apply chain_value_ideal.
  Qed.

  Theorem native_inclusion_scott_compact
    `{DecidableBottom S} `{FinitePositions S} (b : NativeBasis) :
    scott_compact (native_inclusion A b).
  Proof.
    rewrite <- native_inclusion_commutes.
    apply native_value_from_scott_compact.
    exact (@basis_incl_scott_compact S _ _ (native_basis_to BP b)).
  Qed.
End ApproximationConsequences.
