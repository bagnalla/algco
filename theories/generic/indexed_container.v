(** * Descriptor-indexed wrappers for container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  List
.

From algco Require Import
  aCPO
  cpo
  order
.

From algco.generic Require Import
  container
  pointed_container
  finitary_container
  scott_container
  algebraic_container
.

(** The carrier types below retain the pointed descriptor syntactically.
    Additional capabilities are keyed by that descriptor rather than bundled
    into the carrier index. *)
Class DecidableBottom (S : pointed_container) : Type :=
  { decide_bottom_shape : forall s : shape (pc_container S),
      {s = bottom_shape S} + {s <> bottom_shape S}
  }.

Class FinitePositions (S : pointed_container) : Type :=
  { enumerate_positions : forall s : shape (pc_container S),
      list (position (pc_container S) s)
  ; enumerate_positions_complete : forall
      (s : shape (pc_container S)) (p : position (pc_container S) s),
      In p (enumerate_positions s)
  }.

(** Adapters let the wrapper prototype reuse the existing generic proofs
    without changing their bundled interfaces. *)
Definition decidable_container_of (S : pointed_container)
  `{DecidableBottom S} : decidable_pointed_container :=
  {| dpc_pointed := S
   ; bottom_shape_dec := @decide_bottom_shape S _
  |}.

Definition finitary_container_of (S : pointed_container)
  `{DecidableBottom S} `{FinitePositions S} :
  finitary_pointed_container :=
  {| fpc_decidable := @decidable_container_of S _
   ; position_enum := @enumerate_positions S _
   ; position_enum_complete := @enumerate_positions_complete S _
  |}.

(** These are genuine wrappers rather than transparent abbreviations.  The
    descriptor therefore remains visible to unification at the type head. *)
Record Basis (S : pointed_container) : Type :=
  { basis_carrier : mu (pc_container S) }.

Record Value (S : pointed_container) : Type :=
  { value_carrier : nu (pc_container S) }.

Arguments basis_carrier {S} _.
Arguments value_carrier {S} _.

Definition in_basis {S : pointed_container}
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Basis S) : Basis S :=
  {| basis_carrier := in_mu s (fun p => basis_carrier (children p)) |}.

Definition in_value {S : pointed_container}
  (s : shape (pc_container S))
  (children : position (pc_container S) s -> Value S) : Value S :=
  {| value_carrier := in_nu s (fun p => value_carrier (children p)) |}.

Definition basis_le (S : pointed_container) : Basis S -> Basis S -> Prop :=
  fun x y => mu_le S (basis_carrier x) (basis_carrier y).

Definition value_le (S : pointed_container) : Value S -> Value S -> Prop :=
  fun x y => nu_le S (value_carrier x) (value_carrier y).

#[global]
Instance OType_indexed_basis (S : pointed_container) : OType (Basis S).
Proof.
  refine {| leq := @basis_le S |}.
  constructor.
  - intros [x]; apply mu_le_refl.
  - intros [x] [y] [z]; apply mu_le_trans.
Defined.

#[global]
Instance PType_indexed_basis (S : pointed_container) : PType (Basis S).
Proof.
  refine {| bot := {| basis_carrier := mu_bottom S |} |}.
  intros [x]; change (mu_le S (mu_bottom S) x).
  unfold mu_bottom; constructor.
Defined.

#[global]
Instance OType_indexed_value (S : pointed_container) : OType (Value S).
Proof.
  refine {| leq := @value_le S |}.
  constructor.
  - intros [x]; apply nu_le_refl.
  - intros [x] [y] [z]; apply nu_le_trans.
Defined.

#[global]
Instance PType_indexed_value (S : pointed_container) : PType (Value S).
Proof.
  refine {| bot := {| value_carrier := nu_bottom S |} |}.
  intros [x]; change (nu_le S (nu_bottom S) x).
  unfold nu_bottom; constructor.
Defined.

(** Inclusion and canonical finite approximation on the indexed carriers. *)
Definition basis_incl {S : pointed_container} (x : Basis S) : Value S :=
  {| value_carrier := incl_mu (basis_carrier x) |}.

Definition value_ideal {S : pointed_container} (x : Value S) (n : nat) :
  Basis S :=
  {| basis_carrier := truncate_nu n (value_carrier x) |}.

#[global]
Instance Dense_indexed_container (S : pointed_container) :
  @Dense
    (Value S)
    (Basis S)
    (@OType_indexed_value S)
    (@OType_indexed_basis S) :=
  {| incl := basis_incl
   ; ideal := value_ideal
  |}.

(** The wrapper order is definitionally the underlying container order. *)
Lemma directed_basis_carrier {S : pointed_container} {I : Type}
  (d : I -> Basis S) :
  directed d <-> directed (fun i => basis_carrier (d i)).
Proof. reflexivity. Qed.

Lemma directed_value_carrier {S : pointed_container} {I : Type}
  (d : I -> Value S) :
  directed d <-> directed (fun i => value_carrier (d i)).
Proof. reflexivity. Qed.

Lemma supremum_basis_carrier {S : pointed_container} {I : Type}
  (x : Basis S) (d : I -> Basis S) :
  supremum x d <->
  supremum (basis_carrier x) (fun i => basis_carrier (d i)).
Proof.
  split; intros [Hub Hleast]; split.
  - exact Hub.
  - intros ub Hub_raw.
    change (mu_le S (basis_carrier x) ub).
    apply (Hleast {| basis_carrier := ub |}); exact Hub_raw.
  - exact Hub.
  - intros [ub] Hub_wrapped.
    change (mu_le S (basis_carrier x) ub).
    apply Hleast; exact Hub_wrapped.
Qed.

Lemma supremum_value_carrier {S : pointed_container} {I : Type}
  (x : Value S) (d : I -> Value S) :
  supremum x d <->
  supremum (value_carrier x) (fun i => value_carrier (d i)).
Proof.
  split; intros [Hub Hleast]; split.
  - exact Hub.
  - intros ub Hub_raw.
    change (nu_le S (value_carrier x) ub).
    apply (Hleast {| value_carrier := ub |}); exact Hub_raw.
  - exact Hub.
  - intros [ub] Hub_wrapped.
    change (nu_le S (value_carrier x) ub).
    apply Hleast; exact Hub_wrapped.
Qed.

(** Compactness and completeness are transported once at the generic wrapper
    boundary.  Concrete descriptors need only register capabilities. *)
#[global]
Instance Compact_indexed_basis (S : pointed_container)
  `{DB : DecidableBottom S} `{FP : FinitePositions S} :
  @Compact (Basis S) (@OType_indexed_basis S).
Proof.
  constructor; intros [x] d Hdirected Hsup.
  apply directed_basis_carrier in Hdirected.
  apply supremum_basis_carrier in Hsup.
  destruct
    (@mu_compact (@finitary_container_of S DB FP) x
      (fun n => basis_carrier (d n)) Hdirected Hsup) as [i Hi].
  exists i; exact Hi.
Qed.

#[global]
Instance CPO_indexed_value (S : pointed_container)
  `{DB : DecidableBottom S} :
  @CPO (Value S) (@OType_indexed_value S).
Proof.
  constructor; intros d Hdirected.
  apply directed_value_carrier in Hdirected.
  exists
    {| value_carrier :=
         nu_sup (@decidable_container_of S DB)
           (fun n => value_carrier (d n)) |}.
  apply (proj2 (@supremum_value_carrier S nat _ d)).
  exact
    (@nu_sup_supremum (@decidable_container_of S DB)
      (fun n => value_carrier (d n)) Hdirected).
Qed.

(** All five algebraicity laws are discharged generically.  This small
    transport proof replaces the per-datatype instance reassembly that the
    raw fixed-point carriers currently require. *)
#[global]
Instance aCPO_indexed_container (S : pointed_container)
  `{DB : DecidableBottom S} `{FP : FinitePositions S} :
  @aCPO
    (Value S)
    (Basis S)
    (@OType_indexed_value S)
    (@OType_indexed_basis S)
    (@Compact_indexed_basis S DB FP)
    (@Dense_indexed_container S)
    (@CPO_indexed_value S DB).
Proof.
  constructor.
  - intros [x] [y]; apply incl_mu_order_iff.
  - intros [x]; apply chain_truncate_nu.
  - intros [x] [y] Hxy n.
    apply truncate_nu_monotone; exact Hxy.
  - intro n.
    change (continuous (fun x : Value S => value_ideal x n)).
    intros d Hdirected [x] Hsup.
    apply (proj2 (@supremum_basis_carrier S nat _ _)).
    apply directed_value_carrier in Hdirected.
    apply supremum_value_carrier in Hsup.
    exact
      ((@truncate_nu_continuous (@decidable_container_of S DB) n)
        (fun i => value_carrier (d i)) Hdirected x Hsup).
  - intros [x].
    apply (proj2 (@supremum_value_carrier S nat _ _)).
    exact (@incl_truncate_nu_supremum S x).
Qed.

(** Standard arbitrary-directed compactness also survives the wrapper
    boundary. *)
Theorem basis_incl_scott_compact (S : pointed_container)
  `{DB : DecidableBottom S} `{FP : FinitePositions S}
  (b : Basis S) :
  scott_compact (basis_incl b).
Proof.
  destruct b as [b].
  unfold scott_compact.
  intros I d Hinhabited Hdirected [limit] Hsup Hbelow.
  apply directed_value_carrier in Hdirected.
  apply supremum_value_carrier in Hsup.
  change (nu_le S (incl_mu b) limit) in Hbelow.
  destruct
    (@incl_mu_scott_compact (@finitary_container_of S DB FP) b
      I (fun i => value_carrier (d i))
      Hinhabited Hdirected limit Hsup Hbelow) as [i Hi].
  exists i; exact Hi.
Qed.
