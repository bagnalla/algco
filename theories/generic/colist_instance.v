(** * The native colist as a container fixed point. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  FunctionalExtensionality
  List
.

Import ListNotations.

From algco Require Import
  aCPO
  colist
  cpo
  order
.

From algco.generic Require Import
  container
  pointed_container
  finitary_container
  algebraic_container
.

(** The hole shape is AlgCo's semantic bottom [conil].  A cons shape stores
    its nonrecursive payload and has one recursive position. *)
Inductive colist_shape (A : Type) : Type :=
| colist_hole_shape : colist_shape A
| colist_cons_shape : A -> colist_shape A.

Definition colist_position {A : Type} (s : colist_shape A) : Type :=
  match s with
  | colist_hole_shape => Empty_set
  | colist_cons_shape _ => unit
  end.

Definition colist_container (A : Type) : container :=
  {| shape := colist_shape A
   ; position := colist_position
  |}.

Definition colist_pointed_container (A : Type) : pointed_container :=
  {| pc_container := colist_container A
   ; bottom_shape := colist_hole_shape
   ; bottom_position_absurd := fun p => match p with end
  |}.

Definition colist_bottom_shape_dec {A : Type} (s : colist_shape A) :
  {s = colist_hole_shape} + {s <> colist_hole_shape}.
Proof.
  destruct s as [|a].
  - left; reflexivity.
  - right; discriminate.
Defined.

Definition colist_position_enum {A : Type} (s : colist_shape A) :
  list (colist_position s) :=
  match s with
  | colist_hole_shape => []
  | colist_cons_shape _ => [tt]
  end.

Lemma colist_position_enum_complete {A : Type}
  (s : colist_shape A) (p : colist_position s) :
  In p (colist_position_enum s).
Proof.
  destruct s as [|a].
  - destruct p.
  - destruct p; simpl; auto.
Qed.

Definition colist_decidable_container (A : Type) :
  decidable_pointed_container :=
  {| dpc_pointed := colist_pointed_container A
   ; bottom_shape_dec := @colist_bottom_shape_dec A
  |}.

Definition colist_finitary_container (A : Type) :
  finitary_pointed_container :=
  {| fpc_decidable := colist_decidable_container A
   ; position_enum := @colist_position_enum A
   ; position_enum_complete := @colist_position_enum_complete A
  |}.

(** The full descriptor cannot be reconstructed from the projected carrier
    type, so the colist specialization registers a coherent concrete instance
    stack.  These aliases keep the chosen pointed order explicit and
    deterministic for downstream typeclass search. *)
#[global]
Instance OType_container_colist_mu (A : Type) :
  OType (mu (colist_container A)) :=
  OType_container_mu (colist_pointed_container A).

#[global]
Instance PType_container_colist_mu (A : Type) :
  @PType (mu (colist_container A)) (@OType_container_colist_mu A) :=
  @PType_container_mu (colist_pointed_container A).

#[global]
Instance OType_container_colist_nu (A : Type) :
  OType (nu (colist_container A)) :=
  OType_container_nu (colist_pointed_container A).

#[global]
Instance PType_container_colist_nu (A : Type) :
  @PType (nu (colist_container A)) (@OType_container_colist_nu A) :=
  @PType_container_nu (colist_pointed_container A).

(** A concrete registration keeps typeclass search ergonomic: the generic
    compactness instance is parameterized by the whole finitary-container
    package, which cannot in general be reconstructed from its carrier type. *)
#[global]
Instance Compact_colist_mu (A : Type) :
  @Compact (mu (colist_container A))
    (@OType_container_colist_mu A).
Proof.
  exact (Compact_finitary_container_mu (colist_finitary_container A)).
Qed.

#[global]
Instance CPO_container_colist_nu (A : Type) :
  @CPO (nu (colist_container A)) (@OType_container_colist_nu A).
Proof.
  exact (CPO_decidable_container_nu (colist_decidable_container A)).
Qed.

#[global]
Instance Dense_container_colist (A : Type) :
  @Dense
    (nu (colist_container A))
    (mu (colist_container A))
    (@OType_container_colist_nu A)
    (@OType_container_colist_mu A) :=
  {| incl := @incl_mu (colist_pointed_container A)
   ; ideal := fun x n =>
       @truncate_nu (colist_pointed_container A) n x
  |}.

#[global]
Instance aCPO_container_colist (A : Type) :
  @aCPO
    (nu (colist_container A))
    (mu (colist_container A))
    (@OType_container_colist_nu A)
    (@OType_container_colist_mu A)
    (@Compact_colist_mu A)
    (@Dense_container_colist A)
    (@CPO_container_colist_nu A).
Proof.
  constructor.
  - intros x y; apply incl_mu_order_iff.
  - intro x; apply chain_truncate_nu.
  - intros x y Hxy n; apply truncate_nu_monotone, Hxy.
  - intro n.
    exact (@truncate_nu_continuous (colist_decidable_container A) n).
  - intro x.
    exact (@incl_truncate_nu_supremum (colist_pointed_container A) x).
Qed.

(** ** Initial algebra and native lists *)

Fixpoint mu_to_list {A : Type} (x : mu (colist_container A)) : list A :=
  match x with
  | in_mu colist_hole_shape _ => []
  | in_mu (colist_cons_shape a) children =>
      a :: mu_to_list (children tt)
  end.

Fixpoint list_to_mu {A : Type} (l : list A) : mu (colist_container A) :=
  match l with
  | [] =>
      in_mu (C := colist_container A) colist_hole_shape
        (fun p : Empty_set => match p with end)
  | a :: l' =>
      in_mu (C := colist_container A) (colist_cons_shape a)
        (fun _ : unit => list_to_mu l')
  end.

Lemma mu_to_list_list_to_mu {A : Type} (l : list A) :
  mu_to_list (list_to_mu l) = l.
Proof. induction l; simpl; congruence. Qed.

Lemma list_to_mu_mu_to_list {A : Type} (x : mu (colist_container A)) :
  list_to_mu (mu_to_list x) = x.
Proof.
  induction x as [s children IH]; destruct s as [|a]; simpl.
  - f_equal; apply functional_extensionality; intro p; destruct p.
  - f_equal; apply functional_extensionality; intros []; apply IH.
Qed.

Corollary colist_mu_compact {A : Type} (x : mu (colist_container A)) :
  compact x.
Proof. apply compact_spec. Qed.

Corollary list_to_mu_compact {A : Type} (l : list A) :
  compact (list_to_mu l).
Proof. apply compact_spec. Qed.

(** ** Final coalgebra and native colists *)

CoFixpoint nu_to_colist {A : Type}
  (x : nu (colist_container A)) : colist A :=
  match x with
  | in_nu colist_hole_shape _ => conil
  | in_nu (colist_cons_shape a) children =>
      cocons a (nu_to_colist (children tt))
  end.

CoFixpoint colist_to_nu {A : Type}
  (l : colist A) : nu (colist_container A) :=
  match l with
  | conil =>
      in_nu (C := colist_container A) colist_hole_shape
        (fun p : Empty_set => match p with end)
  | cocons a l' =>
      in_nu (C := colist_container A) (colist_cons_shape a)
        (fun _ : unit => colist_to_nu l')
  end.

Lemma nu_to_colist_hole {A : Type}
  (children : Empty_set -> nu (colist_container A)) :
  nu_to_colist
    (in_nu (C := colist_container A) colist_hole_shape children) = conil.
Proof. rewrite unf_eq; reflexivity. Qed.

Lemma nu_to_colist_cons {A : Type} (a : A)
  (children : unit -> nu (colist_container A)) :
  nu_to_colist
    (in_nu (C := colist_container A) (colist_cons_shape a) children) =
  cocons a (nu_to_colist (children tt)).
Proof. rewrite unf_eq; reflexivity. Qed.

Lemma colist_to_nu_nil {A : Type} :
  colist_to_nu (@conil A) =
  in_nu (C := colist_container A) colist_hole_shape
    (fun p : Empty_set => match p with end).
Proof. rewrite unfold_nu_eq; reflexivity. Qed.

Lemma colist_to_nu_cons {A : Type} (a : A) (l : colist A) :
  colist_to_nu (cocons a l) =
  in_nu (C := colist_container A) (colist_cons_shape a)
    (fun _ : unit => colist_to_nu l).
Proof. rewrite unfold_nu_eq; reflexivity. Qed.

(** Converting a generic value to a native colist and back preserves it up to
    generic container bisimilarity. *)
Lemma colist_to_nu_nu_to_colist {A : Type}
  (x : nu (colist_container A)) :
  nu_equiv (colist_to_nu (nu_to_colist x)) x.
Proof.
  revert x; cofix CH; intros [s children]; destruct s as [|a].
  - rewrite nu_to_colist_hole, colist_to_nu_nil.
    constructor; intro p; destruct p.
  - rewrite nu_to_colist_cons, colist_to_nu_cons.
    constructor; intros []; apply CH.
Qed.

(** Converting a native colist to the generic fixed point and back preserves
    it up to the native coinductive equality. *)
Lemma nu_to_colist_colist_to_nu {A : Type} (l : colist A) :
  colist_eq (nu_to_colist (colist_to_nu l)) l.
Proof.
  revert l; cofix CH; intros [|a l].
  - rewrite colist_to_nu_nil, nu_to_colist_hole; constructor.
  - rewrite colist_to_nu_cons, nu_to_colist_cons.
    constructor; apply CH.
Qed.

Corollary nu_to_colist_colist_to_nu_eq {A : Type} (l : colist A) :
  nu_to_colist (colist_to_nu l) = l.
Proof. apply colist_ext, nu_to_colist_colist_to_nu. Qed.

(** ** Proof-level specialization of approximation *)

(** The generic finite approximation order is exactly the native list order
    after specializing the pointed container. *)
Lemma mu_le_to_list_le {A : Type}
  (x y : mu (colist_container A)) :
  mu_le (colist_pointed_container A) x y ->
  list_le (mu_to_list x) (mu_to_list y).
Proof.
  intro Hxy.
  induction Hxy as [children y | s children1 children2 Hchildren IH].
  - simpl; constructor.
  - destruct s as [|a]; simpl.
    + constructor.
    + constructor; apply (IH tt).
Qed.

Lemma list_le_to_mu_le {A : Type}
  (x y : mu (colist_container A)) :
  list_le (mu_to_list x) (mu_to_list y) ->
  mu_le (colist_pointed_container A) x y.
Proof.
  revert y.
  induction x as [sx childrenx IH]; intros [sy childreny] Hxy.
  destruct sx as [|a], sy as [|b]; simpl in Hxy.
  - constructor.
  - constructor.
  - inversion Hxy.
  - inversion Hxy; subst.
    constructor; intros []; apply IH; assumption.
Qed.

Theorem mu_le_iff_list_le {A : Type}
  (x y : mu (colist_container A)) :
  mu_le (colist_pointed_container A) x y <->
  list_le (mu_to_list x) (mu_to_list y).
Proof. split; [apply mu_le_to_list_le | apply list_le_to_mu_le]. Qed.

Corollary mu_le_list_to_mu_iff {A : Type} (l1 l2 : list A) :
  mu_le (colist_pointed_container A) (list_to_mu l1) (list_to_mu l2) <->
  list_le l1 l2.
Proof. rewrite mu_le_iff_list_le, !mu_to_list_list_to_mu; reflexivity. Qed.

(** For this concrete basis, generic order equivalence can be strengthened to
    Coq equality, recovering the conclusion of native [list_compact]. *)
Corollary colist_mu_compact_exact {A : Type}
  (x : mu (colist_container A))
  (ch : nat -> mu (colist_container A)) :
  directed ch -> supremum x ch ->
  exists i, ch i = x.
Proof.
  intros Hch Hsup.
  destruct (@colist_mu_compact A x ch Hch Hsup) as [i [Hix Hxi]].
  exists i.
  rewrite <- (@list_to_mu_mu_to_list A (ch i)).
  rewrite <- (@list_to_mu_mu_to_list A x).
  f_equal; apply list_le_antisym.
  - apply mu_le_to_list_le; exact Hix.
  - apply mu_le_to_list_le; exact Hxi.
Qed.

(** The corresponding coinductive relation is exactly native colist
    approximation. *)
Lemma nu_le_to_colist_le {A : Type}
  (x y : nu (colist_container A)) :
  nu_le (colist_pointed_container A) x y ->
  colist_le (nu_to_colist x) (nu_to_colist y).
Proof.
  revert x y; cofix CH; intros x y Hxy.
  destruct Hxy as [children y | s children1 children2 Hchildren].
  - change
      (colist_le
        (nu_to_colist
          (in_nu (C := colist_container A) colist_hole_shape children))
        (nu_to_colist y)).
    rewrite nu_to_colist_hole; constructor.
  - destruct s as [|a].
    + change
        (colist_le
          (nu_to_colist
            (in_nu (C := colist_container A) colist_hole_shape children1))
          (nu_to_colist
            (in_nu (C := colist_container A) colist_hole_shape children2))).
      rewrite !nu_to_colist_hole; constructor.
    + change
        (colist_le
          (nu_to_colist
            (in_nu (C := colist_container A) (colist_cons_shape a) children1))
          (nu_to_colist
            (in_nu (C := colist_container A) (colist_cons_shape a) children2))).
      rewrite !nu_to_colist_cons; constructor; apply CH, Hchildren.
Qed.

Lemma colist_le_to_nu_le {A : Type}
  (x y : nu (colist_container A)) :
  colist_le (nu_to_colist x) (nu_to_colist y) ->
  nu_le (colist_pointed_container A) x y.
Proof.
  revert x y; cofix CH; intros [sx childrenx] [sy childreny] Hxy.
  destruct sx as [|a], sy as [|b].
  - constructor.
  - constructor.
  - rewrite nu_to_colist_cons, nu_to_colist_hole in Hxy; inversion Hxy.
  - rewrite !nu_to_colist_cons in Hxy; inversion Hxy; subst.
    constructor; intros []; apply CH; assumption.
Qed.

Theorem nu_le_iff_colist_le {A : Type}
  (x y : nu (colist_container A)) :
  nu_le (colist_pointed_container A) x y <->
  colist_le (nu_to_colist x) (nu_to_colist y).
Proof. split; [apply nu_le_to_colist_le | apply colist_le_to_nu_le]. Qed.

Corollary nu_le_colist_to_nu_iff {A : Type} (l1 l2 : colist A) :
  nu_le (colist_pointed_container A) (colist_to_nu l1) (colist_to_nu l2) <->
  colist_le l1 l2.
Proof.
  rewrite nu_le_iff_colist_le.
  rewrite !nu_to_colist_colist_to_nu_eq; reflexivity.
Qed.

(** Generic inclusion and truncation compute as the existing native
    operations after specialization. *)
Lemma nu_to_colist_incl_mu {A : Type}
  (x : mu (colist_container A)) :
  nu_to_colist (incl_mu (C := colist_pointed_container A) x) =
  inj (mu_to_list x).
Proof.
  induction x as [s children IH]; destruct s as [|a]; simpl.
  - apply nu_to_colist_hole.
  - rewrite nu_to_colist_cons, (IH tt); reflexivity.
Qed.

Corollary nu_to_colist_incl_list {A : Type} (l : list A) :
  nu_to_colist
    (incl_mu (C := colist_pointed_container A) (list_to_mu l)) = inj l.
Proof. rewrite nu_to_colist_incl_mu, mu_to_list_list_to_mu; reflexivity. Qed.

Corollary nu_to_colist_dense_incl_list {A : Type} (l : list A) :
  nu_to_colist (incl (list_to_mu l)) = inj l.
Proof. apply nu_to_colist_incl_list. Qed.

Lemma mu_to_list_truncate_nu {A : Type} (n : nat)
  (x : nu (colist_container A)) :
  mu_to_list (truncate_nu (C := colist_pointed_container A) n x) =
  prefix n (nu_to_colist x).
Proof.
  revert x; induction n as [|n IH]; intros [s children]; simpl.
  - reflexivity.
  - destruct s as [|a].
    + change
        ([] = prefix (S n)
          (nu_to_colist
            (in_nu (C := colist_container A) colist_hole_shape children))).
      rewrite nu_to_colist_hole; reflexivity.
    + change
        (a :: mu_to_list
          (truncate_nu (C := colist_pointed_container A) n (children tt)) =
        prefix (S n)
          (nu_to_colist
            (in_nu (C := colist_container A) (colist_cons_shape a) children))).
      rewrite nu_to_colist_cons; simpl; f_equal; apply IH.
Qed.

Lemma mu_to_list_truncate_colist {A : Type} (n : nat) (l : colist A) :
  mu_to_list
    (truncate_nu (C := colist_pointed_container A) n (colist_to_nu l)) =
  prefix n l.
Proof.
  revert l; induction n as [|n IH]; intros [|a l]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IH.
Qed.

Corollary mu_to_list_dense_ideal_colist {A : Type}
  (n : nat) (l : colist A) :
  mu_to_list (ideal (colist_to_nu l) n) =
  prefix n l.
Proof. apply mu_to_list_truncate_colist. Qed.

Lemma nu_to_colist_incl_truncate {A : Type} (n : nat)
  (x : nu (colist_container A)) :
  nu_to_colist
    (incl_mu (C := colist_pointed_container A)
      (truncate_nu (C := colist_pointed_container A) n x)) =
  coprefix n (nu_to_colist x).
Proof.
  rewrite nu_to_colist_incl_mu, mu_to_list_truncate_nu.
  apply inj_prefix_coprefix.
Qed.

Lemma nu_to_colist_incl_truncate_colist {A : Type}
  (n : nat) (l : colist A) :
  nu_to_colist
    (incl_mu (C := colist_pointed_container A)
      (truncate_nu (C := colist_pointed_container A) n
        (colist_to_nu l))) =
  coprefix n l.
Proof.
  rewrite nu_to_colist_incl_mu, mu_to_list_truncate_colist.
  apply inj_prefix_coprefix.
Qed.
