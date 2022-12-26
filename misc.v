(** * Miscellaneous definitions and lemmas. *)

Set Implicit Arguments.

From Coq Require Import
  Bool
  PeanoNat
  String
  List
  Lia
  RelationClasses
  Basics
  Fin
.
Import ListNotations.
Local Open Scope program_scope.

Require Import tactics.

Definition ϵ := EmptyString.

Definition tuple (A B C : Type) (f : A -> B) (g : A -> C) (x : A) : B*C :=
  (f x, g x).

Definition cotuple {A B C : Type} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition sum_map {A B C D : Type} (f : A -> C) (g : B -> D) (x : A + B) : C + D :=
  match x with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

Definition bimap {A B C D : Type} (f : A -> C) (g : B -> D) (x : A * B) : C * D :=
  let (a, b) := x in (f a, g b).

Definition first {A B C : Type} (f : A -> B) (x : A * C) : B * C :=
  let (a, b) := x in (f a, b).

Definition second {A B C : Type} (f : B -> C) (x : A * B) : A * C :=
  let (a, b) := x in (a, f b).

Inductive is_prefix {A : Type} : list A -> list A -> Prop :=
| is_prefix_nil : forall l2,
    is_prefix nil l2
| is_prefix_cons : forall x l1 l2,
    is_prefix l1 l2 ->
    is_prefix (x :: l1) (x :: l2).

#[global]
  Instance Reflexive_is_prefix {A : Type} : Reflexive (@is_prefix A).
Proof. intro x; induction x; constructor; auto. Qed.

#[global]
  Instance Transitive_is_prefix {A : Type} : Transitive (@is_prefix A).
Proof.
  intros xs ys zs.
  revert xs zs.
  induction ys; intros xs zs H0 H1.
  - inversion H0; subst; constructor.
  - inversion H0; subst.
    + constructor.
    + inversion H1; subst.
      constructor; apply IHys; auto.
Qed.

#[global]
  Instance PreOrder_is_prefix {A : Type} : PreOrder (@is_prefix A).
Proof. constructor. apply Reflexive_is_prefix. apply Transitive_is_prefix. Qed.

Lemma is_prefix_antisym {A} (l1 l2 : list A) :
  is_prefix l1 l2 ->
  is_prefix l2 l1 ->
  l1 = l2.
Proof.
  revert l2; induction l1; intros l2 H1 H2.
  { inv H2; auto. }
  inv H1; inv H2; f_equal; apply IHl1; auto.
Qed.

Fixpoint seq_prefix_aux {A : Type} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => f n' :: seq_prefix_aux f n'
  end.

Definition seq_prefix {A : Type} (f : nat -> A) (n : nat) : list A :=
  rev (seq_prefix_aux f n).

Lemma length_seq_prefix_aux {A} (f : nat -> A) (n : nat) :
  length (seq_prefix_aux f n) = n.
Proof. induction n; simpl; auto. Qed.

Corollary length_seq_prefix {A} (f : nat -> A) (n : nat) :
  length (seq_prefix f n) = n.
Proof. unfold seq_prefix; rewrite rev_length; apply length_seq_prefix_aux. Qed.

Lemma map_seq_prefix_aux {A B} (f : nat -> A) (g : A -> B) (n : nat) :
  map g (seq_prefix_aux f n) = seq_prefix_aux (g ∘ f) n.
Proof.
  revert f g; induction n; intros f g; simpl; auto.
  rewrite IHn; reflexivity.
Qed.

Lemma map_seq_prefix {A B} (f : nat -> A) (g : A -> B) (n : nat) :
  map g (seq_prefix f n) = seq_prefix (g ∘ f) n.
Proof.
  unfold seq_prefix; rewrite map_rev, map_seq_prefix_aux; reflexivity.
Qed.

Lemma forall_seq_prefix_aux {A} (f : nat -> A) (P : A -> Prop) (n : nat) :
  (forall i, P (f i)) ->
  Forall P (seq_prefix_aux f n).
Proof.
  induction n; intro H; simpl.
  { constructor. }
  constructor; auto.
Qed.

Lemma forall_seq_prefix {A} (f : nat -> A) (P : A -> Prop) (n : nat) :
  (forall i, P (f i)) ->
  Forall P (seq_prefix f n).
Proof. intro H; apply Forall_rev, forall_seq_prefix_aux; auto. Qed.

Lemma in_seq_prefix_aux {A} (f : nat -> A) (i j : nat) :
  i < j ->
  In (f i) (seq_prefix_aux f j).
Proof.
  revert f i; induction j; intros f i Hij; try lia; simpl.
  destruct (Nat.eqb_spec i j); subst.
  - left; reflexivity.
  - right; apply IHj; lia.
Qed.

Lemma seq_prefix_aux_monotone {A} (f : nat -> A) (i j : nat) :
  i <= j ->
  Forall (fun a => In a (seq_prefix_aux f j)) (seq_prefix_aux f i).
Proof.
  intros Hij; apply Forall_forall.
  revert Hij; revert f j; induction i; simpl; intros f j Hij a Hin.
  { inv Hin. }
  destruct Hin as [Hin|Hin]; subst.
  - destruct j; try lia; simpl.
    destruct (Nat.eqb_spec i j); subst.
    + left; reflexivity.
    + right; apply in_seq_prefix_aux; lia.
  - apply IHi; auto; lia.
Qed.

Inductive list_rel {A B : Type} (R : A -> B -> Prop) : list A -> list B -> Prop :=
| list_rel_nil : list_rel R [] []
| list_rel_cons : forall x y xs ys,
    R x y ->
    list_rel R xs ys ->
    list_rel R (x :: xs) (y :: ys).

Lemma list_rel_app {A B : Type}
  (R : A -> B -> Prop) (l1 l2 : list A) (l3 l4 : list B) :
  list_rel R l1 l3 /\ list_rel R l2 l4 -> list_rel R (l1 ++ l2) (l3 ++ l4).
Proof.
  revert l2 l3 l4.
  induction l1; intros l2 l3 l4 [H0 H1];
    inversion H0; subst; simpl; try constructor; auto.
Qed.

Lemma list_rel_rev {A B} (R : A -> B -> Prop) (l1 : list A) (l2 : list B) :
  list_rel R l1 l2 ->
  list_rel R (rev l1) (rev l2).
Proof.
  induction 1; simpl.
  - constructor.
  - apply list_rel_app; split; auto; constructor; auto; constructor.
Qed.

Lemma list_rel_prefix {A B} (R : A -> B -> Prop) (f : nat -> A) (g : nat -> B) (n : nat) :
  (forall i, R (f i) (g i)) ->
  list_rel R (seq_prefix f n) (seq_prefix g n).
Proof.
  intro HR; apply list_rel_rev.
  induction n; constructor; auto.
Qed.

Lemma list_rel_length {A B : Type} (l1 : list A) (l2 : list B) (R : A -> B -> Prop) :
  list_rel R l1 l2 ->
  length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

Lemma list_rel_map {A B C D: Type} (l1 : list A) (l2 : list B)
  (R : C -> D -> Prop) (f : A -> C) (g : B -> D) :
  list_rel (fun x y => R (f x) (g y)) l1 l2 ->
  list_rel R (map f l1) (map g l2).
Proof. induction 1; simpl; constructor; auto. Qed.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint rev_range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: rev_range n'
  end.

Lemma rev_range_spec (n : nat) :
  rev_range n = rev (range n).
Proof.
  induction n; simpl; auto.
  rewrite IHn, rev_app_distr; reflexivity.
Qed.

Lemma in_range (n i : nat) :
  (i < n)%nat <-> In i (range n).
Proof.
  split.
  - revert i; induction n; intros i Hlt; simpl; try lia.
    apply in_or_app.
    destruct (Nat.eqb_spec i n); subst; simpl; auto; left; apply IHn; lia.
  - revert i; induction n; simpl; intros i Hin; try contradiction.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply IHn in Hin; lia.
    + destruct Hin as [?| Hin]; subst; auto; inversion Hin.
Qed.

Lemma range_length (n : nat) :
  length (range n) = n.
Proof.
  induction n; simpl; auto; rewrite app_length; simpl; rewrite IHn; lia.
Qed.

Lemma range_seq (n : nat) :
  range n = seq 0 n.
Proof.
  induction n; auto; rewrite seq_S; simpl; rewrite IHn; reflexivity.
Qed.

Fixpoint countb_list {A : Type} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + countb_list f xs
  end.

Lemma countb_list_const_true {A} (l : list A) :
  countb_list (fun _ => true) l = length l.
Proof. induction l; auto; simpl; rewrite IHl; auto. Qed.

Lemma not_in_countb_list (l : list nat) (n : nat) :
  ~ In n l ->
  countb_list (Nat.eqb n) l = O.
Proof.
  revert n; induction l; simpl; intros n Hin; auto.
  destruct (Nat.eqb_spec n a); subst.
  - exfalso; apply Hin; auto.
  - rewrite IHl.
    + lia.
    + intro HC; apply Hin; auto.
Qed.

Lemma countb_list_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  countb_list f (l1 ++ l2) = (countb_list f l1 + countb_list f l2)%nat.
Proof. induction l1; auto; simpl; rewrite IHl1; lia. Qed.

Fixpoint drop {A} (n : nat) (l : list A) : list A :=
  match (n, l) with
  | (_, []) => []
  | (O, _) => l
  | (S n', _ :: l') => drop n' l'
  end.

Fixpoint take {A} (n : nat) (l : list A) : list A :=
  match (n, l) with
  | (_, []) => []
  | (O, _) => []
  | (S n', x :: l') => x :: take n' l'
  end.

Lemma take_drop_spec {A} (n : nat) (l : list A) :
  take n l ++ drop n l = l.
Proof.
  revert l; induction n; intro l; simpl; destruct l; auto.
  - simpl; rewrite IHn; reflexivity.
Qed.

Lemma take_length {A} (n : nat) (l : list A) :
  (length (take n l) <= n)%nat.
Proof.
  revert l; induction n; intros []; simpl; try lia.
  specialize (IHn l); lia.
Qed.

Lemma take_length_min {A} n (l : list A) :
  length (take n l) = min n (length l).
Proof. revert l; induction n; intros []; simpl; auto. Qed.

Lemma length_drop_le {A} (l : list A) (n : nat) :
  (length (drop n l) <= length l - n)%nat.
Proof.
  revert l; induction n; intro l; destruct l; simpl; try lia; apply IHn.
Qed.

Definition shift {A} (f : nat -> A) (n : nat) : A :=
  f (S n).

(* Types with at least one element. *)
Class Inhabited (A : Type) : Type :=
  { el : A }.

#[global]
  Instance Inhabited_nat : Inhabited nat :=
  {| el := O |}.

Definition id {A} (x : A) : A := x.

Lemma f_eq' {A B} (x : A) (f g : A -> B) :
  f = g ->
  f x = g x.
Proof. intros ->; reflexivity. Qed.

Lemma Forall_take {A} (P : A -> Prop) l n :
  Forall P l ->
  Forall P (take n l).
Proof.
  revert P l; induction n; intros P l Hl; simpl.
  - destruct l; auto.
  - destruct l; inv Hl; auto.
Qed.

Lemma Forall_drop {A} (P : A -> Prop) l n :
  Forall P l ->
  Forall P (drop n l).
Proof.
  revert P l; induction n; intros P l Hl; simpl.
  - destruct l; auto.
  - destruct l; inv Hl; auto.
Qed.

Lemma Forall_list_rel {A} (R : A -> A -> Prop) l :
  Forall (fun x => R x x) l ->
  list_rel R l l.
Proof. induction l; intro Hl; inv Hl; constructor; auto. Qed.

(* Types with decidable equality. *)
Class EqType (A : Type) : Type :=
  { eqb : A -> A -> bool
  ; eqb_spec : forall x y, reflect (x = y) (eqb x y)
  }.

#[global]
  Program Instance EqType_unit : EqType unit :=
  {| eqb := fun _ _ => true |}.
Next Obligation. destruct x, y; constructor; reflexivity. Qed.

#[global]
  Instance EqType_bool : EqType bool :=
  {| eqb := Bool.eqb
  ; eqb_spec := Bool.eqb_spec |}.

#[global]
  Instance EqType_nat : EqType nat :=
  {| eqb := Nat.eqb
  ; eqb_spec := Nat.eqb_spec |}.

#[global]
  Program Instance EqType_option {A} `{EqType A} : EqType (option A) :=
  {| eqb := fun o1 o2 => match (o1, o2) with
                      | (None, None) => true
                      | (Some x, Some y) => eqb x y
                      | _ => false
                      end |}.
Solve Obligations with try (split; congruence).
Next Obligation.
  destruct x, y; try (constructor; congruence).
  destruct (eqb_spec a a0); constructor; congruence.
Qed.

#[global]
  Program Instance EqType_fin {n} : EqType (Fin.t n) :=
 {| eqb := Fin.eqb |}.
Next Obligation.
  destruct (Fin.eqb x y) eqn:Hxy.
  - apply eqb_eq in Hxy; subst; constructor; reflexivity.
  - constructor; intro HC.
    apply eqb_eq in HC; congruence.
Qed.

Fixpoint list_eqb {A : Type} `{EqType A} (l1 l2 : list A) : bool :=
  match (l1, l2) with
  | (nil, nil) => true
  | (x :: l1', y :: l2') => eqb x y && list_eqb l1' l2'
  | _ => false
  end.

#[global]
  Program Instance EqType_list {A : Type} `{EqType A} : EqType (list A) :=
  {| eqb := list_eqb |}.
Next Obligation.
  revert y.
  induction x; intros []; simpl; try (constructor; congruence).
  destruct (eqb_spec a a0); subst; simpl.
  - destruct (IHx l); subst; constructor; congruence.
  - constructor; congruence.
Qed.

#[global]
  Program Instance EqType_prod {A B : Type} `{EqType A} `{EqType B} : EqType (A * B) :=
  {| eqb := fun a b => let (a1, a2) := a in
                    let (b1, b2) := b in
                    eqb a1 b1 && eqb a2 b2 |}.
Next Obligation.
  destruct (eqb_spec a0 a); subst; simpl.
  - destruct (eqb_spec b0 b); subst; constructor; congruence.
  - constructor; congruence.
Qed.

#[global]
  Program Instance EqType_sum {A B : Type} `{EqType A} `{EqType B} : EqType (A + B) :=
  {| eqb := fun a b => match (a, b) with
                    | (inl x, inl y) => eqb x y
                    | (inr x, inr y) => eqb x y
                    | _ => false
                    end |}.
Next Obligation. split; intros ? ?; congruence. Qed.
Next Obligation. split; intros ? ?; congruence. Qed.
Next Obligation.
  destruct x.
  - destruct y.
    + destruct (eqb_spec a a0); subst; constructor; congruence.
    + constructor; congruence.
  - destruct y.
    + constructor; congruence.
    + destruct (eqb_spec b b0); subst; constructor; congruence.
Qed.

Lemma eqb_refl {A} `{EqType A} (a : A) :
  eqb a a = true.
Proof. destruct (eqb_spec a a); subst; congruence. Qed.

Definition is_prime (n : nat) : Prop :=
  1 < n /\ forall m, 1 < m -> n <> m -> n mod m <> O.

(* Inductive nelist (A : Type) : Type := *)
(* | ne_single : A -> nelist A *)
(* | ne_cons : A -> nelist A -> nelist A. *)

(* Inductive in_nelist {A} : A -> nelist A -> Prop := *)
(* | in_nelist_single : forall a, *)
(*     in_nelist a (ne_single a) *)
(* | in_nelist_here : forall a l,  *)
(*     in_nelist a (ne_cons a l) *)
(* | in_nelist_there : forall a b l, *)
(*     in_nelist a l -> *)
(*     in_nelist a (ne_cons b l). *)

(* Fixpoint nelist_length {A} (l : nelist A) : nat := *)
(*   match l with *)
(*   | ne_single _ => 1 *)
(*   | ne_cons _ xs => S (nelist_length xs) *)
(*   end. *)

(* (* Finite types. *) *)
(* Class FinType (A : Type) : Type := *)
(*   { enum : nelist A *)
(*   ; enum_full : forall a, in_nelist a enum *)
(*   (* ; enum_nodup : NoDup enum *) *)
(*   }. *)

(* (* Finite types. *) *)
(* Class FinType (A : Type) : Type := *)
(*   { enum : list A *)
(*   ; enum_full : forall a, In a enum *)
(*   ; enum_nodup : NoDup enum *)
(*   }. *)

(* (* Finite types. *) *)
(* Class FinType (A : Type) (n : nat) : Type := *)
(*   { enum : Vector.t A n *)
(*   ; enum_full : forall a, Vector.In a enum *)
(*   (* ; enum_nodup : Vector.NoDup enum *) *)
(*   }. *)
