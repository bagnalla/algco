(** * Native Boolean cotrees as container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  FunctionalExtensionality
  List
.

Import ListNotations.

From algco Require Import
  cotree
  order
.

From algco.generic Require Import
  container
  finitary_container
  pointed_container
.

(** Bottom and leaves are nullary; a node has one child at each Boolean
    position. *)
Inductive cotree_shape (A : Type) : Type :=
| cotree_bottom_shape : cotree_shape A
| cotree_leaf_shape : A -> cotree_shape A
| cotree_node_shape : cotree_shape A.

Definition cotree_position {A : Type} (s : cotree_shape A) : Type :=
  match s with
  | cotree_bottom_shape => Empty_set
  | cotree_leaf_shape _ => Empty_set
  | cotree_node_shape => bool
  end.

Definition cotree_container (A : Type) : container :=
  {| shape := cotree_shape A
   ; position := cotree_position
  |}.

Definition cotree_pointed_container (A : Type) : pointed_container :=
  {| pc_container := cotree_container A
   ; bottom_shape := cotree_bottom_shape
   ; bottom_position_absurd := fun p => match p with end
  |}.

Definition cotree_bottom_shape_dec {A : Type} (s : cotree_shape A) :
  {s = cotree_bottom_shape} + {s <> cotree_bottom_shape}.
Proof.
  destruct s as [|a|].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
Defined.

Definition cotree_position_enum {A : Type} (s : cotree_shape A) :
  list (cotree_position s) :=
  match s with
  | cotree_bottom_shape => []
  | cotree_leaf_shape _ => []
  | cotree_node_shape => [false; true]
  end.

Lemma cotree_position_enum_complete {A : Type}
  (s : cotree_shape A) (p : cotree_position s) :
  In p (cotree_position_enum s).
Proof.
  destruct s as [|a|].
  - destruct p.
  - destruct p.
  - destruct p; simpl; auto.
Qed.

Definition cotree_decidable_container (A : Type) :
  decidable_pointed_container :=
  {| dpc_pointed := cotree_pointed_container A
   ; bottom_shape_dec := @cotree_bottom_shape_dec A
  |}.

Definition cotree_finitary_container (A : Type) :
  finitary_pointed_container :=
  {| fpc_decidable := cotree_decidable_container A
   ; position_enum := @cotree_position_enum A
   ; position_enum_complete := @cotree_position_enum_complete A
  |}.

(** ** Initial algebra and native finite trees *)

Fixpoint mu_to_atree {A : Type}
  (x : mu (cotree_container A)) : atree bool A :=
  match x with
  | in_mu cotree_bottom_shape _ => abot
  | in_mu (cotree_leaf_shape a) _ => aleaf a
  | in_mu cotree_node_shape children =>
      anode (fun b => mu_to_atree (children b))
  end.

Fixpoint atree_to_mu {A : Type}
  (t : atree bool A) : mu (cotree_container A) :=
  match t with
  | abot =>
      in_mu (C := cotree_container A) cotree_bottom_shape
        (fun p : Empty_set => match p with end)
  | aleaf a =>
      in_mu (C := cotree_container A) (cotree_leaf_shape a)
        (fun p : Empty_set => match p with end)
  | anode children =>
      in_mu (C := cotree_container A) cotree_node_shape
        (fun b : bool => atree_to_mu (children b))
  end.

Lemma mu_to_atree_atree_to_mu {A : Type} (t : atree bool A) :
  mu_to_atree (atree_to_mu t) = t.
Proof.
  induction t as [|a|children IH]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply functional_extensionality; intro b; apply IH.
Qed.

Lemma atree_to_mu_mu_to_atree {A : Type}
  (x : mu (cotree_container A)) :
  atree_to_mu (mu_to_atree x) = x.
Proof.
  induction x as [s children IH]; destruct s as [|a|]; simpl.
  - f_equal; apply functional_extensionality; intro p; destruct p.
  - f_equal; apply functional_extensionality; intro p; destruct p.
  - f_equal; apply functional_extensionality; intro b; apply IH.
Qed.

(** ** Final coalgebra and native cotrees *)

CoFixpoint nu_to_cotree {A : Type}
  (x : nu (cotree_container A)) : cotree bool A :=
  match x with
  | in_nu cotree_bottom_shape _ => cobot
  | in_nu (cotree_leaf_shape a) _ => coleaf a
  | in_nu cotree_node_shape children =>
      conode (fun b => nu_to_cotree (children b))
  end.

CoFixpoint cotree_to_nu {A : Type}
  (t : cotree bool A) : nu (cotree_container A) :=
  match t with
  | cobot =>
      in_nu (C := cotree_container A) cotree_bottom_shape
        (fun p : Empty_set => match p with end)
  | coleaf a =>
      in_nu (C := cotree_container A) (cotree_leaf_shape a)
        (fun p : Empty_set => match p with end)
  | conode children =>
      in_nu (C := cotree_container A) cotree_node_shape
        (fun b : bool => cotree_to_nu (children b))
  end.

Lemma nu_to_cotree_bottom {A : Type}
  (children : Empty_set -> nu (cotree_container A)) :
  nu_to_cotree
    (in_nu (C := cotree_container A) cotree_bottom_shape children) =
  cobot.
Proof. rewrite unf_eq; reflexivity. Qed.

Lemma nu_to_cotree_leaf {A : Type} (a : A)
  (children : Empty_set -> nu (cotree_container A)) :
  nu_to_cotree
    (in_nu (C := cotree_container A) (cotree_leaf_shape a) children) =
  coleaf a.
Proof. rewrite unf_eq; reflexivity. Qed.

Lemma nu_to_cotree_node {A : Type}
  (children : bool -> nu (cotree_container A)) :
  nu_to_cotree
    (in_nu (C := cotree_container A) cotree_node_shape children) =
  conode (fun b => nu_to_cotree (children b)).
Proof. rewrite unf_eq; reflexivity. Qed.

Lemma cotree_to_nu_bottom {A : Type} :
  cotree_to_nu (@cobot bool A) =
  in_nu (C := cotree_container A) cotree_bottom_shape
    (fun p : Empty_set => match p with end).
Proof. rewrite unfold_nu_eq; reflexivity. Qed.

Lemma cotree_to_nu_leaf {A : Type} (a : A) :
  cotree_to_nu (@coleaf bool A a) =
  in_nu (C := cotree_container A) (cotree_leaf_shape a)
    (fun p : Empty_set => match p with end).
Proof. rewrite unfold_nu_eq; reflexivity. Qed.

Lemma cotree_to_nu_node {A : Type} (children : bool -> cotree bool A) :
  cotree_to_nu (conode children) =
  in_nu (C := cotree_container A) cotree_node_shape
    (fun b : bool => cotree_to_nu (children b)).
Proof. rewrite unfold_nu_eq; reflexivity. Qed.

Lemma cotree_to_nu_nu_to_cotree {A : Type}
  (x : nu (cotree_container A)) :
  nu_equiv (cotree_to_nu (nu_to_cotree x)) x.
Proof.
  revert x; cofix CH; intros [s children]; destruct s as [|a|].
  - rewrite nu_to_cotree_bottom, cotree_to_nu_bottom.
    constructor; intro p; destruct p.
  - rewrite nu_to_cotree_leaf, cotree_to_nu_leaf.
    constructor; intro p; destruct p.
  - rewrite nu_to_cotree_node, cotree_to_nu_node.
    constructor; intro b; apply CH.
Qed.

Lemma nu_to_cotree_cotree_to_nu {A : Type} (t : cotree bool A) :
  cotree_eq (nu_to_cotree (cotree_to_nu t)) t.
Proof.
  revert t; cofix CH; intros [|a|children].
  - rewrite cotree_to_nu_bottom, nu_to_cotree_bottom; constructor.
  - rewrite cotree_to_nu_leaf, nu_to_cotree_leaf; constructor.
  - rewrite cotree_to_nu_node, nu_to_cotree_node.
    constructor; intro b; apply CH.
Qed.

Corollary nu_to_cotree_cotree_to_nu_eq {A : Type}
  (t : cotree bool A) :
  nu_to_cotree (cotree_to_nu t) = t.
Proof. apply cotree_ext, nu_to_cotree_cotree_to_nu. Qed.

(** ** Native specialization of approximation *)

Lemma mu_le_to_atree_le {A : Type}
  (x y : mu (cotree_container A)) :
  mu_le (cotree_pointed_container A) x y ->
  atree_le (mu_to_atree x) (mu_to_atree y).
Proof.
  intro Hxy.
  induction Hxy as
    [children y | s children1 children2 Hchildren IH].
  - simpl; constructor.
  - destruct s as [|a|]; simpl.
    + constructor.
    + constructor.
    + constructor; intro b; apply IH.
Qed.

Lemma atree_le_to_mu_le {A : Type}
  (x y : mu (cotree_container A)) :
  atree_le (mu_to_atree x) (mu_to_atree y) ->
  mu_le (cotree_pointed_container A) x y.
Proof.
  revert y.
  induction x as [sx childrenx IH]; intros [sy childreny] Hxy.
  destruct sx as [|a|], sy as [|b|]; simpl in Hxy.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hxy.
  - inversion Hxy; subst; constructor; intro p; destruct p.
  - inversion Hxy.
  - inversion Hxy.
  - inversion Hxy.
  - inversion Hxy; subst; constructor; intro p; apply IH, H1.
Qed.

Theorem mu_le_iff_atree_le {A : Type}
  (x y : mu (cotree_container A)) :
  mu_le (cotree_pointed_container A) x y <->
  atree_le (mu_to_atree x) (mu_to_atree y).
Proof. split; [apply mu_le_to_atree_le | apply atree_le_to_mu_le]. Qed.

Lemma nu_le_to_cotree_le {A : Type}
  (x y : nu (cotree_container A)) :
  nu_le (cotree_pointed_container A) x y ->
  cotree_le (nu_to_cotree x) (nu_to_cotree y).
Proof.
  revert x y; cofix CH; intros x y Hxy.
  destruct Hxy as
    [children y | s children1 children2 Hchildren].
  - change
      (cotree_le
        (nu_to_cotree
          (in_nu (C := cotree_container A) cotree_bottom_shape children))
        (nu_to_cotree y)).
    rewrite nu_to_cotree_bottom; constructor.
  - destruct s as [|a|].
    + change
        (cotree_le
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_bottom_shape children1))
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_bottom_shape children2))).
      rewrite !nu_to_cotree_bottom; constructor.
    + change
        (cotree_le
          (nu_to_cotree
            (in_nu (C := cotree_container A) (cotree_leaf_shape a)
              children1))
          (nu_to_cotree
            (in_nu (C := cotree_container A) (cotree_leaf_shape a)
              children2))).
      rewrite !nu_to_cotree_leaf; constructor.
    + change
        (cotree_le
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_node_shape children1))
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_node_shape children2))).
      rewrite !nu_to_cotree_node; constructor; intro b.
      apply CH, Hchildren.
Qed.

Lemma cotree_le_to_nu_le {A : Type}
  (x y : nu (cotree_container A)) :
  cotree_le (nu_to_cotree x) (nu_to_cotree y) ->
  nu_le (cotree_pointed_container A) x y.
Proof.
  revert x y; cofix CH; intros [sx childrenx] [sy childreny] Hxy.
  destruct sx as [|a|], sy as [|b|].
  - constructor.
  - constructor.
  - constructor.
  - rewrite nu_to_cotree_leaf, nu_to_cotree_bottom in Hxy; inversion Hxy.
  - rewrite !nu_to_cotree_leaf in Hxy; inversion Hxy; subst.
    constructor; intro p; destruct p.
  - rewrite nu_to_cotree_leaf, nu_to_cotree_node in Hxy; inversion Hxy.
  - rewrite nu_to_cotree_node, nu_to_cotree_bottom in Hxy; inversion Hxy.
  - rewrite nu_to_cotree_node, nu_to_cotree_leaf in Hxy; inversion Hxy.
  - rewrite !nu_to_cotree_node in Hxy; inversion Hxy; subst.
    constructor; intro b; apply CH, H1.
Qed.

Theorem nu_le_iff_cotree_le {A : Type}
  (x y : nu (cotree_container A)) :
  nu_le (cotree_pointed_container A) x y <->
  cotree_le (nu_to_cotree x) (nu_to_cotree y).
Proof. split; [apply nu_le_to_cotree_le | apply cotree_le_to_nu_le]. Qed.

(** Generic inclusion and truncation compute as their native counterparts. *)
Lemma nu_to_cotree_incl_mu {A : Type}
  (x : mu (cotree_container A)) :
  nu_to_cotree (incl_mu (C := cotree_pointed_container A) x) =
  tinj (mu_to_atree x).
Proof.
  induction x as [s children IH]; destruct s as [|a|]; simpl.
  - apply nu_to_cotree_bottom.
  - apply nu_to_cotree_leaf.
  - rewrite nu_to_cotree_node; f_equal.
    apply functional_extensionality; intro b; apply IH.
Qed.

Lemma mu_to_atree_truncate_nu {A : Type} (n : nat)
  (x : nu (cotree_container A)) :
  mu_to_atree (truncate_nu (C := cotree_pointed_container A) n x) =
  tprefix n (nu_to_cotree x).
Proof.
  revert x; induction n as [|n IH]; intros [s children]; simpl.
  - reflexivity.
  - destruct s as [|a|].
    + change
        (abot = tprefix (S n)
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_bottom_shape children))).
      rewrite nu_to_cotree_bottom; reflexivity.
    + change
        (aleaf a = tprefix (S n)
          (nu_to_cotree
            (in_nu (C := cotree_container A) (cotree_leaf_shape a)
              children))).
      rewrite nu_to_cotree_leaf; reflexivity.
    + change
        (anode
          (fun b =>
            mu_to_atree
              (truncate_nu (C := cotree_pointed_container A) n
                (children b))) =
        tprefix (S n)
          (nu_to_cotree
            (in_nu (C := cotree_container A) cotree_node_shape children))).
      rewrite nu_to_cotree_node; simpl; f_equal.
      apply functional_extensionality; intro b; apply IH.
Qed.

Lemma mu_to_atree_truncate_cotree {A : Type} (n : nat)
  (t : cotree bool A) :
  mu_to_atree
    (truncate_nu (C := cotree_pointed_container A) n (cotree_to_nu t)) =
  tprefix n t.
Proof.
  revert t; induction n as [|n IH]; intros [|a|children]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; apply functional_extensionality; intro b; apply IH.
Qed.
