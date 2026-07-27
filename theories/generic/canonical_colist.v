(** * Semantic colists and their canonical partial completion. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  Equivalence
  FunctionalExtensionality
  Morphisms
.

From algco Require Import
  aCPO
  cpo
  order
.

From algco.generic Require Import
  container
  container_combinators
  container_combinator_examples
  indexed_container
  indexed_fold
  partial_completion
  pointed_container
.

Local Open Scope order_scope.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

(** The semantic carrier has exact nil and cons layers.  The compact basis and
    continuous carrier belong to its lifted partial completion. *)
Definition colist (A : Type) : Type :=
  Semantic (fc_container (composed_colist_signature A)).

Definition colist_basis (A : Type) : Type :=
  FinitePartial (composed_colist_signature A).

Definition partial_colist (A : Type) : Type :=
  Partial (composed_colist_signature A).

Arguments colist A : clear implicits.
Arguments colist_basis A : clear implicits.
Arguments partial_colist A : clear implicits.

(** ** Fully formed semantic colists *)

Definition semantic_colist_children {A X : Type} (a : A) (x : X) :
  position (fc_container (composed_colist_signature A))
    (composed_colist_semantic_cons_shape a) -> X :=
  fun p =>
    match p with
    | inl impossible => match impossible with end
    | inr _ => x
    end.

Arguments semantic_colist_children {A X} a x.

Definition conil {A : Type} : colist A :=
  in_nu (composed_colist_semantic_nil_shape A)
    (fun p => match p with end).

Definition cocons {A : Type} (a : A) (tail : colist A) : colist A :=
  in_nu (composed_colist_semantic_cons_shape a)
    (semantic_colist_children a tail).

Inductive colist_view (A : Type) : Type :=
| view_nil
| view_cons (head : A) (tail : colist A).

Arguments view_nil {A}.
Arguments view_cons {A} head tail.

Definition observe {A : Type} (x : colist A) : colist_view A.
Proof.
  destruct x as [s children].
  destruct s as [u | [a u]].
  - exact view_nil.
  - exact (view_cons a (children (inr tt))).
Defined.

Lemma observe_conil {A : Type} : observe (@conil A) = view_nil.
Proof. reflexivity. Qed.

Lemma observe_cocons {A : Type} (a : A) (tail : colist A) :
  observe (cocons a tail) = view_cons a tail.
Proof. reflexivity. Qed.

(** ** Finite partial approximants and partial colists *)

Definition bpending {A : Type} : colist_basis A :=
  {| basis_carrier := mu_bottom (composed_colist_descriptor A) |}.

Definition bnil {A : Type} : colist_basis A :=
  in_basis (composed_colist_nil_shape A)
    (fun p => match p with end).

Definition bcons {A : Type} (a : A) (tail : colist_basis A) :
  colist_basis A :=
  in_basis (composed_colist_cons_shape a)
    (composed_colist_children a tail).

Definition pending {A : Type} : partial_colist A :=
  {| value_carrier := nu_bottom (composed_colist_descriptor A) |}.

Definition returned_nil {A : Type} : partial_colist A :=
  in_value (composed_colist_nil_shape A)
    (fun p => match p with end).

Definition returned_cons {A : Type}
  (a : A) (tail : partial_colist A) : partial_colist A :=
  in_value (composed_colist_cons_shape a)
    (composed_colist_children a tail).

Lemma bpending_is_bottom {A : Type} :
  @bpending A = (bot : colist_basis A).
Proof. reflexivity. Qed.

Lemma pending_is_bottom {A : Type} :
  @pending A = (bot : partial_colist A).
Proof. reflexivity. Qed.

Lemma in_value_pending_eq {A : Type}
  (children : position
    (pc_container (composed_colist_descriptor A))
    (composed_colist_pending_shape A) -> partial_colist A) :
  in_value (composed_colist_pending_shape A) children = @pending A.
Proof.
  unfold pending, in_value.
  change
    ({| value_carrier :=
          in_nu (composed_colist_pending_shape A)
            (fun p => value_carrier (children p)) |} =
     {| value_carrier := nu_bottom (composed_colist_descriptor A) |}).
  f_equal; unfold nu_bottom; f_equal.
  apply functional_extensionality; intro p; destruct p.
Qed.

Lemma monotone_bcons {A : Type} (a : A) : monotone (bcons a).
Proof.
  intros x y Hxy; apply monotone_in_basis; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hxy.
Qed.

Lemma monotone_returned_cons {A : Type} (a : A) :
  monotone (returned_cons a).
Proof.
  intros x y Hxy; apply monotone_in_value; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hxy.
Qed.

Lemma continuous_colist_children {A : Type} (a : A) :
  continuous
    (fun tail : partial_colist A => composed_colist_children a tail).
Proof.
  intros d Hdirected limit Hsup.
  apply supremum_apply; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; exact Hsup.
Qed.

Lemma continuous_returned_cons {A : Type} (a : A) :
  continuous (returned_cons a).
Proof.
  unfold returned_cons.
  change
    (continuous
      ((@in_value (composed_colist_descriptor A)
          (composed_colist_cons_shape a)) ∘
       (fun tail : partial_colist A => composed_colist_children a tail))).
  apply continuous_compose.
  - apply continuous_colist_children.
  - apply continuous_in_value; discriminate.
Qed.

(** Functional extensionality is localized in this named facade.  Clients see
    the three mathematically relevant cases: no information, exact nil, and a
    returned cons layer. *)
Theorem colist_basis_ind {A : Type} (P : colist_basis A -> Prop) :
  P bpending ->
  P bnil ->
  (forall a tail, P tail -> P (bcons a tail)) ->
  forall x, P x.
Proof.
  intros Hpending Hnil Hcons x.
  apply (@basis_induction (composed_colist_descriptor A) P).
  intros [u | [u | [a u]]] children IH.
  - destruct u.
    assert (Hlayer :
      in_basis (composed_colist_pending_shape A) children = @bpending A).
    { unfold bpending, in_basis.
      change
        ({| basis_carrier :=
              in_mu (composed_colist_pending_shape A)
                (fun p => basis_carrier (children p)) |} =
         {| basis_carrier := mu_bottom (composed_colist_descriptor A) |}).
      f_equal; unfold mu_bottom; f_equal.
      apply functional_extensionality; intro p; destruct p.
    }
    change (P (in_basis (composed_colist_pending_shape A) children)).
    rewrite Hlayer; exact Hpending.
  - destruct u.
    assert (Hlayer :
      in_basis (composed_colist_nil_shape A) children = @bnil A).
    { unfold bnil, in_basis; f_equal; f_equal.
      apply functional_extensionality; intro p; destruct p.
    }
    change (P (in_basis (composed_colist_nil_shape A) children)).
    rewrite Hlayer; exact Hnil.
  - destruct u.
    set (tail := children (composed_colist_tail_position a)).
    assert (Hlayer :
      in_basis (composed_colist_cons_shape a) children = bcons a tail).
    { unfold bcons, tail, in_basis; f_equal; f_equal.
      apply functional_extensionality; intro p.
      destruct p as [p | u].
      * destruct p.
      * destruct u; reflexivity.
    }
    change (P (in_basis (composed_colist_cons_shape a) children)).
    rewrite Hlayer; apply Hcons; unfold tail; apply IH.
Qed.

Inductive partial_colist_view (A : Type) : Type :=
| view_pending
| view_returned_nil
| view_returned_cons (head : A) (tail : partial_colist A).

Arguments view_pending {A}.
Arguments view_returned_nil {A}.
Arguments view_returned_cons {A} head tail.

Definition observe_partial {A : Type}
  (x : partial_colist A) : partial_colist_view A.
Proof.
  destruct x as [[s children]].
  destruct s as [u | [u | [a u]]].
  - exact view_pending.
  - exact view_returned_nil.
  - exact (view_returned_cons a {| value_carrier := children (inr tt) |}).
Defined.

Lemma observe_pending {A : Type} :
  observe_partial (@pending A) = view_pending.
Proof. reflexivity. Qed.

Lemma observe_returned_nil {A : Type} :
  observe_partial (@returned_nil A) = view_returned_nil.
Proof. reflexivity. Qed.

Lemma observe_returned_cons {A : Type}
  (a : A) (tail : partial_colist A) :
  observe_partial (returned_cons a tail) = view_returned_cons a tail.
Proof.
  unfold observe_partial, returned_cons, composed_colist_children, in_value;
    simpl.
  destruct tail; reflexivity.
Qed.

(** ** Structural embedding of fully formed values *)

Definition colist_embed {A : Type} (x : colist A) : partial_colist A :=
  embed x.

Lemma colist_embed_nil {A : Type} :
  colist_embed (@conil A) = @returned_nil A.
Proof.
  unfold colist_embed, conil.
  rewrite embed_in.
  unfold returned_nil, composed_colist_nil_shape; f_equal; f_equal.
  apply functional_extensionality; intro p; destruct p.
Qed.

Lemma colist_embed_cons {A : Type} (a : A) (tail : colist A) :
  colist_embed (cocons a tail) = returned_cons a (colist_embed tail).
Proof.
  unfold colist_embed, cocons.
  rewrite embed_in.
  unfold returned_cons, composed_colist_cons_shape; f_equal; f_equal.
  apply functional_extensionality; intro p.
  destruct p as [p | u].
  - destruct p.
  - destruct u; reflexivity.
Qed.

(** ** Totality and realization *)

Definition colist_total {A : Type} (d : partial_colist A) : Prop :=
  Total d.

Definition colist_realizes {A : Type}
  (d : partial_colist A) (v : colist A) : Prop :=
  Realizes d v.

Lemma colist_pending_not_total {A : Type} :
  ~ colist_total (@pending A).
Proof.
  unfold colist_total, Total, pending.
  cbn; unfold nu_bottom; apply total_carrier_pending_absurd.
Qed.

Lemma colist_total_returned_nil {A : Type} :
  colist_total (@returned_nil A).
Proof.
  unfold colist_total, Total, returned_nil, in_value.
  cbn; unfold composed_colist_nil_shape.
  eapply total_returned with
    (s := composed_colist_semantic_nil_shape A).
  - reflexivity.
  - intro p; destruct p.
Qed.

Lemma colist_total_returned_cons {A : Type}
  (a : A) (tail : partial_colist A) :
  colist_total tail -> colist_total (returned_cons a tail).
Proof.
  unfold colist_total, Total, returned_cons, in_value.
  cbn; unfold composed_colist_cons_shape.
  intro Htail.
  eapply total_returned with
    (s := composed_colist_semantic_cons_shape a).
  - reflexivity.
  - intro p; destruct p as [impossible | u].
    + destruct impossible.
    + destruct u; exact Htail.
Qed.

Lemma colist_total_returned_cons_iff {A : Type}
  (a : A) (tail : partial_colist A) :
  colist_total (returned_cons a tail) <-> colist_total tail.
Proof.
  unfold colist_total, Total, returned_cons, in_value.
  cbn.
  unfold composed_colist_cons_shape.
  rewrite total_carrier_returned_iff.
  split.
  - intro Hchildren; exact (Hchildren (composed_colist_tail_position a)).
  - intros Htail p.
    destruct p as [impossible | u].
    + destruct impossible.
    + destruct u; exact Htail.
Qed.

Lemma colist_embed_total {A : Type} (v : colist A) :
  colist_total (colist_embed v).
Proof. unfold colist_total, colist_embed; apply total_embed. Qed.

Lemma colist_realizes_pending {A : Type} (v : colist A) :
  colist_realizes (@pending A) v.
Proof.
  unfold colist_realizes, Realizes, pending.
  cbn; unfold nu_bottom; apply realizes_carrier_pending.
Qed.

Lemma colist_realizes_returned_nil {A : Type} :
  colist_realizes (@returned_nil A) (@conil A).
Proof.
  unfold colist_realizes, Realizes, returned_nil, conil, in_value.
  apply realizes_carrier_returned; intro p; destruct p.
Qed.

Lemma colist_realizes_returned_cons {A : Type}
  (a : A) (partial_tail : partial_colist A) (semantic_tail : colist A) :
  colist_realizes partial_tail semantic_tail ->
  colist_realizes
    (returned_cons a partial_tail) (cocons a semantic_tail).
Proof.
  unfold colist_realizes, Realizes, returned_cons, cocons, in_value.
  intro Htail; apply realizes_carrier_returned; intro p.
  destruct p as [impossible | u].
  - destruct impossible.
  - destruct u; exact Htail.
Qed.

Lemma colist_embed_realizes {A : Type} (v : colist A) :
  colist_realizes (colist_embed v) v.
Proof. unfold colist_realizes, colist_embed; apply realizes_embed. Qed.

Lemma colist_realizes_downward {A : Type}
  (d1 d2 : partial_colist A) (v : colist A) :
  d1 ⊑ d2 ->
  colist_realizes d2 v ->
  colist_realizes d1 v.
Proof.
  unfold colist_realizes; apply realizes_downward.
Qed.

(** ** Prefixes and continuous folds on the partial carrier *)

Definition prefix {A : Type}
  (n : nat) (x : partial_colist A) : colist_basis A :=
  value_ideal x n.

Definition semantic_prefix {A : Type}
  (n : nat) (x : colist A) : colist_basis A :=
  prefix n (colist_embed x).

Definition basis_inclusion {A : Type}
  (x : colist_basis A) : partial_colist A :=
  basis_incl x.

Lemma prefix_chain {A : Type} (x : partial_colist A) :
  chain (fun n => prefix n x).
Proof.
  intro n; exact
    (@chain_value_ideal (composed_colist_descriptor A) x n).
Qed.

Definition colist_basis_fold {A B : Type}
  (pending_result nil_result : B) (step : A -> B -> B) :
  colist_basis A -> B :=
  basis_fold (composed_colist_algebra pending_result nil_result step).

Lemma colist_basis_fold_pending {A B : Type}
  (pending_result nil_result : B) (step : A -> B -> B) :
  colist_basis_fold pending_result nil_result step (@bpending A) =
  pending_result.
Proof. reflexivity. Qed.

Lemma colist_basis_fold_nil {A B : Type}
  (pending_result nil_result : B) (step : A -> B -> B) :
  colist_basis_fold pending_result nil_result step (@bnil A) = nil_result.
Proof. reflexivity. Qed.

Lemma colist_basis_fold_cons {A B : Type}
  (pending_result nil_result : B) (step : A -> B -> B)
  (a : A) (tail : colist_basis A) :
  colist_basis_fold pending_result nil_result step (bcons a tail) =
  step a (colist_basis_fold pending_result nil_result step tail).
Proof. reflexivity. Qed.

Lemma monotone_colist_basis_fold {A B : Type} `{OType B}
  (pending_result nil_result : B) (step : A -> B -> B) :
  (forall x : colist_basis A,
    pending_result ⊑
      colist_basis_fold pending_result nil_result step x) ->
  (forall a, Proper (leq ==> leq) (step a)) ->
  monotone (colist_basis_fold pending_result nil_result step).
Proof.
  intros Hbase Hstep.
  apply (@monotone_basis_fold
    (composed_colist_descriptor A) B _ pending_result
    (composed_colist_algebra pending_result nil_result step)).
  - intros children; reflexivity.
  - exact Hbase.
  - intros [u | [u | [a u]]]; destruct u; simpl.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; reflexivity.
    + intros x y Hxy; apply Hstep, Hxy.
Qed.

Definition partial_colist_fold {A B : Type} `{OType B}
  (pending_result nil_result : B) (step : A -> B -> B) :
  partial_colist A -> B :=
  composed_colist_value_fold pending_result nil_result step.

Lemma partial_colist_fold_pending {A B : Type} `{CPO B}
  (pending_result nil_result : B) (step : A -> B -> B) :
  partial_colist_fold pending_result nil_result step (@pending A) ===
  pending_result.
Proof.
  unfold partial_colist_fold.
  rewrite <- (in_value_pending_eq
    (children := fun p => match p with end)).
  apply composed_colist_value_fold_pending.
Qed.

Lemma partial_colist_fold_nil {A B : Type} `{CPO B}
  (pending_result nil_result : B) (step : A -> B -> B) :
  pending_result ⊑ nil_result ->
  partial_colist_fold pending_result nil_result step (@returned_nil A) ===
  nil_result.
Proof.
  intro Hbase.
  unfold partial_colist_fold, returned_nil.
  apply composed_colist_value_fold_nil; exact Hbase.
Qed.

Lemma partial_colist_fold_cons {A B : Type} `{CPO B}
  (pending_result nil_result : B) (step : A -> B -> B)
  (a : A) (tail : partial_colist A) :
  (forall x : colist_basis A,
    pending_result ⊑
      colist_basis_fold pending_result nil_result step x) ->
  (forall x, continuous (step x)) ->
  partial_colist_fold pending_result nil_result step
    (returned_cons a tail) ===
  step a (partial_colist_fold pending_result nil_result step tail).
Proof.
  unfold partial_colist_fold, returned_cons, colist_basis_fold.
  apply composed_colist_value_fold_cons.
Qed.

(** ** Representative structural and continuous maps *)

Definition basis_map {A B : Type} (f : A -> B) :
  colist_basis A -> colist_basis B :=
  colist_basis_fold bpending bnil (fun a tail => bcons (f a) tail).

Lemma basis_map_pending {A B : Type} (f : A -> B) :
  basis_map f (@bpending A) = @bpending B.
Proof. reflexivity. Qed.

Lemma basis_map_nil {A B : Type} (f : A -> B) :
  basis_map f (@bnil A) = @bnil B.
Proof. reflexivity. Qed.

Lemma basis_map_cons {A B : Type} (f : A -> B)
  (a : A) (tail : colist_basis A) :
  basis_map f (bcons a tail) = bcons (f a) (basis_map f tail).
Proof. reflexivity. Qed.

Lemma monotone_basis_map {A B : Type} (f : A -> B) :
  monotone (basis_map f).
Proof.
  unfold basis_map.
  apply monotone_colist_basis_fold.
  - intro x; rewrite bpending_is_bottom; apply bot_le.
  - intro a; apply monotone_bcons.
Qed.

Lemma basis_map_id {A : Type} (x : colist_basis A) :
  basis_map (fun a => a) x = x.
Proof.
  induction x using colist_basis_ind.
  - reflexivity.
  - reflexivity.
  - rewrite basis_map_cons, IHx; reflexivity.
Qed.

Definition partial_map {A B : Type} (f : A -> B) :
  partial_colist A -> partial_colist B :=
  partial_colist_fold pending returned_nil
    (fun a tail => returned_cons (f a) tail).

Lemma continuous_partial_map {A B : Type} (f : A -> B) :
  continuous (partial_map f).
Proof.
  unfold partial_map, partial_colist_fold, composed_colist_value_fold,
    value_fold.
  apply continuous_co.
  apply monotone_colist_basis_fold.
  - intro x; rewrite pending_is_bottom; apply bot_le.
  - intro a; apply monotone_returned_cons.
Qed.

Lemma partial_map_pending {A B : Type} (f : A -> B) :
  partial_map f (@pending A) === @pending B.
Proof.
  unfold partial_map; apply partial_colist_fold_pending.
Qed.

Lemma partial_map_nil {A B : Type} (f : A -> B) :
  partial_map f (@returned_nil A) === @returned_nil B.
Proof.
  unfold partial_map; apply partial_colist_fold_nil.
  rewrite pending_is_bottom; apply bot_le.
Qed.

Lemma partial_map_cons {A B : Type} (f : A -> B)
  (a : A) (tail : partial_colist A) :
  partial_map f (returned_cons a tail) ===
  returned_cons (f a) (partial_map f tail).
Proof.
  change
    (partial_colist_fold (@pending B) (@returned_nil B)
      (fun x t => returned_cons (f x) t) (returned_cons a tail) ===
     returned_cons (f a)
       (partial_colist_fold (@pending B) (@returned_nil B)
         (fun x t => returned_cons (f x) t) tail)).
  apply (@partial_colist_fold_cons A (partial_colist B) _ _
    (@pending B) (@returned_nil B)
    (fun x t => returned_cons (f x) t) a tail).
  - intro x; rewrite pending_is_bottom; apply bot_le.
  - intro x; apply continuous_returned_cons.
Qed.
