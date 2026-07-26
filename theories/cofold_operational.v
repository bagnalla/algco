(** * A small operational model of an extracted colist cofold.

    This first model is deliberately specialized to [colist_existsb].  It
    treats exposing a colist constructor and evaluating [P a] as terminating
    atomic operations, and isolates divergence caused by following the
    recursive argument of the extracted [cofold] equation. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Bool
.

Local Open Scope bool_scope.

From algco Require Import
  colist
  order
.

(** [None] means that the computation has not returned within the supplied
    fuel.  [Some b] means that it has returned the ordinary Boolean value [b].
    In particular, [None] and [Some false] are the operational and semantic
    bottoms that the denotational result type [bool] alone cannot
    distinguish. *)
Fixpoint colist_existsb_eval {A : Type}
  (fuel : nat) (P : A -> bool) (l : colist A) : option bool :=
  match fuel with
  | O => None
  | S fuel' =>
      match l with
      | conil => Some false
      | cocons a l' =>
          if P a then Some true else colist_existsb_eval fuel' P l'
      end
  end.

Definition colist_existsb_returns {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) : Prop :=
  exists fuel, colist_existsb_eval fuel P l = Some b.

(** More fuel cannot invalidate a returned result. *)
Lemma colist_existsb_eval_S {A : Type}
  (fuel : nat) (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_eval fuel P l = Some b ->
  colist_existsb_eval (S fuel) P l = Some b.
Proof.
  revert l b; induction fuel; intros l b Hreturn.
  - discriminate.
  - destruct l as [|a l]; simpl in *.
    + exact Hreturn.
    + destruct (P a); auto.
Qed.

Lemma colist_existsb_eval_monotone {A : Type}
  (fuel fuel' : nat) (P : A -> bool) (l : colist A) (b : bool) :
  (fuel <= fuel')%nat ->
  colist_existsb_eval fuel P l = Some b ->
  colist_existsb_eval fuel' P l = Some b.
Proof.
  intro Hle; induction Hle; intro Hreturn.
  - exact Hreturn.
  - apply colist_existsb_eval_S, IHHle, Hreturn.
Qed.

(** Reaching an actual end marker returns the semantic bottom [false].  Fuel
    exhaustion, by contrast, returns [None]. *)
Lemma colist_existsb_eval_conil {A : Type}
  (fuel : nat) (P : A -> bool) :
  colist_existsb_eval (S fuel) P (@conil A) = Some false.
Proof. reflexivity. Qed.

Corollary colist_existsb_returns_conil {A : Type} (P : A -> bool) :
  colist_existsb_returns P (@conil A) false.
Proof. exists 1%nat; reflexivity. Qed.

(** A finite positive witness makes the lazy disjunction return. *)
Lemma colist_existsb_eval_witness {A : Type}
  (P : A -> bool) (l : colist A) (k : nat) :
  nth' (fun a => P a = true) k l ->
  colist_existsb_eval (S k) P l = Some true.
Proof.
  intro Hnth; induction Hnth; simpl.
  - rewrite H; reflexivity.
  - destruct (P a); auto.
Qed.

Corollary colist_existsb_returns_witness {A : Type}
  (P : A -> bool) (l : colist A) (k : nat) :
  nth' (fun a => P a = true) k l ->
  colist_existsb_returns P l true.
Proof.
  intro Hnth; exists (S k); apply colist_existsb_eval_witness, Hnth.
Qed.

(** The step used by [colist_existsb] is continuous in AlgCo's semantic
    Boolean order. *)
Lemma continuous_existsb_step {A : Type} (P : A -> bool) (a : A) :
  continuous (fun b => P a || b).
Proof. destruct (P a); simpl; apply continuous_const || apply continuous_id. Qed.

Lemma colist_existsb_nil {A : Type} (P : A -> bool) :
  colist_existsb P (@conil A) = false.
Proof. unfold colist_existsb; rewrite cofold_nil'; reflexivity. Qed.

Lemma colist_existsb_cons {A : Type}
  (P : A -> bool) (a : A) (l : colist A) :
  colist_existsb P (cocons a l) = P a || colist_existsb P l.
Proof.
  unfold colist_existsb; rewrite cofold_cons'; auto using continuous_existsb_step.
Qed.

(** Finite operational results agree with the denotational Coq [cofold]. *)
Theorem colist_existsb_eval_sound {A : Type}
  (fuel : nat) (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_eval fuel P l = Some b ->
  colist_existsb P l = b.
Proof.
  revert l b; induction fuel; intros l b Hreturn.
  - discriminate.
  - destruct l as [|a l]; simpl in Hreturn.
    + inversion Hreturn; subst; apply colist_existsb_nil.
    + destruct (P a) eqn:Ha.
      * inversion Hreturn; subst.
        rewrite colist_existsb_cons, Ha; reflexivity.
      * apply IHfuel in Hreturn.
        rewrite colist_existsb_cons, Ha, Hreturn; reflexivity.
Qed.

Corollary colist_existsb_returns_sound {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_returns P l b ->
  colist_existsb P l = b.
Proof.
  intros [fuel Hreturn]; eapply colist_existsb_eval_sound; eauto.
Qed.

(** The all-false infinite input never reaches [conil] and never finds a
    witness, so every finite evaluation remains pending. *)
Lemma colist_existsb_eval_nats_false (fuel start : nat) :
  colist_existsb_eval fuel (const false) (nats start) = None.
Proof.
  revert start; induction fuel; intro start; simpl; auto.
Qed.

Corollary bad_bool_eval_pending (fuel : nat) :
  colist_existsb_eval fuel (const false) (nats O) = None.
Proof. apply colist_existsb_eval_nats_false. Qed.

Corollary bad_bool_does_not_return (b : bool) :
  ~ colist_existsb_returns (const false) (nats O) b.
Proof.
  intros [fuel Hreturn].
  rewrite bad_bool_eval_pending in Hreturn; discriminate.
Qed.

(** Nevertheless, its extensional AlgCo denotation is the returned Boolean
    value [false]. *)
Corollary bad_bool_denotes_false :
  bad_bool = false.
Proof. unfold bad_bool; apply bad_bool_false. Qed.

Theorem bad_bool_denotational_operational_gap :
  bad_bool = false /\
  forall b, ~ colist_existsb_returns (const false) (nats O) b.
Proof.
  split.
  - apply bad_bool_denotes_false.
  - apply bad_bool_does_not_return.
Qed.
