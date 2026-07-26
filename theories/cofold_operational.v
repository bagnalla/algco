(** * A small operational model of an extracted colist cofold.

    The generic layer distinguishes a pending computation from an atomically
    returned result and permits a lifted step to ignore its recursive
    argument.  The concrete model is specialized to [colist_existsb]; it
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
  cpo
  order
.

(** ** Flat operational results *)

(** The flat information order has one pending result below every returned
    value, while distinct returned values are incomparable. *)
Inductive flat_le {A : Type} : option A -> option A -> Prop :=
| flat_le_pending : forall result,
    flat_le None result
| flat_le_returned : forall value,
    flat_le (Some value) (Some value).

(** A pending computation makes no claim about its denotation.  A returned
    atomic value must equal that denotation. *)
Definition flat_realizes {A : Type} (result : option A) (value : A) : Prop :=
  match result with
  | None => True
  | Some value' => value = value'
  end.

Definition flat_step_monotone {A B : Type}
  (step : A -> option B -> option B) : Prop :=
  forall a x y, flat_le x y -> flat_le (step a x) (step a y).

Definition flat_step_sound {A B : Type}
  (f : A -> B -> B) (step : A -> option B -> option B) : Prop :=
  forall a result value,
    flat_realizes result value ->
    flat_realizes (step a result) (f a value).

(** A fuelled model of the hand-written lazy extraction equation for
    [cofold].  The operational step receives the recursive result as a flat
    approximation, so it may return without demanding that result. *)
Fixpoint cofold_eval
  {A B : Type} `{o : OType B} `{@PType B o}
  (fuel : nat) (step : A -> option B -> option B) (l : colist A) : option B :=
  match fuel with
  | O => None
  | S fuel' =>
      match l with
      | conil => Some ⊥
      | cocons a l' => step a (cofold_eval fuel' step l')
      end
  end.

Lemma flat_le_some_inv {A : Type} (x : A) (result : option A) :
  flat_le (Some x) result ->
  result = Some x.
Proof. intro Hle; inversion Hle; reflexivity. Qed.

Lemma flat_le_refl {A : Type} (result : option A) :
  flat_le result result.
Proof. destruct result; constructor. Qed.

Lemma flat_le_trans {A : Type} (x y z : option A) :
  flat_le x y ->
  flat_le y z ->
  flat_le x z.
Proof.
  intros Hxy Hyz; destruct Hxy.
  - constructor.
  - exact Hyz.
Qed.

Lemma cofold_eval_S_le
  {A B : Type} `{o : OType B} `{@PType B o}
  (fuel : nat) (step : A -> option B -> option B) (l : colist A) :
  flat_step_monotone step ->
  flat_le (cofold_eval fuel step l) (cofold_eval (S fuel) step l).
Proof.
  intro Hstep; revert l; induction fuel; intro l.
  - simpl; constructor.
  - destruct l as [|a l]; simpl.
    + constructor.
    + apply Hstep, IHfuel.
Qed.

Lemma cofold_eval_S
  {A B : Type} `{o : OType B} `{@PType B o}
  (fuel : nat) (step : A -> option B -> option B)
  (l : colist A) (b : B) :
  flat_step_monotone step ->
  cofold_eval fuel step l = Some b ->
  cofold_eval (S fuel) step l = Some b.
Proof.
  intros Hstep Hreturn.
  pose proof (cofold_eval_S_le fuel l Hstep) as Hle.
  rewrite Hreturn in Hle; apply flat_le_some_inv in Hle; exact Hle.
Qed.

Lemma cofold_eval_le
  {A B : Type} `{o : OType B} `{@PType B o}
  (fuel fuel' : nat) (step : A -> option B -> option B) (l : colist A) :
  flat_step_monotone step ->
  (fuel <= fuel')%nat ->
  flat_le (cofold_eval fuel step l) (cofold_eval fuel' step l).
Proof.
  intros Hstep Hle; induction Hle.
  - apply flat_le_refl.
  - eapply flat_le_trans.
    + apply IHHle.
    + apply cofold_eval_S_le, Hstep.
Qed.

Lemma cofold_eval_monotone
  {A B : Type} `{o : OType B} `{@PType B o}
  (fuel fuel' : nat) (step : A -> option B -> option B)
  (l : colist A) (b : B) :
  flat_step_monotone step ->
  (fuel <= fuel')%nat ->
  cofold_eval fuel step l = Some b ->
  cofold_eval fuel' step l = Some b.
Proof.
  intros Hstep Hle; induction Hle; intro Hreturn.
  - exact Hreturn.
  - apply cofold_eval_S; auto.
Qed.

(** The logical-relation theorem connecting the operational evaluator to
    AlgCo's denotational [cofold]. *)
Theorem cofold_eval_realizes
  {A B : Type} `{o : OType B} `{@ExtType B o}
  `{@PType B o} `{@CPO B o}
  (f : A -> B -> B) (step : A -> option B -> option B)
  (fuel : nat) (l : colist A) :
  (forall a, continuous (f a)) ->
  flat_step_sound f step ->
  flat_realizes (cofold_eval fuel step l) (cofold f l).
Proof.
  intros Hcontinuous Hstep; revert l; induction fuel; intro l.
  - simpl; apply I.
  - destruct l as [|a l]; simpl.
    + rewrite cofold_nil'; reflexivity.
    + rewrite cofold_cons'; auto.
Qed.

Corollary cofold_eval_sound
  {A B : Type} `{o : OType B} `{@ExtType B o}
  `{@PType B o} `{@CPO B o}
  (f : A -> B -> B) (step : A -> option B -> option B)
  (fuel : nat) (l : colist A) (b : B) :
  (forall a, continuous (f a)) ->
  flat_step_sound f step ->
  cofold_eval fuel step l = Some b ->
  cofold f l = b.
Proof.
  intros Hcontinuous Hstep Hreturn.
  pose proof
    (@cofold_eval_realizes
      A B o _ _ _ f step fuel l Hcontinuous Hstep) as Hsound.
  rewrite Hreturn in Hsound; exact Hsound.
Qed.

(** ** Lazy Boolean existential *)

(** [None] means that the computation has not returned within the supplied
    fuel.  [Some b] means that it has returned the ordinary Boolean value [b].
    In particular, [None] and [Some false] are the operational and semantic
    bottoms that the denotational result type [bool] alone cannot
    distinguish. *)
Definition colist_existsb_step {A : Type}
  (P : A -> bool) (a : A) (result : option bool) : option bool :=
  if P a then Some true else result.

Lemma colist_existsb_step_monotone {A : Type} (P : A -> bool) :
  flat_step_monotone (colist_existsb_step P).
Proof.
  intros a x y Hle; unfold colist_existsb_step.
  destruct (P a); auto using flat_le_returned.
Qed.

Lemma colist_existsb_step_sound {A : Type} (P : A -> bool) :
  flat_step_sound (fun a b => P a || b) (colist_existsb_step P).
Proof.
  intros a result value Hrealizes; unfold colist_existsb_step.
  destruct (P a); simpl; auto.
Qed.

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

Lemma colist_existsb_eval_is_cofold_eval {A : Type}
  (fuel : nat) (P : A -> bool) (l : colist A) :
  colist_existsb_eval fuel P l =
  cofold_eval fuel (colist_existsb_step P) l.
Proof.
  revert l; induction fuel as [|fuel IH]; intro l.
  - reflexivity.
  - destruct l as [|a l].
    + reflexivity.
    + simpl; unfold colist_existsb_step.
      destruct (P a); auto.
Qed.

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
  intro Hreturn; rewrite colist_existsb_eval_is_cofold_eval in Hreturn.
  unfold colist_existsb.
  eapply (cofold_eval_sound (step := colist_existsb_step P)).
  - apply continuous_existsb_step.
  - apply colist_existsb_step_sound.
  - exact Hreturn.
Qed.

Corollary colist_existsb_returns_sound {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_returns P l b ->
  colist_existsb P l = b.
Proof.
  intros [fuel Hreturn]; eapply colist_existsb_eval_sound; eauto.
Qed.

(** A big-step semantics for the specialized lazy target equation.  The hit
    rule deliberately has no premise for evaluating the recursive tail. *)
Inductive colist_existsb_bigstep {A : Type} (P : A -> bool)
  : colist A -> bool -> Prop :=
| colist_existsb_bigstep_nil :
    colist_existsb_bigstep P conil false
| colist_existsb_bigstep_hit : forall a l,
    P a = true ->
    colist_existsb_bigstep P (cocons a l) true
| colist_existsb_bigstep_miss : forall a l b,
    P a = false ->
    colist_existsb_bigstep P l b ->
    colist_existsb_bigstep P (cocons a l) b.

Lemma colist_existsb_eval_bigstep {A : Type}
  (fuel : nat) (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_eval fuel P l = Some b ->
  colist_existsb_bigstep P l b.
Proof.
  revert l b; induction fuel; intros l b Hreturn.
  - discriminate.
  - destruct l as [|a l]; simpl in Hreturn.
    + inversion Hreturn; subst; constructor.
    + destruct (P a) eqn:Ha.
      * inversion Hreturn; subst; apply colist_existsb_bigstep_hit, Ha.
      * apply colist_existsb_bigstep_miss; auto.
Qed.

Lemma colist_existsb_bigstep_returns {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_bigstep P l b ->
  colist_existsb_returns P l b.
Proof.
  intro Heval; induction Heval.
  - exists 1%nat; reflexivity.
  - exists 1%nat; simpl; rewrite H; reflexivity.
  - destruct IHHeval as [fuel Hreturn].
    exists (S fuel); simpl; rewrite H; exact Hreturn.
Qed.

Theorem colist_existsb_bigstep_iff_returns {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_bigstep P l b <->
  colist_existsb_returns P l b.
Proof.
  split.
  - apply colist_existsb_bigstep_returns.
  - intros [fuel Hreturn]; eapply colist_existsb_eval_bigstep; eauto.
Qed.

Corollary colist_existsb_bigstep_sound {A : Type}
  (P : A -> bool) (l : colist A) (b : bool) :
  colist_existsb_bigstep P l b ->
  colist_existsb P l = b.
Proof.
  intro Heval; apply colist_existsb_returns_sound.
  apply colist_existsb_bigstep_returns, Heval.
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

Corollary bad_bool_has_no_bigstep_evaluation (b : bool) :
  ~ colist_existsb_bigstep (const false) (nats O) b.
Proof.
  intro Heval; apply (bad_bool_does_not_return (b := b)).
  apply colist_existsb_bigstep_returns, Heval.
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
