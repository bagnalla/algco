(** * Complete partial orders and suprema/infima operators. *)

From Coq Require Import
  Basics
  PeanoNat
  Equivalence
  ClassicalChoice
  IndefiniteDescription (* for suprema/infima *)
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From algco Require Import
  axioms
  misc
  order
  tactics
.

Local Open Scope order_scope.

(** [A] is a dCPO (directed-complete partial order) whenever suprema of
    directed countable collections exist. *)
Class dCPO (A : Type) `{OType A} : Prop :=
  { exists_sup : forall f : nat -> A, directed f -> exists s, supremum s f }.

(** [A] is a ldCPO (lower-directed-complete partial order) whenever
    infima of downward-directed countable collections exist. *)
Class ldCPO (A : Type) `{OType A} : Prop :=
  { exists_inf : forall f : nat -> A, downward_directed f -> exists s, infimum s f }.

Class dLattice (A : Type) {o : OType A} `{@dCPO A o} `{@ldCPO A o} : Prop := {}.

(** Pointed lattice.  For convenience -- deviates slightly from
    standard definition by quantifying over only countable
    collections. *)
Class pLattice (A : Type) {o : OType A} {p : @PType _ o} : Prop := {
    lattice_exists_sup : forall f : nat -> A, exists s, supremum s f
  ; lattice_exists_inf : forall f : nat -> A, exists s, infimum s f
  }.

#[global]
  Instance pLattice_dCPO {A} `{pLattice A} : dCPO A.
Proof. firstorder. Qed.
#[global] Hint Resolve pLattice_dCPO : order.

#[global]
  Instance pLattice_ldCPO {A} `{pLattice A} : ldCPO A.
Proof. firstorder. Qed.
#[global] Hint Resolve pLattice_ldCPO : order.

#[global]
  Instance pLattice_dLattice {A} `{pLattice A} : dLattice A.
Qed.
#[global] Hint Resolve pLattice_dLattice : order.


Lemma ex_ex_supremum {A} `{OType A} (f : nat -> A) :
  exists x : A, (exists b : A, supremum b f) -> supremum x f.
Proof.
  destruct (classic (exists a, supremum a f)).
  - destruct H0 as [a Ha]; exists a; intros; auto.
  - exists (f O); intros [a Ha]; exfalso; apply H0; exists a; auto.
Qed.

(** Primitive non-constructive supremum operation for ordered type
    [A]. Given a countable collection [f] of elements of type [A],
    produce an element [a] such that [a] is the supremum of [f]
    whenever such a supremum provably exists. Derived from excluded
    middle + indefinite description. *)
Definition sup_prim {A} `{OType A} (f : nat -> A)
  : { a : A | (exists b, supremum b f) -> supremum a f } :=
  constructive_indefinite_description _ (ex_ex_supremum _).

Lemma ex_ex_infimum {A} `{OType A} (f : nat -> A) :
  exists x : A, (exists b : A, infimum b f) -> infimum x f.
Proof.
  destruct (classic (exists a, infimum a f)).
  - destruct H0 as [a Ha]; exists a; intros; auto.
  - exists (f O); intros [a Ha]; exfalso; apply H0; exists a; auto.
Qed.

(* See above. *)
Definition inf_prim {A} `{OType A} (f : nat -> A)
  : { a : A | (exists b, infimum b f) -> infimum a f } :=
  constructive_indefinite_description _ (ex_ex_infimum _).

(* Take the supremum of countable collection [f]. *)
Definition sup {A} `{OType A} (f : nat -> A) : A := proj1_sig (sup_prim f).

(* [sup f] is the supremum of [f] whenever [A] is a dCPO and [f] is
   directed. *)
Lemma sup_spec {A} `{dCPO A} (f : nat -> A) :
  directed f -> supremum (sup f) f.
Proof. intro Hf; unfold sup; destruct sup_prim; simpl; apply s, H0; auto. Qed.

Lemma lattice_sup_spec {A} `{pLattice A} (f : nat -> A) :
  supremum (sup f) f.
Proof. unfold sup; destruct sup_prim; simpl; apply s; firstorder. Qed.

(* Take the infimum of countable collection [f]. *)
Definition inf {A} `{OType A} (f : nat -> A) : A := proj1_sig (inf_prim f).

(* [inf f] is the infimum of [f] whenever [A] is an ldCPO and [f] is
   downward-directed. *)
Lemma inf_spec {A} `{ldCPO A} (f : nat -> A) :
  downward_directed f -> infimum (inf f) f.
Proof. intro Hf; unfold inf; destruct inf_prim; simpl; apply i, H0; auto. Qed.

Lemma lattice_inf_spec {A} `{pLattice A} (f : nat -> A) :
  infimum (inf f) f.
Proof. unfold inf; destruct inf_prim; simpl; apply i; firstorder. Qed.

#[global]
  Instance pLattice_arrow {A B} `{pLattice B} : pLattice (A -> B).
Proof.
  constructor; intro f.
  - exists (fun x => sup (fun i => f i x)).
    apply supremum_apply.
    intro a; apply lattice_sup_spec.
  - exists (fun x => inf (fun i => f i x)).
    apply infimum_apply.
    intro a; apply lattice_inf_spec.
Qed.
#[global] Hint Resolve pLattice_arrow : order.

(** [Prop] has suprema and infima. *)

(* #[global] *)
(*   Instance dCPO_Prop : dCPO Prop. *)
(* Proof. *)
(*   constructor; intro f; exists (exists i, f i); split. *)
(*   - intros i Hi; exists i; auto. *)
(*   - intros ub Hub [i Hi]; eapply Hub; eauto. *)
(* Qed. *)
(* #[global] Hint Resolve dCPO_Prop : order. *)

(* #[global] *)
(*   Instance ldCPO_Prop : ldCPO Prop. *)
(* Proof. *)
(*   constructor; intros f; exists (forall i, f i); split. *)
(*   - intros i Hi; auto. *)
(*   - intros ub Hub x i; apply Hub; auto. *)
(* Qed. *)
(* #[global] Hint Resolve ldCPO_Prop : order. *)

(* #[global] *)
(*   Instance dLattice_Prop : dLattice Prop. Qed. *)
(* #[global] Hint Resolve dLattice_Prop : order. *)

#[global]
  Instance Lattice_Prop : pLattice Prop.
Proof.
  constructor; intro f.
  - exists (exists i, f i); split.
    + intros i Hi; exists i; auto.
    + intros ub Hub [i Hi]; eapply Hub; eauto.
  - exists (forall i, f i); split.
    + intros i Hi; auto.
    + intros ub Hub x i; apply Hub; auto.
Qed.
#[global] Hint Resolve Lattice_Prop : order.

(* #[global] *)
(*   Instance dCPO_bool : dCPO bool. *)
(* Proof. *)
(*   constructor; intro f. *)
(*   destruct (classic (exists i, f i = true)). *)
(*   - exists true; split. *)
(*     + intro i; simpl; unfold bool_le; destruct (f i); auto. *)
(*     + intros x Hx; destruct x; try reflexivity. *)
(*       destruct H as [i H]; specialize (Hx i). *)
(*       rewrite H in Hx; destruct Hx. *)
(*   - exists false; split. *)
(*     + intro i; destruct (f i) eqn:Hfi; try reflexivity. *)
(*       exfalso; apply H; exists i; auto. *)
(*     + intros x Hx; destruct x; reflexivity. *)
(* Qed. *)
(* #[global] Hint Resolve dCPO_bool : order. *)

(* #[global] *)
(*   Instance ldCPO_bool : ldCPO bool. *)
(* Proof. *)
(*   constructor; intro f. *)
(*   destruct (classic (exists i, f i = false)). *)
(*   - exists false; split. *)
(*     + intro i; simpl; unfold bool_le; destruct (f i); auto. *)
(*     + intros x Hx; destruct x; try reflexivity. *)
(*       destruct H as [i H]; specialize (Hx i). *)
(*       rewrite H in Hx; destruct Hx. *)
(*   - exists true; split. *)
(*     + intro i; destruct (f i) eqn:Hfi; try reflexivity. *)
(*       exfalso; apply H; exists i; auto. *)
(*     + intros x Hx; destruct x; reflexivity. *)
(* Qed. *)
(* #[global] Hint Resolve ldCPO_bool : order. *)

(* #[global] *)
(*   Instance dLattice_bool : dLattice bool. Qed. *)
(* #[global] Hint Resolve dLattice_bool : order. *)

#[global]
  Instance Lattice_bool : pLattice bool.
Proof.
  constructor; intro f.
  - destruct (classic (exists i, f i = true)).
    + exists true; split.
      * intro i; simpl; unfold bool_le; destruct (f i); auto.
      * intros x Hx; destruct x; try reflexivity.
        destruct H as [i H]; specialize (Hx i).
        rewrite H in Hx; destruct Hx.
    + exists false; split.
      * intro i; destruct (f i) eqn:Hfi; try reflexivity.
        exfalso; apply H; exists i; auto.
      * intros x Hx; destruct x; reflexivity.
  - destruct (classic (exists i, f i = false)).
    + exists false; split.
      * intro i; simpl; unfold bool_le; destruct (f i); auto.
      * intros x Hx; destruct x; try reflexivity.
        destruct H as [i H]; specialize (Hx i).
        rewrite H in Hx; destruct Hx.
    + exists true; split.
      * intro i; destruct (f i) eqn:Hfi; try reflexivity.
        exfalso; apply H; exists i; auto.
      * intros x Hx; destruct x; reflexivity.
Qed.
#[global] Hint Resolve Lattice_Prop : order.

#[global]
  Instance ldCPO_arrow {A B} `{ldCPO B} : ldCPO (A -> B).
Proof.
  constructor; intros f Hf.
  exists (fun x => inf (fun n => f n x)).
  assert (Hf': forall x, downward_directed (fun i => f i x)).
  { intros x j k.
    specialize (Hf j k); destruct Hf as [l [Hl Hl']].
    exists l; auto. }
  split.
  - intros i x; specialize (Hf' x).
    apply inf_spec in Hf'; apply Hf'.
  - intros g Hlb x.
    specialize (Hf' x).
    apply inf_spec in Hf'.
    apply Hf'; intro; apply Hlb.
Qed.

#[global]
  Instance dCPO_arrow {A B} `{dCPO B} : dCPO (A -> B).
Proof.
  constructor; intros f Hf.
  exists (fun x => sup (fun n => f n x)).
  assert (Hf': forall x, directed (fun i => f i x)).
  { intros x j k.
    specialize (Hf j k); destruct Hf as [l [Hl Hl']].
    exists l; auto. }
  split.
  - intros i x; specialize (Hf' x).
    apply sup_spec in Hf'; apply Hf'.
  - intros g Hub x.
    specialize (Hf' x).
    apply sup_spec in Hf'.
    apply Hf'; intro; apply Hub.
Qed.

#[global]
  Instance dCPO_prod {A B} `{dCPO A} `{dCPO B} : dCPO (A * B).
Proof.
  constructor; intros ch Hch.
  destruct H0.
  specialize (exists_sup0 (fst ∘ ch) (directed_fst _ Hch)).
  destruct exists_sup0 as [a Ha].
  destruct H2.
  specialize (exists_sup0 (snd ∘ ch) (directed_snd _ Hch)).
  destruct exists_sup0 as [b Hb].
  exists (a, b); apply supremum_prod; auto.
Qed.

#[global]
  Instance dCPO_sum {A B} `{dCPO A} `{dCPO B} : dCPO (A + B).
Proof.
  constructor; intros ch Hch.
  destruct (classic (exists i a, ch i = inl a)) as [Ha|Ha].
  { destruct Ha as [i [a Ha]].
    set (ch_a := fun j => match (ch j) with
                       | inl x => x
                       | inr _ => a
                       end).
    assert (Hch_a: directed ch_a).
    { intros j k; specialize (Hch j k); destruct Hch as [z [Hiz Hjz]].
      unfold ch_a.
      exists z; split.
      - destruct (ch j) eqn:Hchj.
        + destruct (ch z) eqn:Hchz; auto; inv Hiz.
        + destruct (ch z) eqn:Hchz; try reflexivity; inv Hiz.
      - destruct (ch k) eqn:Hchk.
        + destruct (ch z) eqn:Hchz; auto; inv Hjz.
        + destruct (ch z) eqn:Hchz; try reflexivity; inv Hjz. }
    destruct H0; apply exists_sup0 in Hch_a; clear exists_sup0.
    destruct (classic (exists i b, ch i = inr b)).
    { destruct H0 as [j [b Hb]].
      specialize (Hch i j).
      destruct Hch as [k [Hik Hjk]].
      rewrite Ha in Hik.
      rewrite Hb in Hjk.
      destruct (ch k).
      - inv Hjk.
      - inv Hik. }
    destruct Hch_a as [x Hx].
    exists (inl x).
    destruct Hx as [Hub Hlub].
    split.
    - intro j.
      specialize (Hub j).
      unfold ch_a in Hub.
      destruct (ch j) eqn:Hchj; auto.
      exfalso; apply H0; exists j, b; auto.
    - intros [y|y] Hy.
      + apply Hlub; intro j; specialize (Hy j).
        unfold ch_a; destruct (ch j) eqn:Hchj; auto; inv Hy; simpl in *.
      + specialize (Hy i); rewrite Ha in Hy; inv Hy. }
  destruct (ch O) eqn:Hch0.
  { exfalso; apply Ha; exists O, a; auto. }
  set (ch_b := fun j => match (ch j) with
                     | inl _ => b
                     | inr y => y
                     end).
  assert (Hch_b: directed ch_b).
  { intros j k; specialize (Hch j k); destruct Hch as [z [Hiz Hjz]].
    unfold ch_b.
    exists z; split.
    - destruct (ch j) eqn:Hchj.
      + destruct (ch z) eqn:Hchz; try reflexivity; inv Hiz.
      + destruct (ch z) eqn:Hchz; auto; inv Hiz.
    - destruct (ch k) eqn:Hchk.
      + destruct (ch z) eqn:Hchz; try reflexivity; inv Hjz.
      + destruct (ch z) eqn:Hchz; auto; inv Hjz. }
  destruct H2; apply exists_sup0 in Hch_b; clear exists_sup0.
  destruct Hch_b as [y [Hub Hlub]].
  exists (inr y); split.
  - intro i; specialize (Hub i).
    unfold ch_b in Hub.
    destruct (ch i) eqn:Hchi; auto.
    destruct (Hch O i) as [k [HOk Hik]].
    rewrite Hch0 in HOk.
    rewrite Hchi in Hik.
    destruct (ch k).
    + inv HOk.
    + inv Hik.
  - intros x Hx.
    destruct x.
    + specialize (Hx O); rewrite Hch0 in Hx; inv Hx.
    + apply Hlub; intro i.
      specialize (Hx i).
      unfold ch_b.
      destruct (ch i); auto; inv Hx.
Qed.

Lemma le_sup {A} `{dCPO A} (f : nat -> A) (a : A) (i : nat) :
  directed f ->
  a ⊑ f i ->
  a ⊑ sup f.
Proof.
  intros Hf Hleq.
  generalize (sup_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma lattice_le_sup {A} `{pLattice A} (f : nat -> A) (a : A) (i : nat) :
  a ⊑ f i ->
  a ⊑ sup f.
Proof.
  intros Hleq.
  generalize (lattice_sup_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma le_inf {A} `{ldCPO A} (f : nat -> A) (a : A) :
  downward_directed f ->
  lower_bound a f ->
  a ⊑ inf f.
Proof.
  intros Hf Hbound; generalize (inf_spec f); intros [Hlb Hglb]; auto.
Qed.

Lemma lattice_le_inf {A} `{pLattice A} (f : nat -> A) (a : A) :
  lower_bound a f ->
  a ⊑ inf f.
Proof.
  intros Hbound; generalize (lattice_inf_spec f); intros [Hlb Hglb]; auto.
Qed.

Lemma ge_sup {A} `{dCPO A} (f : nat -> A) (a : A) :
  directed f ->
  upper_bound a f ->
  sup f ⊑ a.
Proof.
  intros Hf Hbound; generalize (sup_spec f); intros [Hub Hlub]; auto.
Qed.

Lemma lattice_ge_sup {A} `{pLattice A} (f : nat -> A) (a : A) :
  upper_bound a f ->
  sup f ⊑ a.
Proof.
  intros Hbound; generalize (lattice_sup_spec f); intros [Hub Hlub]; auto.
Qed.

Lemma ge_inf {A} `{ldCPO A} (f : nat -> A) (a : A) (i : nat) :
  downward_directed f ->
  f i ⊑ a ->
  inf f ⊑ a.
Proof.
  intros Hf Hleq.
  generalize (inf_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma lattice_ge_inf {A} `{pLattice A} (f : nat -> A) (a : A) (i : nat) :
  f i ⊑ a ->
  inf f ⊑ a.
Proof.
  intros Hleq.
  generalize (lattice_inf_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma supremum_sup {A} `{dCPO A} (f : nat -> A) (a : A) :
  supremum a f ->
  sup f === a.
Proof.
  intros Hsup; eapply supremum_unique; eauto.
  unfold sup; destruct (sup_prim f); apply s; exists a; auto.
Qed.

Lemma infimum_inf {A} `{ldCPO A} (f : nat -> A) (a : A) :
  infimum a f ->
  inf f === a.
Proof.
  intros Hinf; eapply infimum_unique; eauto.
  unfold inf; destruct (inf_prim f); apply i; exists a; auto.
Qed.

Lemma sup_apply {A B} `{dCPO B} (f : nat -> A -> B) (x : A) :
  directed f ->
  sup f x === sup (fun i => f i x).
Proof.
  intro Hf; symmetry; apply supremum_sup, apply_supremum, sup_spec; auto.
Qed.

Lemma lattice_sup_apply {A B} `{pLattice B} (f : nat -> A -> B) (x : A) :
  sup f x === sup (fun i => f i x).
Proof.
  symmetry; apply supremum_sup, apply_supremum, lattice_sup_spec; auto.
Qed.

Lemma inf_apply {A B} `{ldCPO B} (f : nat -> A -> B) (x : A) :
  downward_directed f ->
  inf f x === inf (fun i => f i x).
Proof.
  symmetry; apply infimum_inf; auto with order.
  apply apply_infimum, inf_spec; auto.
Qed.

Lemma lattice_inf_apply {A B} `{pLattice B} (f : nat -> A -> B) (x : A) :
  inf f x === inf (fun i => f i x).
Proof.
  symmetry; apply infimum_inf; auto with order.
  apply apply_infimum, lattice_inf_spec; auto.
Qed.

Lemma continuous_sup {A B} `{dCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  continuous f ->
  directed ch ->
  f (sup ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply sup_spec; auto.
Qed.

Lemma cocontinuous_sup {A B} `{dCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  cocontinuous f ->
  directed ch ->
  f (sup ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply sup_spec; auto.
Qed.

Lemma wcontinuous_sup {A B} `{dCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  wcontinuous f ->
  chain ch ->
  f (sup ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply sup_spec; auto with order.
Qed.

Lemma dec_continuous_inf {A B} `{ldCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  dec_continuous f ->
  downward_directed ch ->
  f (inf ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply inf_spec; auto.
Qed.

Lemma dec_cocontinuous_inf {A B} `{ldCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  dec_cocontinuous f ->
  downward_directed ch ->
  f (inf ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply inf_spec; auto.
Qed.

Lemma dec_wcontinuous_inf {A B} `{ldCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  dec_wcontinuous f ->
  dec_chain ch ->
  f (inf ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply inf_spec; auto with order.
Qed.

Lemma Proper_sup {A} `{dCPO A} (f g : nat -> A) :
  directed f ->
  directed g ->
  f === g ->
  sup f === sup g.
Proof.
  intros Hf Hg Hfg.
  eapply supremum_unique.
  - apply sup_spec; auto.
  - rewrite Hfg; apply sup_spec; auto.
Qed.

Lemma sup_shift {A} `{dCPO A} (f : nat -> A) :
  chain f ->
  sup (shift f) === sup f.
Proof.
  intro Hf; apply supremum_sup; auto with order.
  apply supremum_shift; auto.
  apply sup_spec; auto with order.
Qed.

Lemma sup_shift' {A} `{dCPO A} (f g : nat -> A) :
  chain f ->
  g === shift f ->
  sup f === sup g.
Proof.
  intros Hch Heq; subst.
  symmetry.
  apply supremum_sup.
  rewrite Heq; apply supremum_shift, sup_spec; auto with order.
Qed.

Lemma inf_shift' {A} `{ldCPO A} (f g : nat -> A) :
  dec_chain f ->
  g === shift f ->
  inf f === inf g.
Proof.
  intros Hch Heq; subst.
  symmetry.
  apply infimum_inf.
  rewrite Heq; apply infimum_shift, inf_spec; auto with order.
Qed.

Lemma sup_intro (P : nat -> Prop) (i : nat) :
  directed P ->
  P i ->
  sup P.
Proof.
  intros Hdir HP.
  generalize (sup_spec _ Hdir); intros [Hub Hlub].
  eapply Hub; eauto.
Qed.

Lemma sup_elim (P : nat -> Prop) :
  directed P ->
  sup P ->
  exists i, P i.
Proof.
  intros Hdir HP.
  generalize (sup_spec _ Hdir); intros [Hub Hlub].
  apply Hlub; auto.
  intros i H'; exists i; apply H'.
Qed.

(** Compute the least fixed point of F by taking the supremum of the
    chain obtained by repeated iteration of F starting from z. *)
Definition iter {A} `{OType A} (F : A -> A) (z : A) : A :=
  sup (iter_n F z).

(** Compute the greatest fixed point of F by taking the infimum of the
    decreasing chain obtained by repeated iteration of F starting from z. *)
Definition dec_iter {A} `{OType A} (F : A -> A) (z : A) : A :=
  inf (iter_n F z).

(** [iter F z] is a fixed point of [F]. *)
Lemma iter_unfold {A} `{dCPO A} (F : A -> A) (z : A) :
  wcontinuous F ->
  z ⊑ F z ->
  iter F z === F (iter F z).
Proof.
  unfold iter.
  intros HF Hle.
  assert (Hchain: chain (iter_n F z)).
  { apply chain_iter_n'; auto.
    apply wcontinuous_monotone; auto. }
  eapply wcontinuous_sup in HF.
  2: { eauto. }
  rewrite HF; clear HF Hle.
  unfold compose.
  apply sup_shift'; auto.
  apply equ_arrow; intro i; reflexivity.
Qed.

(** [dec_iter F z] is a fixed point of [F]. *)
Lemma dec_iter_unfold {A} `{ldCPO A} (F : A -> A) (z : A) :
  dec_wcontinuous F ->
  F z ⊑ z ->
  dec_iter F z === F (dec_iter F z).
Proof.
  unfold dec_iter.
  intros HF Hle.
  assert (Hchain: dec_chain (iter_n F z)).
  { apply dec_chain_iter_n'; auto.
    apply dec_wcontinuous_monotone; auto. }
  eapply dec_wcontinuous_inf in HF; eauto.
  rewrite HF; clear HF Hle.
  unfold compose.
  apply inf_shift'; auto.
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma sup_apply_ext {A B} `{dCPO B} {_ : ExtType B} (f : nat -> A -> B) (x : A) :
  directed f ->
  sup f x = sup (fun i => f i x).
Proof.
  intro Hf; symmetry; apply ext, supremum_sup, apply_supremum, sup_spec; auto.
Qed.

Lemma monotone_sup {A} `{dCPO A} (f g : nat -> A) :
  directed f ->
  directed g ->
  (forall i, f i ⊑ g i) ->
  sup f ⊑ sup g.
Proof.
  intros Hf Hg Hfg; apply ge_sup; auto.
  intro i; etransitivity; eauto; apply sup_spec; auto.
Qed.

Lemma monotone_inf {A} `{ldCPO A} (f g : nat -> A) :
  downward_directed f ->
  downward_directed g ->
  (forall i, f i ⊑ g i) ->
  inf f ⊑ inf g.
Proof.
  intros Hf Hg Hfg; apply le_inf; auto.
  intro i; etransitivity; eauto; apply inf_spec; auto.
Qed.

Lemma Proper_inf {A} `{ldCPO A} (f g : nat -> A) :
  downward_directed f ->
  downward_directed g ->
  f === g ->
  inf f === inf g.
Proof.
  intros Hf Hg Hfg; split; apply monotone_inf; auto; intro i; apply Hfg.
Qed.

Lemma continuous_supP {A} `{dCPO A} (f : A -> Prop) (ch : nat -> A) :
  continuous f ->
  directed ch ->
  f (sup ch) <-> sup (f ∘ ch).
Proof.
  intros Hf Hch.
  apply equ_iff, continuous_sup; auto.
Qed.

Lemma sup_const {A} `{dCPO A} (a : A) :
  sup (fun _ => a) === a.
Proof.
  eapply supremum_unique.
  { apply sup_spec; auto with order. }
  apply supremum_const.
Qed.

Lemma sup_const' {A} `{dCPO A} (f : nat -> A) (a : A) :
  f === const a ->
  sup f === a.
Proof.
  intro Hf.
  rewrite equ_arrow in Hf.
  unfold const in Hf.
  eapply supremum_unique.
  - apply sup_spec; intros ? j; exists j; split; rewrite !Hf; reflexivity.
  - apply supremum_const'; apply equ_arrow; intro i; apply Hf.
Qed.

Lemma sup_true_exists_i (f : nat -> bool) :
  sup f = true ->
  exists i, f i = true.
Proof.
  intro Hsup.
  contra H.
  assert (f = const false).
  { ext i; unfold const; apply not_ex_all_not with (n:=i) in H.
    destruct (f i); congruence. }
  subst.
  apply eq_equ in Hsup.
  unfold const in Hsup.
  rewrite sup_const in Hsup.
  apply ext in Hsup; congruence.
Qed.
