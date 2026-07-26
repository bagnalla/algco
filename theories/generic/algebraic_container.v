(** * Algebraic structure for pointed container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Program.Equality
.

From algco Require Import
  aCPO
  axioms
  cpo
  order
.

From algco.generic Require Import
  container
  pointed_container
  finitary_container
.

(** The canonical finite truncations are dense in every generic
    coinductive value.  This theorem needs only a pointed signature: neither
    deciding the bottom shape nor enumerating recursive positions is involved. *)
Theorem incl_truncate_nu_supremum (C : pointed_container)
  (x : nu (pc_container C)) :
  @supremum nat (nu (pc_container C)) (OType_container_nu C) x
    (fun n => incl_mu (truncate_nu n x)).
Proof.
  split.
  - intro n; apply incl_truncate_nu_le.
  - revert x; cofix CH; intros x ub Hub.
    destruct x as [s children].
    pose proof (Hub 1) as Hone; simpl in Hone.
    dependent destruction Hone.
    + constructor.
    + constructor; intro p.
      apply CH; intro n.
      specialize (Hub (S n)); simpl in Hub.
      dependent destruction Hub.
      * destruct (bottom_position_absurd C p).
      * apply H.
Qed.

(** Child projection transports an existing supremum pointwise.  As on the
    inductive side, leastness follows by replacing one child of the limiting
    layer with an arbitrary upper bound. *)
Lemma supremum_nu_child (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (ch : nat -> nu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s) :
  supremum (in_nu s children) ch ->
  supremum (children p) (nu_child_chain C s p ch).
Proof.
  intros [Hub Hlub]; split.
  - apply upper_bound_nu_child_chain; exact Hub.
  - intros ub Hub_child.
    set (replacement := replace_child p ub children).
    assert (Hcandidate : upper_bound (in_nu s replacement) ch).
    { intro i.
      destruct (nu_le_layer_inv C (Hub i)) as
        [[bottom_children Hi] | [childreni [Hi Hchildreni]]].
      - rewrite Hi; constructor.
      - rewrite Hi; constructor; intro q.
        destruct (classicT (q = p)) as [Hqp | Hqp].
        + subst q; unfold replacement; rewrite replace_child_same.
          specialize (Hub_child i).
          unfold nu_child_chain in Hub_child.
          rewrite Hi, nu_child_same in Hub_child.
          exact Hub_child.
        + unfold replacement; rewrite replace_child_other; auto.
    }
    pose proof (Hlub _ Hcandidate) as Hlayer.
    pose proof
      (@nu_child_monotone C s p (in_nu s children)
        (in_nu s replacement) Hlayer) as Hchild.
    rewrite !nu_child_same in Hchild.
    unfold replacement in Hchild; rewrite replace_child_same in Hchild.
    exact Hchild.
Qed.

Lemma nu_le_exposed_not_bottom (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  ~ nu_le (dpc_pointed C) (in_nu s children)
      (nu_bottom (dpc_pointed C)).
Proof.
  intros Hs Hle; unfold nu_bottom in Hle.
  dependent destruction Hle; apply Hs; reflexivity.
Qed.

(** A nonbottom supremum exposes its outer shape at some stage. *)
Lemma supremum_nu_exposed_stage (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (ch : nat -> nu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  supremum (in_nu s children) ch ->
  exists i,
    exists children' : position (pc_container (dpc_pointed C)) s ->
        nu (pc_container (dpc_pointed C)),
      ch i = in_nu s children' /\
      forall p, nu_le (dpc_pointed C) (children' p) (children p).
Proof.
  intros Hs [Hub Hlub].
  destruct (strong_LPO (fun n => nu_exposes_dec C (ch n))) as [Hex | Hnone].
  - destruct Hex as [i Hi].
    destruct (nu_le_layer_inv C (Hub i)) as
      [[bottom_children Hbottom] | [childreni [Hshape Hchildren]]].
    + rewrite Hbottom in Hi; simpl in Hi.
      exfalso; apply Hi; reflexivity.
    + exists i, childreni; split; assumption.
  - assert (Hbottom : upper_bound (nu_bottom (dpc_pointed C)) ch).
    { intro i.
      destruct (ch i) as [t childreni] eqn:Hi.
      destruct (@bottom_shape_dec C t) as [Ht | Ht].
      - dependent destruction Ht; constructor.
      - exfalso; apply Hnone; exists i; rewrite Hi; exact Ht.
    }
    apply Hlub in Hbottom.
    exfalso; eapply nu_le_exposed_not_bottom; eauto.
Qed.

(** Projecting a child after one additional truncation contains at least the
    truncation of the projected coinductive child.  On a shape mismatch both
    projections carry no information, so the one-sided order is sufficient
    and avoids equality between empty child functions. *)
Lemma truncate_nu_child_le_mu_child (C : decidable_pointed_container)
  (n : nat)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  (x : nu (pc_container (dpc_pointed C))) :
  mu_le (dpc_pointed C) (truncate_nu n (nu_child C s p x))
    (mu_child C s p (truncate_nu (S n) x)).
Proof.
  destruct x as [t children].
  destruct (classicT (s = t)) as [Hst | Hst].
  - dependent destruction Hst.
    rewrite nu_child_same.
    change
      (mu_le (dpc_pointed C) (truncate_nu n (children p))
        (mu_child C s p
          (in_mu s (fun q => truncate_nu n (children q))))).
    rewrite mu_child_same.
    apply mu_le_refl.
  - assert (Hchild :
      nu_child C s p (in_nu t children) = nu_bottom (dpc_pointed C)).
    { unfold nu_child.
      destruct (classicT (s = t)) as [H | H].
      - exfalso; apply Hst, H.
      - reflexivity.
    }
    rewrite Hchild; destruct n; simpl; constructor.
Qed.

(** Every finite truncation is continuous.  At a nonbottom limit, an exposed
    stage forces any upper bound of the truncated stages to have the same
    outer shape.  Continuity then follows recursively at each child; no finite
    synchronization across positions is needed. *)
Theorem truncate_nu_continuous (C : decidable_pointed_container) (n : nat) :
  @continuous
    (nu (pc_container (dpc_pointed C)))
    (mu (pc_container (dpc_pointed C)))
    (OType_container_nu (dpc_pointed C))
    (OType_container_mu (dpc_pointed C))
    (fun x => truncate_nu (C := dpc_pointed C) n x).
Proof.
  induction n as [|n IH].
  - intros ch Hch x Hsup; unfold compose; simpl; split.
    + intro i; apply mu_le_refl.
    + intros ub Hub; unfold mu_bottom; constructor.
  - intros ch Hch x Hsup; unfold compose.
    destruct x as [s children].
    change
      (supremum
        (in_mu s (fun p => truncate_nu n (children p)))
        (fun i => truncate_nu (S n) (ch i))).
    destruct (@bottom_shape_dec C s) as [Hs | Hs].
    + dependent destruction Hs; split.
      * intro i.
        change
          (mu_le (dpc_pointed C) (truncate_nu (S n) (ch i))
            (truncate_nu (S n)
              (in_nu (bottom_shape (dpc_pointed C)) children))).
        apply truncate_nu_monotone, (proj1 Hsup).
      * intros ub Hub; constructor.
    + split.
      * intro i.
        change
          (mu_le (dpc_pointed C) (truncate_nu (S n) (ch i))
            (truncate_nu (S n) (in_nu s children))).
        apply truncate_nu_monotone, (proj1 Hsup).
      * intros ub Hub.
        destruct (supremum_nu_exposed_stage C Hs Hsup) as
          [j [childrenj [Hj Hchildrenj]]].
        pose proof (Hub j) as Hubj.
        change
          (mu_le (dpc_pointed C) (truncate_nu (S n) (ch j)) ub)
          in Hubj.
        rewrite Hj in Hubj; simpl in Hubj.
        destruct (mu_le_exposed_inv C Hs Hubj) as
          [childrenub [Hub_shape Hchildrenub]].
        rewrite Hub_shape in Hub |- *.
        constructor; intro p.
        pose proof
          (@supremum_nu_child C s children ch p Hsup) as Hchild_sup.
        pose proof
          (@directed_nu_child_chain C s p ch Hch) as Hchild_directed.
        pose proof
          (IH (nu_child_chain C s p ch) Hchild_directed
            (children p) Hchild_sup) as Htruncated_child_sup.
        apply (proj2 Htruncated_child_sup); intro i.
        unfold compose.
        pose proof (Hub i) as Hi.
        change
          (mu_le (dpc_pointed C) (truncate_nu (S n) (ch i))
            (in_mu s childrenub)) in Hi.
        pose proof
          (@mu_child_monotone C s p
            (truncate_nu (S n) (ch i)) (in_mu s childrenub) Hi)
          as Hprojected.
        rewrite mu_child_same in Hprojected.
        eapply mu_le_trans.
        -- apply truncate_nu_child_le_mu_child.
        -- exact Hprojected.
Qed.

(** The canonical inclusion and truncation sequence form the generic dense
    presentation.  Laws for this data are assembled in the [aCPO] instance
    below. *)
#[global]
Instance Dense_pointed_container (C : pointed_container) :
  @Dense
    (nu (pc_container C))
    (mu (pc_container C))
    (OType_container_nu C)
    (OType_container_mu C) :=
  {| incl := incl_mu
   ; ideal := fun x n => truncate_nu n x
  |}.

(** Finiteness is needed here only through compactness of [mu C].  Directed
    completeness and truncation continuity use the decidable pointed part,
    while density itself was proved for every pointed signature. *)
#[global]
Instance aCPO_finitary_container (C : finitary_pointed_container) :
  @aCPO
    (nu (pc_container (fpc_pointed C)))
    (mu (pc_container (fpc_pointed C)))
    (OType_container_nu (fpc_pointed C))
    (OType_container_mu (fpc_pointed C))
    (Compact_finitary_container_mu C)
    (@Dense_pointed_container (fpc_pointed C))
    (CPO_decidable_container_nu (fpc_decidable C)).
Proof.
  constructor.
  - intros x y; apply incl_mu_order_iff.
  - intro x; apply chain_truncate_nu.
  - intros x y Hxy n; apply truncate_nu_monotone, Hxy.
  - intro n; apply truncate_nu_continuous.
  - intro x; apply incl_truncate_nu_supremum.
Qed.
