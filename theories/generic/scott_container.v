(** * Arbitrary-directed compactness for container fixed points. *)

Set Implicit Arguments.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Basics
  IndefiniteDescription
  List
  Program.Equality
.

From algco Require Import
  aCPO
  axioms
  order
.

From algco.generic Require Import
  container
  pointed_container
  finitary_container
.

(** Standard compactness relative to arbitrary nonempty directed families.
    The supremum is supplied relationally, so this definition does not require
    a [DCPO] instance or choose a supremum operation. *)
Polymorphic Definition scott_compact {A : Type} `{OType A} (x : A) : Prop :=
  forall (I : Type) (d : I -> A),
    inhabited I ->
    directed d ->
    forall s, supremum s d -> leq x s ->
    exists i, leq x (d i).

(** Scott compactness implies the sequence-based notion used by the current
    AlgCo hierarchy. *)
Lemma scott_compact_compact {A : Type} `{OType A} (x : A) :
  scott_compact x -> compact x.
Proof.
  intros Hcompact d Hdirected Hsup.
  assert (Hxx : leq x x) by reflexivity.
  destruct
    (Hcompact nat d (inhabits 0) Hdirected x Hsup Hxx)
    as [i Hxi].
  exists i; split.
  - exact ((proj1 Hsup) i).
  - exact Hxi.
Qed.

(** A finite family of members of an arbitrary nonempty directed family has a
    common upper member. *)
Lemma directed_finite_upper_family {A I J : Type} `{OType A}
  (d : I -> A) :
  inhabited I ->
  directed d ->
  forall (index : J -> I) (xs : list J),
    exists k, forall x, In x xs -> leq (d (index x)) (d k).
Proof.
  intros [i0] Hdirected index xs.
  induction xs as [|x xs [k Hk]].
  - exists i0; intros y Hy; inversion Hy.
  - destruct (Hdirected (index x) k) as [l [Hxl Hkl]].
    exists l; intros y [Hy | Hy].
    + subst y; exact Hxl.
    + transitivity (d k); [apply Hk; exact Hy | exact Hkl].
Qed.

(** Project one child from every member of an arbitrarily indexed family. *)
Definition nu_child_family (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  {I : Type}
  (d : I -> nu (pc_container (dpc_pointed C))) :
  I -> nu (pc_container (dpc_pointed C)) :=
  fun i => nu_child C s p (d i).

Lemma directed_nu_child_family (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  {I : Type}
  (d : I -> nu (pc_container (dpc_pointed C))) :
  directed d -> directed (nu_child_family C s p d).
Proof.
  intros Hdirected i j.
  destruct (Hdirected i j) as [k [Hik Hjk]].
  exists k; split; apply nu_child_monotone; assumption.
Qed.

Lemma upper_bound_nu_child_family (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s)
  {I : Type}
  (d : I -> nu (pc_container (dpc_pointed C))) :
  upper_bound (in_nu s children) d ->
  upper_bound (children p) (nu_child_family C s p d).
Proof.
  intros Hub i.
  unfold nu_child_family.
  rewrite <- nu_child_same.
  apply nu_child_monotone, Hub.
Qed.

Lemma supremum_nu_child_family (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  {I : Type}
  (d : I -> nu (pc_container (dpc_pointed C)))
  (p : position (pc_container (dpc_pointed C)) s) :
  supremum (in_nu s children) d ->
  supremum (children p) (nu_child_family C s p d).
Proof.
  intros [Hub Hlub]; split.
  - apply upper_bound_nu_child_family; exact Hub.
  - intros ub Hub_child.
    set (replacement := replace_child p ub children).
    assert (Hcandidate : upper_bound (in_nu s replacement) d).
    { intro i.
      destruct (nu_le_layer_inv C (Hub i)) as
        [[bottom_children Hi] | [childreni [Hi Hchildreni]]].
      - rewrite Hi; constructor.
      - rewrite Hi; constructor; intro q.
        destruct (classicT (q = p)) as [Hqp | Hqp].
        + subst q; unfold replacement; rewrite replace_child_same.
          specialize (Hub_child i).
          unfold nu_child_family in Hub_child.
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

(** A nonbottom supremum of an arbitrarily indexed family has a member that
    already exposes its outer shape.  Unlike the sequence proof, this uses
    ordinary excluded middle on an existential and no LPO. *)
Lemma supremum_nu_exposed_member (C : decidable_pointed_container)
  (s : shape (pc_container (dpc_pointed C)))
  (children : position (pc_container (dpc_pointed C)) s ->
    nu (pc_container (dpc_pointed C)))
  {I : Type}
  (d : I -> nu (pc_container (dpc_pointed C))) :
  s <> bottom_shape (dpc_pointed C) ->
  supremum (in_nu s children) d ->
  exists i,
    exists children' : position (pc_container (dpc_pointed C)) s ->
        nu (pc_container (dpc_pointed C)),
      d i = in_nu s children' /\
      forall p, nu_le (dpc_pointed C) (children' p) (children p).
Proof.
  intros Hs [Hub Hlub].
  destruct (classicT (exists i, nu_exposes C (d i))) as [Hex | Hnone].
  - destruct Hex as [i Hi].
    destruct (nu_le_layer_inv C (Hub i)) as
      [[bottom_children Hbottom] | [childreni [Hshape Hchildren]]].
    + rewrite Hbottom in Hi; simpl in Hi.
      exfalso; apply Hi; reflexivity.
    + exists i, childreni; split; assumption.
  - assert (Hbottom : upper_bound (nu_bottom (dpc_pointed C)) d).
    { intro i.
      destruct (d i) as [t childreni] eqn:Hi.
      destruct (@bottom_shape_dec C t) as [Ht | Ht].
      - dependent destruction Ht; constructor.
      - exfalso; apply Hnone; exists i; rewrite Hi; exact Ht.
    }
    apply Hlub in Hbottom.
    exfalso; eapply nu_le_exposed_not_bottom; eauto.
Qed.

(** Every included finite basis element is compact in the standard
    arbitrary-directed sense.  This is the compactness theorem needed to view
    [mu C] as a basis of the pointed partial domain [nu C], rather than merely
    as a compact ordered type in isolation. *)
Theorem incl_mu_scott_compact (C : finitary_pointed_container)
  (b : mu (pc_container (fpc_pointed C))) :
  @scott_compact
    (nu (pc_container (fpc_pointed C)))
    (OType_container_nu (fpc_pointed C))
    (incl_mu b).
Proof.
  induction b as [s children IH].
  unfold scott_compact in *.
  intros I d Hinhabited Hdirected limit Hsup Hbelow.
  destruct (@bottom_shape_dec (fpc_decidable C) s) as [Hs | Hs].
  - dependent destruction Hs.
    destruct Hinhabited as [i0].
    exists i0; simpl; constructor.
  - change
      (nu_le (fpc_pointed C)
        (in_nu s (fun p => incl_mu (children p))) limit) in Hbelow.
    destruct (nu_le_exposed_inv (fpc_decidable C) Hs Hbelow) as
      [limit_children [Hlimit Hchildren_limit]].
    rewrite Hlimit in Hsup.
    destruct
      (@supremum_nu_exposed_member
        (fpc_decidable C) s limit_children I d Hs Hsup) as
      [j [childrenj [Hj Hchildrenj]]].
    assert (Hchild_witness : forall
      p : position (pc_container (fpc_pointed C)) s,
      exists i,
        nu_le (fpc_pointed C) (incl_mu (children p))
          ((nu_child_family (fpc_decidable C) s p d) i)).
    { intro p.
      destruct
        (IH p I (nu_child_family (fpc_decidable C) s p d)
          Hinhabited
          (directed_nu_child_family (fpc_decidable C) s p Hdirected)
          (limit_children p)
          (@supremum_nu_child_family (fpc_decidable C) s limit_children I d p
            Hsup)
          (Hchildren_limit p)) as [i Hi].
      exists i; exact Hi.
    }
    pose (index := fun p : position (pc_container (fpc_pointed C)) s =>
      proj1_sig
        (constructive_indefinite_description
          (fun i =>
            nu_le (fpc_pointed C) (incl_mu (children p))
              ((nu_child_family (fpc_decidable C) s p d) i))
          (Hchild_witness p))).
    assert (Hindex : forall
      p : position (pc_container (fpc_pointed C)) s,
      nu_le (fpc_pointed C) (incl_mu (children p))
        ((nu_child_family (fpc_decidable C) s p d) (index p))).
    { intro p; unfold index.
      destruct
        (constructive_indefinite_description
          (fun i =>
            nu_le (fpc_pointed C) (incl_mu (children p))
              ((nu_child_family (fpc_decidable C) s p d) i))
          (Hchild_witness p)) as [i Hi].
      exact Hi.
    }
    destruct
      (@directed_finite_upper_family
        (nu (pc_container (fpc_pointed C))) I
        (position (pc_container (fpc_pointed C)) s)
        (OType_container_nu (fpc_pointed C))
        d Hinhabited Hdirected index (@position_enum C s)) as [k Hk].
    destruct (Hdirected j k) as [l [Hjl Hkl]].
    exists l.
    rewrite Hj in Hjl.
    destruct (nu_le_exposed_inv (fpc_decidable C) Hs Hjl) as
      [childrenl [Hl Hchildrenl]].
    change
      (nu_le (fpc_pointed C)
        (in_nu s (fun p => incl_mu (children p))) (d l)).
    rewrite Hl; constructor; intro p.
    transitivity
      ((nu_child_family (fpc_decidable C) s p d) (index p)).
    + exact (Hindex p).
    + transitivity ((nu_child_family (fpc_decidable C) s p d) k).
      * unfold nu_child_family; apply nu_child_monotone, Hk.
        apply position_enum_complete.
      * transitivity ((nu_child_family (fpc_decidable C) s p d) l).
        -- unfold nu_child_family; apply nu_child_monotone; exact Hkl.
        -- unfold nu_child_family; rewrite Hl, nu_child_same; reflexivity.
Qed.
