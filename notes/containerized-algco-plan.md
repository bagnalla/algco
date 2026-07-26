# Containerized AlgCo prototype plan

## Status and decision boundary

This is an exploratory plan for a possible successor architecture to AlgCo.
It is not yet a decision to rewrite the current development. The existing
modules remain the reference implementation and the artifact corresponding to
the [AlgCo paper](https://arxiv.org/abs/2301.09802).

The hypothesis to test is:

> Retaining an open-recursive, container-like presentation of a coinductive
> type should let us derive its semantic algebraic CPO, compact basis,
> operational lifting, finite observations, and realization relation from one
> description.

Proof ergonomics is a primary acceptance criterion, not a later polishing
step.  For the common instances, users should define operations over familiar
native types and reduce their main obligations to ordinary structural
induction over familiar basis elements.  Shapes, positions, dependent
transports, and representation conversions may occur in the generic kernel or
the one-time instance proof, but should not occur in routine program proofs.

A rewrite is justified only if one complete vertical slice is clearer and at
least as usable as the current type-specific development. Until that decision
point, all generic work should live alongside the current modules.
Milestones 2F and 2G now pass that test for both linear colist `comap` and
branching Boolean-cotree `map`, Milestone 2H isolates the smallest derivation
experiment justified by their duplication, and Milestone 2I successfully
factors their fold/cofold layer theorem.  Milestone 2J then shows that semantic
container combinators derive the required descriptor capabilities without a
reified code language.  The remaining decision is whether native-presentation
factoring and the operational layer justify a larger rewrite, not whether
native constructor equations can survive the representation boundary.

This plan grew out of the investigation in
[`cofold-extraction-productivity.md`](cofold-extraction-productivity.md). That
report remains the record of the extraction problem and the observation-indexed
productivity results. This document concerns the broader architecture suggested
by that work.  Provisional architectural conclusions that cut across individual
prototype milestones are collected separately in
[`algco2-design.md`](algco2-design.md).

## Milestone 1 checkpoint: fixed-point representation

Status on July 26, 2026: **technically successful with qualifications**.

The first feasibility spike is implemented in:

- [`theories/generic/container.v`](../theories/generic/container.v), containing
  containers, their inductive and coinductive fixed points, and structural
  bisimilarity;
- [`theories/generic/colist_instance.v`](../theories/generic/colist_instance.v),
  containing the pointed colist signature and conversions to the existing
  native `list` and `colist` types.

### Positive results

- Coq accepts the generic `μ` and `ν` definitions with recursive children
  represented by `Pos s → μ C` and `Pos s → ν C`.
- The automatically generated induction principle for `μ C` supplies an
  induction hypothesis for every recursive position.
- The pointed colist container can be defined directly with an empty position
  type for `conil` and `unit` for `cocons`.
- Dependent pattern matching in the conversions is local and manageable.
- Both inductive conversions are inverse, and both coinductive conversions are
  inverse up to their respective structural bisimilarities.
- The coinductive conversion proofs use the same one-layer unfolding style as
  the native colist development; no new guardedness workaround was required.

### Equality and axiom audit

| Result | Additional assumption |
|---|---|
| Generic `ν` bisimilarity reflexivity and symmetry | none |
| Generic `ν` bisimilarity transitivity | `Eq_rect_eq.eq_rect_eq` |
| `μ ColistC → list → μ ColistC` round trip | functional extensionality |
| `list → μ ColistC → list` round trip | none |
| Both coinductive round trips as bisimulations | none |
| Native-colist round trip as Coq equality | existing `colist_ext` axiom |

Transitivity is the first place where eliminating equal dependent container
indices becomes nontrivial. The current proof uses `dependent destruction` and
therefore inherits `eq_rect_eq`, an axiom already present elsewhere in this
development. Before treating generic bisimilarity as foundational, a short
follow-up should determine whether a path-explicit formulation can avoid that
assumption without making routine proofs substantially worse.

CoFixpoints do not unfold by reflexivity when their result is observed only by
an equality goal. Explicit one-step unfolding lemmas solve this, just as
`colist.unf_eq` does for the native type.

### Extraction finding

Direct extraction of the generic fixed points succeeds, but Coq erases their
dependent container indices to a representation of the following form:

```haskell
type Shape = Any
type Position = Any

data Mu = In_mu Shape (Position -> Mu)
data Nu = In_nu Shape (Position -> Nu)
```

The specialized colist conversions consequently contain `unsafeCoerce` at
shape and child accesses.  This is an expected way for Haskell extraction to
erase source-level dependencies, not by itself a correctness failure.  It is
reasonable for closed extracted code whose values and uses all originate in
well-typed Coq.

It is less attractive as a public Haskell API: exposed constructors would let
handwritten code violate the erased shape/position invariant, all container
instances share an opaque representation, and malformed external values could
reach branches that were impossible in Coq.  The prototype should therefore
keep both extraction routes open.  Native datatypes with proved
specializations are likely to provide the clearer public boundary, while
direct generic extraction remains a valid option for closed programs.

### Checkpoint decision

Milestone 1 provides enough evidence to continue to the generic order and
truncation experiment. It does **not** justify a source or runtime rewrite yet.
The next milestone should preserve native colists as the extraction boundary
and compare every generically derived relation with the existing native one.

## Milestone 1.5 checkpoint: proof-level colist specialization

Status on July 26, 2026: **the first specialization boundary works**.

[`theories/generic/pointed_container.v`](../theories/generic/pointed_container.v)
now adds the least-shape structure needed by AlgCo and derives:

- inductive and coinductive approximation preorders;
- least elements and the corresponding `OType` and `PType` instances;
- structural inclusion from `μ C` into `ν C`;
- depth truncation from `ν C` into `μ C`;
- monotonicity, growth of successive truncations, and soundness of an included
  truncation below its source value.

The colist instance proves that this is not merely an abstract parallel API:

- generic `μ` approximation is equivalent to native `list_le`;
- generic `ν` approximation is equivalent to native `colist_le`;
- generic inclusion computes as native `inj`;
- generic truncation computes as `prefix`, and inclusion after truncation
  computes as `coprefix`.

Consequently, dependent matches and container indices can remain inside the
generic kernel and the one-time instance module.  Statements presented to a
colist user can still use only `list`, `colist`, `list_le`, `colist_le`, `inj`,
`prefix`, and `coprefix`.

The assumption audit follows the pattern already seen in Milestone 1:

| Result | Additional assumption |
|---|---|
| Generic order reflexivity | none |
| Generic order transitivity and the resulting preorder instances | `Eq_rect_eq.eq_rect_eq` |
| Generic monotonicity, truncation growth, and truncation soundness | none |
| Generic/native order correspondence | none |
| Inclusion and truncation computation lemmas | none |
| Canonical native-colist order equivalence stated through both round trips | existing `colist_ext` axiom |

Thus dependent equality has not leaked into the colist-facing statements, but
it remains in the current proof that the generic relations are transitive.  A
path-explicit order formulation remains worth testing before treating this
kernel as foundational; it is not necessary to answer the present ergonomics
question.

At this checkpoint the prototype had not yet derived the complete algebraic
CPO structure or reconstructed a representative operation such as `comap`.
Milestones 2A through 2F below record that vertical slice, including its
definition, continuity proof, constructor equations, and proof-ergonomics
comparison.

## Milestone 2A checkpoint: directed completeness

Status on July 26, 2026: **the generic CPO construction works**.

[`theories/generic/finitary_container.v`](../theories/generic/finitary_container.v)
records two distinct interfaces that the initial plan had conflated:

```text
decidable pointed container
  = pointed container + a test for the bottom shape

finitary pointed container
  = decidable pointed container
  + a complete finite enumeration of every position type
```

The separation is mathematically useful.  Directed completeness of `ν C`
does not require finite branching.  The bottom-shape test is enough to find an
exposed stage of a directed chain.  Finite position enumeration first becomes
necessary when combining finitely many witnesses in the compactness proof.

The checkpoint adds:

- order reflection of `incl : μ C → ν C`, completing its order-embedding law;
- the basis truncation chain and its included value chain;
- a total child projection for arbitrary container layers;
- directedness and upper-bound lemmas for projected child chains;
- a generic coinductive supremum `nu_sup`;
- proofs that `nu_sup` is an upper bound and the least upper bound;
- a `CPO (ν C)` instance for every decidable pointed container.

The colist instance supplies both interfaces without requiring decidable
equality on the element type.  Pattern matching distinguishes `hole` from
`cons a`, and the position enumerations are `[]` and `[tt]`.

The generic supremum follows the existing colist and cotree construction.  It
uses `LPO_option` to choose an exposed stage.  To project a requested child
from an arbitrary layer, it additionally uses AlgCo's strong classical
equality to compare shapes; a mismatch maps to semantic bottom.  Directedness
proves that this convention cannot discard information in a relevant chain.

### Milestone 2A assumption audit

| Result | Additional assumption |
|---|---|
| Colist decidable/finitary interface data | none |
| Inclusion order reflection and generic chain statements | `Eq_rect_eq.eq_rect_eq` |
| Child projection itself and `nu_sup` definition | existing `classic` and constructive indefinite description |
| Child projection computation at an equal shape | the same classical assumptions plus `Eq_rect_eq.eq_rect_eq` |
| Directed child chains and the `CPO` correctness theorem | the same classical assumptions plus `Eq_rect_eq.eq_rect_eq` |

No assumption is new to AlgCo: the concrete CPO constructions already use the
classical package, and the dependent generic order already used `eq_rect_eq`.
The generic construction does make classical shape comparison computationally
visible inside the semantic supremum.  This is acceptable for the current
semantic experiment but should be kept out of a public extracted runtime
representation unless a specialization removes it.

Compactness is completed as Milestone 2B below, Milestone 2C completes density
through truncation and the resulting `aCPO` instance, and Milestone 2F records
the eventual `comap` test of the user-facing proof interface.

## Milestone 2B checkpoint: compactness of the generic basis

Status on July 26, 2026: **the finiteness stress test succeeds**.

[`theories/generic/finitary_container.v`](../theories/generic/finitary_container.v)
now proves that every element of `μ C` is compact when `C` has a complete
finite enumeration of each position type.  It registers the resulting
`Compact (μ C)` instance.  The colist module additionally registers a
concrete instance for `μ ColistC`; this avoids asking typeclass search to
reconstruct an entire finitary-container package from the carrier type.

This specialization exposed a structural typeclass issue rather than a mere
search inconvenience: `μ (pc_container C)` retains the underlying container
but not enough information to reconstruct which pointed or finitary package
supplies its order.  Multiple packages may legitimately share that carrier.
The alternatives and current recommendation are recorded in the
[AlgCo 2 design sketch](algco2-design.md#typeclass-resolution-and-descriptor-identity).

The proof factors into four reusable pieces:

1. A finite family of indices into a directed sequence has a common upper
   stage.
2. Shape-aware child projection on `μ C` is monotone and preserves
   directedness.
3. If `inμ s children` is a supremum, each `children p` is the supremum of
   the corresponding projected sequence.  Leastness is proved by replacing
   that one child with an arbitrary upper bound and applying leastness of the
   whole layer.
4. Structural induction on a finite tree gives one stage for each recursive
   child.  The position enumeration and directedness merge those finitely
   many stages.  A separately chosen exposed stage ensures that the merged
   stage has the required outer shape.

The last point is the precise role of finitary branching.  Neither decidable
equality nor a duplicate-free enumeration of positions is needed.  The proof
uses only the completeness statement `p ∈ position_enum s`.  It also does not
use the `CPO (ν C)` construction: compactness is an intrinsic property of the
inductive basis order and arbitrary countable directed suprema that happen to
exist there.

The generic theorem returns AlgCo order equivalence `ch i === x`, exactly as
the definition of `compact` requires.  The existing native theorem
`list_compact` returns Coq equality because native list approximation is
antisymmetric.  The new `colist_mu_compact` and `list_to_mu_compact` lemmas
make the generic result available at the colist specialization boundary; the
order correspondence also yields `colist_mu_compact_exact`, with the same
exact-stage conclusion for the generic colist basis.  The native theorem
remains the more ergonomic result for code and proofs stated entirely over
`list`.

### Milestone 2B assumption audit

`Print Assumptions` gives the following boundary:

| Result | Additional assumption |
|---|---|
| Finite directed-stage aggregation | none |
| Child projection, child-supremum transport, and exposed-stage inversion | existing `classic`, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` |
| Generic compactness and its `Compact` instance | the same three assumptions |
| Concrete colist compactness instance and order-equivalence corollaries | no assumptions beyond the generic theorem |
| Exact-stage generic-colist corollary | additionally, existing functional extensionality via the `μ ColistC ≅ list` round trip |

Strong LPO selects an exposed stage for a nonbottom supremum, while indefinite
description selects one compactness witness per position before the finite
enumeration merges them.  These introduce no new axiom to AlgCo.  The second
selection could likely be replaced by a more cumbersome list-indexed proof,
but doing so would not remove the classical assumptions already required by
shape projection and exposed-stage selection.

Milestone 2C below completes sequential density and the generic `aCPO`.  The
prototype continues to use countable directed sequences; the proposed
separation between standard DCPO semantics and this canonical sequential
presentation is documented in
[`algco2-design.md`](algco2-design.md#directed-completeness-and-the-computational-presentation).

## Milestone 2C checkpoint: sequential density and algebraicity

Status on July 26, 2026: **the complete generic sequential `aCPO` assembles**.

The new
[`theories/generic/algebraic_container.v`](../theories/generic/algebraic_container.v)
isolates the remaining algebraic structure from the fixed-point, order,
completeness, and compactness modules.  It adds:

- the canonical density theorem
  `supremum x (λ n, incl_mu (truncate_nu n x))`;
- pointwise transport of coinductive child suprema;
- continuity of every finite truncation `truncate_nu n`;
- the generic `Dense (ν C) (μ C)` presentation;
- the complete `aCPO (ν C) (μ C)` instance for a finitary pointed container.

The hypotheses separate more cleanly than expected:

| Construction or theorem | Required signature structure |
|---|---|
| Included truncations have supremum `x` | pointed container only |
| Canonical `Dense` data | pointed container only |
| Finite-truncation continuity | decidable pointed container |
| Directed completeness of `ν C` | decidable pointed container |
| Compactness of `μ C` | finitary pointed container |
| Complete generic `aCPO` | finitary pointed container, combining the preceding structures |

Density is a short coinductive argument.  An upper bound of all truncations
already bounds the first exposed layer; recursively, the bounds at depths
`n + 1` bound each child at depth `n`.

Continuity is the more informative result.  For a nonbottom supremum, one
exposed stage forces an arbitrary upper bound of the truncated stages to have
the correct outer shape.  Each child is then handled by the induction
hypothesis at the smaller depth.  No common stage for all children is needed,
because leastness is proved pointwise against a fixed upper bound.  Thus even
finite-truncation continuity does **not** require finite branching.  Position
enumeration remains confined to compactness.

### Colist specialization and typeclass behavior

[`theories/generic/colist_instance.v`](../theories/generic/colist_instance.v)
now registers one coherent concrete stack for the generic colist carrier:

```text
OType, PType, Compact, CPO, Dense, aCPO
```

Direct `typeclasses eauto` smoke tests find every structure for
`μ ColistC` and `ν ColistC`.  The dense inclusion and ideal also compute as
the existing native `inj` and `prefix`, witnessed by
`nu_to_colist_dense_incl_list` and `mu_to_list_dense_ideal_colist`.

This is a successful specialization workaround, not a solution to generic
descriptor inference.  The concrete module explicitly chooses the pointed
and finitary packages and aliases their orders.  Generic clients still cannot
expect Coq to reconstruct such a package from `μ (pc_container C)` alone.

### Milestone 2C assumption audit

| Result | Additional assumption |
|---|---|
| Canonical truncation density | `Eq_rect_eq.eq_rect_eq` |
| `Dense` data | none |
| Child-supremum transport, exposed-stage selection, and truncation continuity | existing `classic`, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` |
| Generic and concrete-container `aCPO` instances | the same three assumptions, inherited from completeness, compactness, and continuity |
| Colist inclusion/ideal computation corollaries | none |

No new axiom is introduced.  In particular, the density proof itself does not
use strong LPO or classical shape comparison; those enter finite-observation
continuity through exposed-stage selection and generic child projection.

The sequential algebraic vertical slice is now complete.  Milestone 2D below
generalizes compactness to arbitrary nonempty directed families, and Milestone
2E tests a descriptor-indexed carrier that makes generic instance resolution
deterministic.

## Milestone 2D checkpoint: Scott compactness of the included basis

Status on July 26, 2026: **the arbitrary-directed compactness argument
succeeds**.

The new
[`theories/generic/scott_container.v`](../theories/generic/scott_container.v)
keeps this experiment separate from the current sequential hierarchy.  It
defines standard compactness relative to any nonempty directed family whose
supremum is supplied relationally:

```text
scott_compact k :=
  ∀ (I : Type) (d : I → A),
    inhabited I → directed d →
    ∀ x, supremum x d → k ⊑ x →
    ∃ i, k ⊑ d i
```

This does not assume or construct a `DCPO A`.  It states what happens whenever
the particular directed family has a supremum.  The bridge theorem
`scott_compact_compact` shows that this implies AlgCo's existing
sequence-based `compact` predicate.

For every finitary pointed container, the main result is:

```text
incl_mu_scott_compact :
  ∀ b : μ C, scott_compact (incl_mu b : ν C)
```

This is the standard basis theorem: it is the image of a finite basis element
in the semantic domain that is compact.  It is stronger and more relevant to
algebraicity than the earlier statement that `μ C` is internally compact for
its own sequence-based order.

The proof follows the finite-tree structure of `b`:

1. The bottom basis element lies below any member; explicit inhabitance of
   the index type supplies that member.
2. If `incl_mu b ⊑ limit` and `b` exposes a constructor, then `limit` exposes
   the same constructor.
3. A nonbottom supremum has some family member exposing that constructor.  If
   no member exposed anything, semantic bottom would be an upper bound,
   contradicting leastness of the nonbottom supremum.
4. Projecting a child from every family member preserves directedness and
   transports the supplied supremum pointwise.  Structural induction therefore
   gives one witness index for each child of `b`.
5. The complete finite position enumeration and directedness merge those
   child indices into one member.  One final directedness step merges it with
   the constructor-exposing member.

This confirms the earlier hypothesis split:

| Construction or theorem | Required structure |
|---|---|
| Definition of `scott_compact` | an ordered carrier |
| Finite common upper member | an explicitly inhabited directed family |
| Child-family and exposed-member lemmas | decidable pointed container |
| Scott compactness of every included `μ C` element | finitary pointed container |

Finite branching is still used at exactly one semantic point: synchronizing
the finitely many child witnesses.  Countability of the directed family is not
used.  Coq accepts the index type in a universe independent of the carrier's
universe, so the definition is not accidentally restricted to small or
same-universe families.

The exposed-member proof is slightly cleaner than the construction of the
existing sequential supremum.  Because a supremum is already supplied and
only an existence result is needed, it applies excluded middle directly to
`∃ i, nu_exposes (d i)`; it does not invoke strong LPO or search a sequence.
This does **not** yet provide arbitrary directed suprema for `ν C`.  A full
universe-polymorphic `DCPO (ν C)` construction remains a separate experiment.

The concrete colist boundary exposes the results as
`colist_incl_scott_compact` and `incl_list_scott_compact`.  Thus an included
generic list is standardly compact in the generic colist semantic carrier,
while existing native list and colist APIs remain unchanged.

### Milestone 2D assumption audit

| Result | Additional assumption |
|---|---|
| `scott_compact`, its bridge to sequential compactness, and finite directed-family aggregation | none |
| Child-family supremum transport and exposed-member existence | existing `classic`, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` |
| `incl_mu_scott_compact` | the same three assumptions |
| Concrete colist corollaries | no assumptions beyond the generic theorem |

No axiom is new to AlgCo.  Constructive indefinite description selects one
witness index for each recursive position before finite aggregation; the
classical and dependent-equality assumptions are inherited from generic child
projection and shape transport.

## Milestone 2E checkpoint: descriptor-indexed carriers

Status on July 26, 2026: **the wrapper resolves the generic instance stack
without concrete reassembly**.

The new
[`theories/generic/indexed_container.v`](../theories/generic/indexed_container.v)
defines genuine one-field wrappers:

```text
Basis S = wrapper around μ (pc_container S)
Value S = wrapper around ν (pc_container S)
```

They are records, not transparent aliases, so the pointed descriptor `S`
remains visible at the type head.  The pointed descriptor determines the
container, semantic bottom, and approximation order.  Capabilities needed only
by later constructions are separate classes keyed by `S`:

```text
DecidableBottom S
FinitePositions S
```

Adapters reconstruct the existing `decidable_pointed_container` and
`finitary_pointed_container` packages.  This lets the experiment reuse all of
the raw fixed-point theorems without changing their APIs.

The generic wrapper module supplies the complete stack once:

| Structure or theorem | Required descriptor capability |
|---|---|
| `OType` and `PType` for `Basis S` and `Value S` | pointed descriptor only |
| canonical `Dense (Value S) (Basis S)` data | pointed descriptor only |
| `CPO (Value S)` | `DecidableBottom S` |
| `Compact (Basis S)` | `DecidableBottom S` and `FinitePositions S` |
| `aCPO (Value S) (Basis S)` | both capabilities |
| Scott compactness of `incl b` | both capabilities |

The one-time `aCPO` proof transports the same five laws as the raw generic
instance.  That transport is now paid once for all descriptors rather than
repeated by every concrete datatype.

The companion
[`theories/generic/indexed_colist_instance.v`](../theories/generic/indexed_colist_instance.v)
registers only:

```text
DecidableBottom (ColistS A)
FinitePositions (ColistS A)
```

It declares no colist-specific wrapper `OType`, `Compact`, `CPO`, `Dense`, or
`aCPO`.  Nevertheless, ordinary `typeclasses eauto` resolves the entire stack.
Printing the durable smoke-test proof shows that Coq selected exactly:

```text
aCPO_indexed_container
  (colist_pointed_container A)
  (DecidableBottom_colist A)
  (FinitePositions_colist A)
```

Thus the descriptor no longer has to be reconstructed from a projected raw
carrier, and the particular compactness, density, and completeness instance
terms agree automatically.

### Initial proof-ergonomics result

The basic native boundary remains shallow.  One-time conversions connect
`Basis ColistS` with `list` and `Value ColistS` with `colist`.  The high-level
operations using ordinary `incl` and `ideal` satisfy native statements:

```text
indexed_value_to_colist (incl (list_to_indexed_basis l)) = inj l
indexed_basis_to_list (ideal (colist_to_indexed_value l) n) = prefix n l
scott_compact (incl (list_to_indexed_basis l))
```

No coercions were introduced, so this experiment exposes the actual wrapper
cost.  Directedness transports definitionally because it quantifies only over
members of the supplied family.  Suprema need two small generic transport
lemmas: their leastness clause quantifies over every possible upper bound, so
the raw and wrapped carrier types are not definitionally interchangeable.
Native conversion definitions also use the wrapper constructor or projection
once.  These costs remain behind the specialization boundary in the current
smoke tests.

Two qualifications remain important:

- capability classes contain computational deciders and enumerations; a
  descriptor should have one coherent registered instance of each, or those
  choices should be explicit;
- the current stable index is a `pointed_container`, which still contains its
  nullary-bottom proof.  A final design may separate signature data from this
  law more aggressively.

The wrapper therefore solves the tested typeclass-resolution problem, but at
the end of this checkpoint it did not by itself decide between containers and
a functor-code language or establish operation-level proof ergonomics.
Milestone 2F below records the decisive native `comap` test.

### Milestone 2E assumption audit

| Result | Additional assumption |
|---|---|
| Wrappers, capabilities, adapters, orders, pointed structures, and `Dense` data | none |
| Native conversion and inclusion/ideal computation lemmas | none |
| Generic wrapper `Compact`, `CPO`, and `aCPO` instances | existing `classic`, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` inherited from the raw theorems |
| Wrapper Scott-compactness theorem | the same three assumptions |

No new axiom or universe constraint appears at the wrapper boundary.

## Milestone 2F checkpoint: native `comap` through the indexed presentation

Status on July 26, 2026: **the colist operation slice succeeds, including the
proof-ergonomics criterion**.

The new
[`theories/generic/indexed_colist_comap.v`](../theories/generic/indexed_colist_comap.v)
defines the native-list basis computation and extends it through the generic
indexed `aCPO`:

```text
indexed_amap f b       = amap f (indexed_basis_to_list b)
indexed_comap_value f  = co (indexed_amap f)
indexed_comap f l      = indexed_comap_value f (colist_to_indexed_value l)
```

The operation accepts and returns native colists.  Its public results likewise
mention only native constructors and operations:

```text
continuous (indexed_comap f)
indexed_comap f conil = conil
indexed_comap f (cocons a l) = cocons (f a) (indexed_comap f l)
indexed_comap f (inj xs) = inj (List.map f xs)
```

The old `comap` is not used to prove any of these facts.  Only after the direct
constructor equations are established does a coinductive regression theorem
prove `indexed_comap f l = comap f l`.

### Reusable `cofold` boundary

Proving the `cocons` equation directly first exposed the same shifted-supremum
argument that the existing `co_fold_cons` theorem hides.  Leaving that proof
inside every operation would fail the ergonomics criterion.  The prototype
therefore factors it into a one-time specialization API:

```text
indexed_fold
indexed_co_fold
indexed_cofold
indexed_co_fold_nil'
indexed_co_fold_cons'
indexed_cofold_nil'
indexed_cofold_cons'
```

`indexed_co_fold_cons'` drops the bottom approximation, transports the native
prefix computation across the wrapper, and applies continuity to the tail
supremum.  Once this is available, the `comap` constructor proof is again just
an application of the `cofold` rule plus continuity of `cocons`, matching the
shape of the current AlgCo proof.  The wrapper conversion and dependent
container representation do not appear in the operation statement or its
routine proof.

There is one concrete implementation wrinkle.  The generic `co` definition
uses the alias `basis A`, so the shifted-supremum proof must explicitly
`unfold basis` before native ideal-computation lemmas rewrite.  This is local
to the reusable specialization theorem, but it is evidence that AlgCo 2 should
make the approximation presentation an explicit stable parameter instead of
recovering it through an opaque typeclass-indexed alias.

The native-to-indexed conversion is proved monotone and continuous once in
`indexed_colist_instance.v`.  The proof deliberately uses the coinductive
native/generic equivalence as an order equivalence rather than converting it
to Coq equality.  Consequently, neither bridge theorem needs `colist_ext`.
Native continuity is then a short composition of that bridge with generic
continuity of `co`.

### Proof and assumption comparison

| Result | Comparison with existing `comap` |
|---|---|
| Basis-map monotonicity | one native monotonicity application plus the one-time basis conversion lemma |
| Continuity | composition through the native/indexed bridge; no visible transport in the statement |
| `conil` and `cocons` equations | same operation-level proof pattern after the reusable indexed `cofold` lemmas |
| Finite-list equation | ordinary induction using the two native constructor equations |
| Extensional equality | proved coinductively only as a final regression check |

The assumption audit is:

| Result | Assumptions |
|---|---|
| Native/indexed monotonicity and continuity bridges | `Eq_rect_eq.eq_rect_eq` inherited from the generic wrapper order |
| Indexed basis-map monotonicity | the same dependent-equality assumption |
| Indexed and native `comap` continuity | functional extensionality, classical logic, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` inherited from the generic `aCPO` |
| Native constructor, basis-inclusion, finite-list, and regression equalities | the preceding assumptions plus the existing `colist_ext` axiom |

The old `continuous_comap` has the same functional-extensionality, classical,
and indefinite-description assumptions but not `Eq_rect_eq.eq_rect_eq`; its
constructor equations already use `colist_ext`.  Thus the indexed route adds
only the dependent-equality assumption already identified in the generic
container order.  It introduces no new axiom.

This is enough to accept descriptor-indexed wrappers as viable for the colist
slice.  Milestone 2G below tests the corresponding branching boundary.

## Milestone 2G checkpoint: branching Boolean cotrees

Status on July 26, 2026: **the branching representation and operation slice
also succeeds**.

Three new modules implement the slice:

- [`theories/generic/cotree_instance.v`](../theories/generic/cotree_instance.v)
  defines the raw pointed container and native fixed-point conversions;
- [`theories/generic/indexed_cotree_instance.v`](../theories/generic/indexed_cotree_instance.v)
  registers the two descriptor capabilities and exposes the native boundary;
- [`theories/generic/indexed_cotree_map.v`](../theories/generic/indexed_cotree_map.v)
  derives indexed `tfold`/`tcofold` rules and reconstructs native `cotree_map`.

The Boolean-cotree signature is:

```text
shape = bottom | leaf A | node
position bottom   = Empty
position (leaf a) = Empty
position node     = bool
```

Its initial and final fixed points convert to `atree bool A` and
`cotree bool A`.  Both round trips are proved, with the coinductive ones first
stated as structural bisimulations.  Generic approximation is exactly native
`atree_le`/`cotree_le`; generic inclusion computes as `tinj`; and generic
truncation computes as `tprefix`.

### Indexed specialization and instance reuse

The concrete indexed module registers only:

```text
DecidableBottom (cotree_pointed_container A)
FinitePositions (cotree_pointed_container A)
```

It declares no cotree-specific wrapper `OType`, `Compact`, `CPO`, `Dense`, or
`aCPO`.  The durable smoke test elaborates directly to:

```text
aCPO_indexed_container
  (cotree_pointed_container A)
  (DecidableBottom_cotree A)
  (FinitePositions_cotree A)
```

The public boundary remains native:

```text
indexed_value_to_cotree (incl (atree_to_indexed_basis t)) = tinj t
indexed_basis_to_atree (ideal (cotree_to_indexed_value t) n) = tprefix n t
scott_compact (incl (atree_to_indexed_basis t))
```

Thus the wrapper result from Milestone 2E is not colist-specific.

### Branching `tcofold` and `cotree_map`

The reusable specialization API contains:

```text
indexed_tfold
indexed_co_tfold
indexed_tcofold
indexed_co_tfold_bot' / leaf' / node'
indexed_tcofold_bot' / leaf' / node'
```

The node theorem is the decisive case.  Each Boolean child supplies its own
indexed ideal chain.  `supremum_apply` assembles their suprema into a
pointwise function-space supremum, and `wcontinuous` transports that supremum
through the node algebra.  The shifted parent truncation is identified with
one node layer over the child truncations.  All wrapper and supremum reasoning
is confined to this reusable theorem.

The reconstructed map has native statements:

```text
continuous (indexed_cotree_map f)
indexed_cotree_map f cobot = cobot
indexed_cotree_map f (coleaf a) = coleaf (f a)
indexed_cotree_map f (conode k) = conode (indexed_cotree_map f ∘ k)
indexed_cotree_map f (tinj t) = tinj (atree_map f t)
```

The operation-level node proof applies `indexed_tcofold_node'` and discharges
only `wcontinuous conode` using the existing continuity theorem.  It contains
no container shape, position, wrapper conversion, or dependent transport.
The old `cotree_map` is used only afterward as a coinductive regression oracle.

Two internal elaboration details are worth retaining as design evidence:

- under the nested child function, simplification exposed the generic
  `value_ideal` projection before the native ideal rewrite could fire; the
  reusable node proof therefore unfolds the wrapper projections once and uses
  the raw truncation theorem pointwise;
- Coq initially inferred the node algebra as an implicit argument of the
  computation theorem.  An explicit `Arguments` declaration makes `leaf`,
  `node`, and `children` visible at call sites and restores predictable
  operation proofs.

These are specialization-API issues, not transports in client theorems.  They
support providing deliberate simplification and argument declarations rather
than relying on automatic unfolding.

### Milestone 2G assumption audit

| Result | Assumptions |
|---|---|
| Shape, position, capabilities, raw conversions, and coinductive round trips as bisimulations | none |
| Initial-algebra round trips as Coq equalities | functional extensionality, because node and even nullary child functions must be equated |
| Native/indexed order and continuity bridges | `Eq_rect_eq.eq_rect_eq` inherited from the generic wrapper order; no `cotree_ext` |
| Indexed `tfold` node rule and native map continuity | functional extensionality, classical logic, constructive indefinite description, and `Eq_rect_eq.eq_rect_eq` inherited from the generic `aCPO` |
| Native map constructor, finite-tree, and regression equalities | the preceding assumptions plus the existing `cotree_ext` axiom |

The existing native `cotree_map` equations have the same assumptions except
for `Eq_rect_eq.eq_rect_eq`.  As in the colist experiment, dependent equality
is the only additional axiom and is inherited from the current generic
container order; the branching construction introduces no new axiom.

The two operation slices now establish that enriched containers are a viable
semantic backend for both linear and finitely branching types.  They do not
show that handwritten specialization is economical: the raw conversion and
order proofs remain substantial and structurally repetitive.  A functor-code
language is therefore most plausible as a derivation frontend over this
container semantics, not as a replacement motivated by failed proof
ergonomics.

## Milestone 2H checkpoint: specialization audit and frontend boundary

Status on July 26, 2026: **the audit is complete and a minimal implementation
experiment is specified**.

This checkpoint compares the complete colist and Boolean-cotree slices before
introducing another representation.  The six specialization modules contain
1,817 lines in total:

| Layer | Colist | Boolean cotree |
|---|---:|---:|
| Raw descriptor, conversions, and order correspondence | 493 | 393 |
| Descriptor-indexed native boundary | 161 | 168 |
| Fold/cofold rules and reconstructed map | 267 | 335 |

The colist raw module also contains an older concrete `OType`/`CPO`/`aCPO`
instance stack that the cotree slice deliberately does not repeat.  It should
not be counted as a requirement for a future specialization.  Conversely, the
larger cotree operation module contains the genuinely new function-space
argument for a branching node.  Raw line counts therefore overstate exact
duplication, but they identify the two large repeated seams: native
presentation plumbing and fold/cofold infrastructure.

### Field-by-field classification

| Material in the two slices | Classification | Intended home |
|---|---|---|
| Shape and position definitions | Derivable from a small strictly-positive code | Frontend interpretation into `container` |
| Distinguished nullary bottom, its decision procedure, and finite position enumeration | Derivable when pointedness and finite recursive families are represented by the code | Frontend capabilities |
| `μ`/native-basis conversions and their inverse proofs | Inherently tied to the chosen native datatype unless that datatype is generated too | Native presentation obligation |
| `ν`/native-value conversions and bisimulation round trips | Inherently tied to the native coinductive constructors and equality | Native presentation obligation |
| Generic/native order correspondence | Structurally regular, but its proof analyzes the native order constructors | Native presentation obligation, packaged once |
| Inclusion and truncation as `inj`/`prefix` or `tinj`/`tprefix` | Type-specific commuting laws with a common statement schema | Native presentation obligation |
| Indexed aliases and `DecidableBottom`/`FinitePositions` registrations | Entirely derivable | Frontend |
| Wrapper conversions and basis-conversion monotonicity | Derivable from a packaged order isomorphism | Generic native-presentation layer |
| Native-to-indexed monotonicity and continuity | The two proofs are the same order-isomorphism argument | Generic native-presentation layer |
| Indexed inclusion, ideal, and Scott-compactness corollaries | Derivable from the presentation laws and existing container theorems | Generic native-presentation layer |
| Structural basis fold and continuous extension | Container-generic; code generation would duplicate a theorem | Generic container backend |
| Shifted-supremum constructor proof | Container-generic once each algebra branch is weakly continuous | Generic container backend |
| Named native constructor equations and useful `Arguments` declarations | A thin, type-specific public facade; Gallina data cannot emit commands or theorem names | Native specialization module |
| `amap`, `atree_cotree_map`, algebra continuity, finite-input results, and regression against old operations | Operation-specific | Client/program module |

The most important correction to the earlier plan is that a frontend should
not generate a colist fold theorem and a cotree fold theorem independently.
The shifted-supremum argument in both modules has the same source: depth
`S n` exposes one container layer over the depth-`n` child approximants.  It
belongs in one theorem over `Basis S` and `Value S`.  Branching changes only
the continuity obligation for the algebra at a shape; `supremum_apply` already
handles its pointwise child family.

The other important boundary is negative.  A signature code cannot derive an
isomorphism to an independently declared native `list`, `colist`, `atree`, or
`cotree` merely by computation.  Claiming otherwise would either hide the
same proofs in automation or require the frontend to generate the native
datatypes themselves.  The first prototype should package and reuse these
proofs, not pretend to eliminate them.

### Minimal code language

The smallest compositional grammar needed by the two completed slices is:

```text
D ::= K A                 constant payload
    | Rᶠ I                an I-indexed finite family of recursive occurrences
    | D + D               choice of constructor form
    | D × D               paired fields

P D ::= 1 + D             canonical pointed signature
```

Its ordinary functor interpretation is:

```text
⟦K A⟧ X     = A
⟦Rᶠ I⟧ X    = I → X
⟦D + E⟧ X   = ⟦D⟧ X + ⟦E⟧ X
⟦D × E⟧ X   = ⟦D⟧ X × ⟦E⟧ X
⟦P D⟧ X     = 1 + ⟦D⟧ X
```

The frontend compiles this interpretation to the already-tested `container`
representation; it does not introduce a second fixed-point semantics.  The
left `1` of `P D` is the distinguished semantic bottom.  Its position type is
empty, and the outer sum gives a canonical bottom-shape decision.  Position
enumeration is derived structurally.  `Rᶠ I` therefore carries an explicit
finite enumeration of `I`; arbitrary constant payloads need no finiteness
assumption because they contribute no recursive positions.  Write `R` for
`Rᶠ unit`.

The two existing signatures become:

```text
ColistCode A = P (K A × R)
CotreeCode A = P (K A + Rᶠ bool)
```

`K unit` can serve as a nonbottom nullary constructor, so no additional
constructor is needed for the present experiment.

A general field-former `Πᶠ i : I. D i` is deliberately absent.  Its standard
container compilation uses a function of component shapes.  Even the special
case `Π b : bool. R` then has shapes of type `bool → unit`, introducing
functional extensionality and multiple intensional representatives for what
should be the single cotree-node shape.  The primitive `Rᶠ I` compiles
canonically to one shape with position type `I`.  General dependent fields can
be reconsidered only when a datatype requires them.  Empty signatures, nested
types, ordered payloads, and negative occurrences are likewise outside the
first grammar.

The code must have an explicit interpretation.  It is a frontend for defining
one canonical pointed container and its computational capabilities, not an
alternative axiomatization of `μ`, `ν`, approximation, or algebraicity.

### Native presentation package

The frontend alone stops at generic fixed points.  A separate presentation
record should connect them to the public native types.  In schematic form it
contains:

```text
NativePresentation D:
  NativeBasis, NativeValue

  basis_to_generic : NativeBasis → Basis ⟦P D⟧
  basis_to_native  : Basis ⟦P D⟧ → NativeBasis
  value_to_generic : NativeValue → Value ⟦P D⟧
  value_to_native  : Value ⟦P D⟧ → NativeValue

  basis round trips
  value round trips, initially up to the native equivalence
  basis-order correspondence
  value-order correspondence
  inclusion commuting law
  truncation commuting law
```

This package should state order and coinductive laws using equivalence where
possible.  Conversion to Coq equality remains a specialization corollary and
may use the existing native extensionality axiom.  Generic lemmas can then
derive the indexed conversion wrappers, monotonicity, continuity, ideal
equation, inclusion equation, and compactness result.  The duplicated
continuity proofs in `indexed_colist_instance.v` and
`indexed_cotree_instance.v` should disappear.

The package is a proof boundary, not a new global instance stack.  Its
descriptor remains explicit, and the generic kernel should not ask typeclass
search to reconstruct a proof-rich presentation from a projected carrier.

### Generic fold/cofold target

Before implementing syntax, factor the operation-independent core into a
generic container theorem.  For a pointed algebra

```text
α : ∀ s, (position s → B) → B
```

define structural recursion on `Basis S` and extend it continuously to
`Value S`.  Under a pointed result type, a bottom equation for the designated
shape, and weak continuity of every `α s`, the target computation rule is:

```text
cofold α (in_value s children)
  === α s (fun p => cofold α (children p))
```

The exact general theorem may retain the more permissive base-value premises
used by `indexed_co_fold`; the first frontend only needs the pointed
specialization.  One theorem must instantiate to all of:

```text
cofold step conil
cofold step (cocons a l)
tcofold leaf node cobot
tcofold leaf node (coleaf a)
tcofold leaf node (conode children)
```

This is the highest-value and highest-risk part of the next implementation
slice.  If the apparent common theorem requires type-specific truncation
reasoning after all, a code frontend would hide duplication rather than remove
it.

### What the first frontend should and should not produce

It should produce, by transparent definitions and ordinary lemmas:

- the interpreted `container` and `pointed_container`;
- canonical `DecidableBottom` and `FinitePositions` capabilities;
- descriptor-indexed `Basis` and `Value` aliases;
- the generic fold/cofold interface and its shape-indexed computation theorem;
- generic consequences of a supplied `NativePresentation`;
- predictable simplification lemmas for wrapper projections.

It should not attempt to produce:

- native inductive or coinductive declarations;
- native conversion functions or their round-trip proofs;
- native order-correspondence proofs;
- native extensionality principles;
- operation algebras or their continuity proofs;
- theorem names, hint registrations, or `Arguments` commands through heavy
  metaprogramming.

The last group should remain a short handwritten facade in the first version.
If those declarations are still numerous after the semantic duplication is
removed, lightweight generation can be evaluated separately.  MetaCoq, Elpi,
or a custom plugin is not justified by the present evidence.

### Implementation experiment and acceptance gate

The next slice should proceed in this order:

1. Add a generic structural fold and prove its continuous-extension layer
   equation over the existing indexed container backend.
2. Add the minimal constant/finite-recursion/sum/product grammar and transparent
   compilation to containers, deriving pointedness and finite-position
   capabilities.
3. Add the native-presentation package and derive its wrapper-level order and
   continuity consequences.
4. Define parallel coded colist and cotree descriptors without deleting the
   current modules.
5. Recover the existing native `comap` and `cotree_map` constructor proofs
   through the common fold theorem.
6. Compare declarations, proof terms, build assumptions, error messages, and
   extraction boundaries against Milestones 2F and 2G.

The experiment succeeds only if:

- the shifted-supremum proof occurs once;
- descriptor capability registrations are no longer handwritten per type;
- the native-to-indexed continuity bridge occurs once;
- public operation equations retain their current native statements and short
  continuity-only proofs;
- no new axiom appears in the assumption audit; and
- the remaining handwritten presentation laws are visibly about the native
  datatype rather than wrapper bookkeeping.

This gate measures reduction of real duplication, not merely movement of the
same proof scripts behind tactics.  Operational lifting remains the following
milestone once this representation decision is settled.

## Milestone 2I checkpoint: generic fold/cofold layer equation

Status on July 26, 2026: **the generic layer theorem succeeds for both
completed operation slices**.

[`theories/generic/indexed_fold.v`](../theories/generic/indexed_fold.v) now
defines:

```text
indexed_algebra S B =
  ∀ s, (position s → B) → B

basis_fold : indexed_algebra S B → Basis S → B
value_fold : indexed_algebra S B → Value S → B
```

`basis_fold` is ordinary structural recursion over the container initial
algebra.  `value_fold` is its AlgCo continuous extension through the existing
descriptor-indexed `aCPO`.  The generic monotonicity theorem exposes the same
three obligations as the previous native folds:

```text
the bottom-shape algebra returns z
z lies below every finite fold result
every shape algebra is monotone in its children
```

If every shape algebra is weakly continuous, the principal theorem is:

```text
value_fold α (in_value s children)
  === α s (fun p => value_fold α (children p))
```

Its proof contains the single remaining `shift_supremum''` in the indexed
fold path.  It forms the pointwise supremum of all child fold chains with
`supremum_apply`, transports that supremum through `α s`, and identifies the
shifted parent truncations with one layer over the child truncations.  This
argument is independent of whether the position type is `unit`, `bool`, or
another supported family.

### Finiteness/API coupling

The current Gallina type of `value_fold` and all three value-fold equations
requires `FinitePositions S`.  This is presently an **API dependency**, not a
premise used by the layer argument itself.  `value_fold` is defined through
the existing generic `co`, whose source must be a full `aCPO (Value S)`; the
construction of that `aCPO` uses `FinitePositions S` to prove compactness of
the proposed basis.  Consequently Coq requests the capability before the
layer theorem begins.

After `value_fold` has been obtained, however, `value_fold_layer` never
enumerates positions or combines finitely many child witnesses.  It uses the
canonical truncation chains and their one-step layer equation, pointwise child
suprema, and weak continuity of the algebra branch.  It does not invoke basis
compactness or even the reconstruction/density field of `aCPO`.  The shifted-
supremum proof is therefore position-family agnostic.  In particular, the
present statement should not be read as evidence that finite branching is a
mathematical requirement of the fold equation.

This suggests factoring a weaker sequential-extension interface from the
full algebraic-CPO interface.  Such an interface would expose the canonical
approximation chain and layer-shift law needed by `value_fold_layer`, and
would normally retain reconstruction as the law that makes the sequence a
genuine presentation of each value, without also requiring every approximant
to be compact.  An infinite-branching test case should then determine whether
the generic layer theorem can be restated with that weaker structure.  This
refactoring is not a prerequisite for the direct-combinator experiment: its
recursive-family primitive is deliberately finitary, so that experiment can
proceed while keeping this coupling visible as a later generalization
boundary.

### Three computation rules, one recursive argument

The generic module exposes three rules rather than forcing every constructor
through the strongest theorem:

- `value_fold_bottom` proves the designated-bottom equation without any
  assumptions about other shapes;
- `value_fold_nullary` proves an eventually constant nonbottom nullary layer
  from only its local base inequality and monotonicity;
- `value_fold_layer` contains the one general shifted-supremum proof for
  recursive layers.

The weakened nullary rule matters for proof ergonomics.  Deriving a leaf from
the general theorem would unnecessarily demand weak continuity of the node
algebra and a global lower-bound theorem for every finite tree.  The separate
rule keeps the native cotree leaf theorem's original single premise
`z ⊑ leaf a` while still centralizing all eventually-constant reasoning.

### Colist and cotree specializations

The colist specialization defines the algebra:

```text
hole       ↦ z
cons a     ↦ fun children => step a (children tt)
```

and the cotree specialization defines:

```text
bottom     ↦ z
leaf a     ↦ leaf a
node       ↦ node
```

Both generic basis folds have native computation bridges:

```text
indexed_fold z step b
  = fold z step (indexed_basis_to_list b)

indexed_tfold z leaf node b
  = tfold z leaf node (indexed_basis_to_atree b)
```

The native-to-indexed conversions now also expose deliberate constructor
equations.  Because the descriptor cannot be inferred from a projected shape,
these equations must spell out `in_value`'s descriptor internally; this is the
same elaboration limitation identified in Milestone 2E and remains hidden from
client theorems.

`indexed_comap_value` and `indexed_cotree_map_value` are now instances of the
generic `value_fold`, not independent calls to `co` over native folds.  Their
public continuity, constructor, finite-input, and regression theorems retain
the same native statements.  In particular, the operation proofs still
discharge only constructor continuity:

```text
indexed_comap f (cocons a l)
  = cocons (f a) (indexed_comap f l)

indexed_cotree_map f (conode children)
  = conode (indexed_cotree_map f ∘ children)
```

The old `comap` and `cotree_map` remain final regression oracles.

### Small surprises

- The explicit premises `z ⊑ step a z` and
  `z ⊑ node (fun _ => z)` in the old recursive-layer APIs are consequences of
  the stronger premise that `z` lies below every finite fold.  They are
  retained for source-level comparison, but the generic proof does not use
  them.
- A separate nullary theorem is useful even though nullary shapes are covered
  mathematically by the general theorem: it prevents irrelevant global
  obligations from leaking into leaf proofs.
- The colist native-fold bridge is constructive.  The Boolean-cotree bridge
  uses functional extensionality to equate its function-valued child results,
  as expected from the native `anode` representation.
- `FinitePositions S` occurs in the generic equations because `value_fold`
  currently enters through the full `aCPO` API.  The recursive layer proof
  itself performs no finite enumeration; this is an interface-generalization
  opportunity rather than evidence that the equation needs finite branching.
- The first factoring step increases total prototype lines because it keeps
  both native regression helpers and the new generic API.  Its measured payoff
  is proof uniqueness: the shifted-supremum argument now occurs once.  The
  frontend and native-presentation experiments must still demonstrate a net
  reduction in specialization plumbing.

### Milestone 2I assumption audit

| Result | Assumptions |
|---|---|
| Raw `basis_fold` and its constructor equation | none |
| Generic `value_fold_bottom`, `value_fold_nullary`, and `value_fold_layer` | `FinitePositions S` at the current API boundary, plus `Eq_rect_eq.eq_rect_eq`, classical logic, and constructive indefinite description inherited from the indexed `aCPO` and selected supremum; the proofs do not enumerate positions |
| Specialized colist recursive fold equation | the same generic assumptions; no functional extensionality |
| Specialized cotree recursive fold equation | the generic assumptions plus functional extensionality for the native `tfold` bridge |
| Native `comap` and `cotree_map` equalities | the preceding assumptions plus the existing respective native extensionality axiom |

No new axiom is introduced by the generic layer theorem.  A full `make -B`
and `coqchk` over the new module and both specializations pass.  Searching the
three operation modules confirms that `shift_supremum''` occurs only in
`indexed_fold.v`.

### Checkpoint decision

The highest-risk semantic part of the frontend experiment has passed.  At
this checkpoint the proposed next step was a minimal `K`/`Rᶠ`/sum/product
syntax.  Milestone 2J tests the strictly smaller alternative first: semantic
container combinators carrying their finiteness evidence directly.

## Milestone 2J checkpoint: semantic container combinators

Status on July 26, 2026: **direct combinators derive the required structural
facts; a reified code frontend is not presently justified**.

The experiment is split into three modules:

- [`theories/generic/container_combinators.v`](../theories/generic/container_combinators.v)
  defines the pure semantic constructors and carries finite-position evidence;
- [`theories/generic/indexed_container_combinators.v`](../theories/generic/indexed_container_combinators.v)
  bridges that evidence to `DecidableBottom` and `FinitePositions`; and
- [`theories/generic/container_combinator_examples.v`](../theories/generic/container_combinator_examples.v)
  assembles parallel colist and Boolean-cotree descriptors and exercises the
  generic fold rules.

### Semantic interface

`finite_index` packages an index type, an enumeration, and its completeness
proof.  `finitary_container` packages an ordinary `container` with a complete
enumeration of each shape's recursive positions.  The constructors immediately
return this semantic bundle:

```text
finitary_constant A
finitary_recursive I
finitary_sum C D
finitary_product C D
```

There is no signature AST and no interpretation function.  Constants may have
arbitrary shape types because they contribute no recursive positions.
Products enumerate the coproduct of their components' position types, while
sums select the positions of the chosen shape.

`finitary_point C` adds the outer nullary bottom shape.  Its bottom test is
derived by case analysis on the outer sum, and its position enumeration is
empty at bottom and inherited from `C` otherwise.  The pure module can package
the result as the existing `finitary_pointed_container`; the separate indexed
bridge registers:

```text
DecidableBottom (finitary_point C)
FinitePositions (finitary_point C)
```

The important elaboration detail is that `C` remains in the descriptor head.
Typeclass resolution receives the evidence-bearing bundle directly; it is not
asked to reconstruct a finitary descriptor from a projected carrier, which is
the inference problem encountered in Milestone 2E.

### Two composed signatures

The examples use the semantic equations formerly proposed as codes:

```text
ComposedColist A = point (constant A × recursive unit)
ComposedCotree A = point (constant A + recursive bool)
```

For both descriptors, declarations of `value_fold` elaborate without naming
either capability instance.  Complete basis-fold equations and value-fold
bottom/cons and bottom/leaf/node equations also compile through the generic
rules.

The proof ergonomics are acceptable but expose the ordinary container
encoding in two small places:

- a product's positions form a coproduct, so the colist tail position is
  `inr tt` rather than `tt`; a named `composed_colist_tail_position` hides it;
- applications of the generic value-fold rules still spell out the descriptor
  because Coq cannot infer it from a projected shape.  This is the same local
  specialization-boundary annotation required by the handwritten descriptors.

The cotree node position reduces definitionally to `bool`, so its branching
algebra retains the desired `(bool → B) → B` type.  Named bottom, cons, leaf,
and node shapes prevent nested sums and products from entering theorem
statements.

### What an explicit code would add

This checkpoint corrects the earlier motivation for codes.  An arbitrary
plain `container` does not determine a bottom shape or finite enumerations, but
a container assembled through evidence-preserving combinators does provide
those facts by construction.  A reified code would not improve that result.

The distinctive extra feature of a code is induction over the way a signature
was assembled.  That is useful only if a later generic transformation must
distinguish constants, choices, products, and recursive fields rather than
operate on the resulting shapes, positions, pointedness, and enumeration.
Operational lifting is the remaining plausible test.  Until it demonstrates
that need, adding an AST and interpretation layer would create a second
description without eliminating any established obligation.

### Milestone 2J assumption audit

| Result | Assumptions |
|---|---|
| Container constructors, finite enumerations, pointing, and capability bridge | none |
| Composed colist/cotree basis-fold equations | none |
| Composed colist/cotree value-fold equations | `Eq_rect_eq.eq_rect_eq`, classical logic, and constructive indefinite description inherited from the existing indexed `aCPO` and selected supremum |

No functional extensionality is needed by the composed Boolean-node equation;
it enters the old specialization only when relating the generic fold to native
`tfold`.  A full `make -B` and `coqchk` over the new modules pass, and no new
axiom appears.

### Checkpoint decision

Do not implement the pointed-polynomial code AST now.  Retain the direct
semantic combinators and proceed to the `NativePresentation` experiment,
which tests the larger remaining source of specialization plumbing.  When the
operational lifting begins, first attempt it over pointed containers and their
capabilities.  Introduce reified codes only if that construction genuinely
requires structural recursion over signature syntax.

## Motivation

AlgCo already follows the initial-algebra/final-coalgebra pattern
mathematically. For example,
[`theories/cotree.v`](../theories/cotree.v#L37) explicitly defines the
open-recursive `cotreeF`, describes `atree` as its least fixed point and compact
basis, and defines `cotree` coinductively as the corresponding greatest fixed
point. The same relationship appears concretely in other modules:

| Open signature | Finite basis | Coinductive values |
|---|---|---|
| `1 + X` | `nat` | `conat` |
| `1 + A × X` | `list A` | `colist A` |
| `1 + A + (I → X)` | `atree I A` | `cotree I A` |
| trie node signature | `trie A B` | `cotrie A B` |

The implementation repeats the fixed-point types, approximation orders,
inclusions, truncations, compactness arguments, and `aCPO` instances for each
case. Afterward, [`aCPO`](../theories/aCPO.v#L52) abstracts over the value and
basis types but no longer records the signature or its recursive positions.

For ordinary denotational reasoning, forgetting the signature is often an
advantage. For type-directed operational reasoning, it is a limitation. An
outer `option A` can add divergence to an atomic result, but an `aCPO A B`
instance alone does not say where computations must be inserted inside a
recursive value.

The distinction is visible in the two kinds of bottom discovered in the
`cofold` investigation:

```text
pending                 the target computation has not returned
returned semantic ⊥     the target returned AlgCo's least semantic value
```

For a colist result these should be different constructors. A computation may
be pending before exposing its outer layer, or it may return `conil`, which is
an ordinary target constructor denoting the semantic bottom.

## Goals

The prototype should determine whether a single finitary signature can support
all of the following.

1. Generic least and greatest fixed-point types.
2. A generic finite-approximation order.
3. Inclusion of the least fixed point into the greatest.
4. Canonical depth truncations and their supremum theorem.
5. Compactness and an `aCPO` instance for finite branching.
6. A computation lifting that adds a distinct operational `pending` layer.
7. An operational approximation order and realization relation.
8. Observation-indexed totality and coverage for the lifted type.
9. Demand-aware operational models of extracted folds.
10. An ergonomic connection to native Coq datatypes and extraction.

The initial target is one complete colist slice, followed by enough of cotrees
to show that the construction is genuinely generic rather than a disguised
list library.

## Non-goals of the prototype

The first prototype should not attempt to:

- replace or reorganize the existing AlgCo modules;
- present every CPO as a recursive container;
- handle arbitrary nested, indexed, or negative recursive types;
- verify Coq's complete extraction pipeline or Haskell runtime;
- eliminate all existing extensionality or classical axioms;
- port sieve, tries, real-number domains, or probabilistic semantics;
- decide strictness and payload evaluation uniformly for every target language.

The prototype should remain small enough that abandoning it is inexpensive.

## Mathematical design

### Containers

Start with a conventional container presentation:

```text
Container C:
  Shape C : Type
  Pos C   : Shape C → Type

⟦C⟧ X = Σ s : Shape C, Pos C s → X
```

In Coq, the fixed points should be declared directly in terms of shapes and
positions so that recursive occurrences remain visibly strictly positive:

```text
μ C  = inμ  (s : Shape C) (Pos C s → μ C)
ν C  = inν  (s : Shape C) (Pos C s → ν C)
```

The first version may use a pair of parameters `Shape` and `Pos` instead of a
record if that improves Coq's positivity checking or generated eliminators.

### Pointed signatures

AlgCo's coinductive domains contain an explicit approximation hole. For
example, the relevant stream-like signature is not the total stream functor

```text
StreamF X = A × X
```

whose initial algebra is empty. It is the pointed signature

```text
ColistF X = 1 + A × X
```

where the `1` is `conil`, interpreted as the least semantic approximation.
Consequently:

```text
list A    ≅ μ ColistF
colist A  ≅ ν ColistF
```

The generic semantic order needs at least:

- a distinguished hole shape with no recursive positions;
- the hole below every layer;
- compatible non-hole layers ordered recursively;
- equality, or a separately supplied relation, for nonrecursive data.

Begin with discrete non-hole shapes. Ordered node data, as used by cotries,
belongs in a later enriched-container extension.

### Finiteness

Directed completeness and algebraicity require different structures.  The
generic CPO construction needs a decision procedure distinguishing the bottom
shape from exposed shapes, but permits arbitrary branching.  The compact-basis
theorem additionally requires finite observations.  The current sufficient
condition is a complete enumeration:

```text
positions  : ∀ s : Shape C, list (Pos C s)
complete   : ∀ s (p : Pos C s), p ∈ positions s
```

The enumeration need not be duplicate-free for the intended proof: it is used
only to combine finitely many recursive compactness witnesses into one chain
index.

This matches the current cotree development, where the dense basis is defined
for general branching but the demonstrated `aCPO` instance uses finite Boolean
branching. The prototype must make this side condition explicit rather than
hiding it in a type-specific proof.

### Semantic fixed points and the algebraic CPO

For a pointed, finitely branching container `C`, derive:

```text
Basis C = μ C
Value C = ν C
```

and define:

```text
incl     : μ C → ν C
truncate : nat → ν C → μ C
```

The theorem inventory should include:

```text
truncate n x ⊑ truncate (n + 1) x

incl (truncate n x) ⊑ x

x = sup (λ n, incl (truncate n x))

compact b

aCPO (ν C) (μ C)
```

Equality in the supremum theorem may initially be AlgCo equivalence rather
than Coq equality. The prototype should record exactly where a coinductive
extensionality principle is required.

### Operational lifting

Let the computation lifting add a new nullary shape:

```text
T X = pending + returned X
```

For a semantic container `C`, define `Lift C` by:

```text
Shape (Lift C) = pending-shape + Shape C

Pos (Lift C) pending          = Empty
Pos (Lift C) (returned s)     = Pos C s
```

Then define:

```text
OpBasis C = μ (Lift C)
OpValue C = ν (Lift C)
```

For colists, the one-layer operational signature becomes:

```text
pending
+ returned_conil
+ returned_cocons A X
```

Thus the semantic hole and operational pending state are distinct by
construction.

The operational order should satisfy:

```text
pending ⊑ᵒ d

returned_conil ⊑ᵒ returned_conil

d₁ ⊑ᵒ d₂
────────────────────────────────────────────────────────
returned_cocons a d₁ ⊑ᵒ returned_cocons a d₂
```

In particular, a returned semantic bottom should not operationally refine into
a different returned constructor merely because the semantic order places it
below that constructor.

### Realization

Define a relation between operational and semantic fixed points by the greatest
fixed point of the container's relational action:

```text
pending R v                                    always

childrenᵒ and childrenˢ are pointwise R-related
───────────────────────────────────────────────
returned s childrenᵒ R inν s childrenˢ
```

For finite operational approximants, define the analogous relation by
induction. Establish at least:

```text
d₁ ⊑ᵒ d₂ → d₁ R v → d₂ R v

finite operational evaluation returns an observation
→ that observation is sound for the semantic value
```

Pending relates to every semantic value because it makes no observational
claim. This is the recursive analogue of `flat_realizes None v := True` in
[`cofold_operational.v`](../theories/cofold_operational.v).

### Observations and totality

Do not identify totality with semantic maximality in the generic definitions.
Define finite requests and observations from the lifted shape structure.

For the first colist instance, retain the simple depth requests:

```text
Observes 0 d                             always

Observes k tail
────────────────────────────────────────
Observes (k + 1) (returned_cocons a tail)
```

Then:

```text
Total d  := ∀ k, Observes k d

Covers q := ∀ k, ∃ n, Observes k (q n)
```

The generic development should connect this definition to the existing
observation-indexed results in
[`productivity.v`](../theories/productivity.v), not introduce a competing
meaning of coverage.

For branching containers, requests will eventually need finite shapes or
paths. This is intentionally outside the first colist milestone.

### Placement of computation at payloads

The equation

```text
OpValue C = ν (Lift C)
```

adds computation at each recursive layer but treats nonrecursive fields as
atomic values. This is appropriate for the first spine-only colist model.

A later type-directed interpretation may replace a payload parameter `A` by
its own operational interpretation `Op A`. The placement of this lifting
depends on the target's strictness and value/computation discipline. The
container prototype must not silently claim that atomic payloads are fully
evaluated.

## Proposed Coq organization

The prototype now uses the following parallel namespace:

```text
theories/generic/container.v
theories/generic/pointed_container.v
theories/generic/finitary_container.v
theories/generic/algebraic_container.v
theories/generic/colist_instance.v
```

An eventual operational layer remains provisional.  Avoid changing imports of
existing non-generic modules during the prototype.

The layers should have one-way dependencies:

```text
container
    ↓
μ/ν fixed points and relational action
    ↓
pointed order, truncation, and aCPO
    ↓
operational lifting and realization
    ↓
native-type instances and program examples
```

Keep extraction-specific definitions out of the semantic container module.

## Vertical-slice milestones

### Milestone 0: theorem inventory

Before writing generic proofs, record the current colist results that the
prototype must recover:

- constructors and one-step unfolding;
- approximation and extensional-equivalence relations;
- finite prefixes and prefix monotonicity;
- inclusion of lists into colists;
- compactness of finite lists;
- density and the canonical ideal chain;
- the `aCPO` instance;
- `cofold_nil` and `cofold_cons`;
- existing extraction behavior used by the regression examples.

This prevents a superficially elegant representation from silently dropping
essential functionality.

### Milestone 1: container fixed points

Implement `μ C` and `ν C` for a small container representation. Instantiate:

```text
ColistShape A = hole | cons A

Pos hole       = Empty
Pos (cons a)   = unit
```

Construct conversions:

```text
μ ColistC A  ↔ list A
ν ColistC A  ↔ colist A
```

Initially prove round trips using the appropriate inductive or coinductive
equivalence. Do not replace native lists or colists.

### Milestone 2: generic algebraic structure

The pointed prefix order, inclusion, depth truncation, and their colist
correspondence are complete as Milestone 1.5.  Milestone 2A additionally
provides the generic directed supremum and `CPO (ν C)` under a decidable-bottom
interface.  Milestone 2B uses finite position enumeration to prove compactness
of `μ C`.  Milestone 2C proves density and finite-truncation continuity and
assembles the generic `aCPO`; its concrete colist stack exposes the ideal as
native `prefix` without requiring clients to reconstruct container packages.
Milestone 2D separately proves standard Scott compactness of every included
`μ C` basis element against arbitrary nonempty directed families, without yet
constructing arbitrary directed suprema of `ν C`.  Milestone 2E wraps both
fixed points in descriptor-indexed carriers and recovers the complete generic
instance stack from two keyed capabilities; the colist specialization no
longer reassembles that stack concretely.  Milestone 2F reconstructs `comap`
from structural recursion on the native list basis and the generically supplied
continuous extension.  It recovers continuity and native `conil`/`cocons`
equations, and factors the shifted-supremum reasoning into reusable indexed
`cofold` rules so routine proofs do not mention containers or conversions.
Milestone 2G repeats the boundary for Boolean cotrees, reuses the same generic
instance stack, derives branching `tfold`/`tcofold` computation rules, and
recovers the native `cotree_map` node equation.  This is the first evidence
that the abstraction is not colist-specific.  Milestone 2H audits both slices,
separates generic fold and wrapper theorems from unavoidable native
presentation obligations, and specifies a minimal pointed-polynomial frontend
with an explicit container interpretation.  Milestone 2I proves the common
generic fold/cofold layer theorem and recovers both operation slices from it.

### Milestone 3: lifted operational fixed point

Implement `Lift C`, its operational order, and its realization relation.
For the colist container, demonstrate the three distinct forms:

```text
pending
returned_conil
returned_cocons
```

Recover the flat atomic lifting as the nonrecursive special case if doing so is
natural. It is not necessary to force both APIs into one encoding if that harms
proof ergonomics.

### Milestone 4: program instances

Use `comap` as the guarded baseline:

```text
productive input
→ every finite output prefix is operationally covered
```

Then use `cofilter` as the demand-sensitive test:

```text
predicate true   → expose a constructor without demanding the tail
predicate false  → continue with the recursive approximation
```

Prove:

```text
every finite operational approximation is semantically sound

enough surviving input elements
→ coverage of every finite output prefix
```

Also reproduce the coinductive two-bottom counterexample:

```text
cofilter (const false) infinite_input
```

has semantic denotation `conil` but never operationally returns an outer
constructor.

### Milestone 5: extraction and ergonomics experiment

Generic dependent container terms may extract poorly. Compare two routes:

1. Extract the generic fixed-point representation directly.
2. Retain native datatypes at runtime and use container isomorphisms only for
   proofs and derived instances.

Inspect generated Haskell for constructor clarity, laziness, dictionary noise,
and obvious performance problems. A generic proof architecture does not
require a generic runtime representation.

### Milestone 6: go/no-go review

Evaluate the success criteria below before porting any additional application.
If the result is mixed, retain the generic operational lifting as a separate
library without rewriting AlgCo's semantic core.

## Success criteria

Proceed toward a successor rewrite only if the prototype satisfies all of the
following core criteria.

### Mathematical coverage

- The generic colist instance recovers the existing approximation order,
  truncation chain, supremum, compactness, and `aCPO` results.
- A second genuinely branching instance reuses the same proofs.
- The operational lifting distinguishes pending computation from returned
  semantic bottom without ad hoc constructors for each datatype.
- Realization and finite-observation soundness are stated once and instantiated
  cleanly.

### Proof engineering

- User-facing theorem statements remain recognizable.
- Routine proofs are shorter or more reusable, rather than merely moving all
  complexity into transports and dependent equality.
- Compilation time and proof-search behavior remain practical.
- The generic development requires no stronger axioms than a clearly isolated
  analogue of principles already used by the native types.
- Error messages and simplification are tolerable for ordinary program proofs.

### Extraction

- There is a path to clean lazy target code, either directly or through native
  representation wrappers.
- The generic semantics does not force eager evaluation of recursive fields.
- `colist_existsb`, `comap`, and `cofilter` retain their intended demand
  behavior.

### Architectural payoff

- The same signature really drives semantic values, compact bases,
  operational values, and finite observations.
- The distinction between semantic and operational orders becomes clearer than
  in the current organization.
- Adding another finitary coinductive type requires mostly container data and
  type-specific payload facts, not a copied domain-theory development.

## Stop or redesign conditions

Do not proceed to a rewrite if any of these persists after a focused attempt:

- Coq's positivity or guardedness rules prevent usable generic `μ`/`ν` types.
- Coinductive equality transports dominate every proof.
- The finite-branching compactness theorem cannot be expressed without nearly
  all of the current type-specific arguments.
- Extracted terms expose dependent container encodings with no clean native
  boundary.
- Ordered payloads require an abstraction so complicated that the simple
  colist and cotree cases become harder to use.
- Operational strictness still has to be restated entirely for every program,
  leaving little benefit beyond semantic code deduplication.

Failure of the full rewrite criterion would not invalidate the operational
insights. The lifted-container or realization components may still be useful
as independent additions.

## Compatibility and migration strategy

If the review favors a rewrite:

1. Treat it as a successor implementation rather than editing the paper
   artifact destructively.
2. Preserve the current modules and examples as regression oracles.
3. Provide conversions or compatibility lemmas for native datatypes.
4. Port in increasing order of difficulty: conat, colist, cotree, then cotrie.
5. Keep nonrecursive semantic domains such as `bool`, `Prop`, and `eR` outside
   the container hierarchy unless there is an independent reason to move them.
6. Port sieve only after operational `cofilter` coverage has a satisfactory
   statement.
7. Re-run extraction examples at every migration milestone.

It may be preferable to publish the generic core as a new library or namespace
and let AlgCo instances depend on it. A source-level rewrite and a runtime
representation rewrite are separate decisions.

## Open questions

1. Should the first signature universe use simple containers, indexed
   containers, or an ordered/container-enriched record?
2. What is the minimal finiteness structure needed to prove compactness while
   retaining usable computation?
3. Can a single generic coinductive extensionality principle replace the
   current type-specific axioms?
4. Should the full operational domain `ν (Lift C)` be built immediately, or
   should the first evaluator use only finite elements `μ (Lift C)`?
5. Can finite requests be derived generically from the container, or should
   observations remain an explicit parameter?
6. How should ordered nonrecursive data, especially cotrie labels, participate
   in the semantic and operational relations?
7. Where should computation be inserted for lazy payloads, products, sums, and
   function fields?
8. Can target adequacy be modularized over a generic lifted step, or does it
   require a target-language semantics before further abstraction is useful?
9. Should generic types be extracted directly, or erased in favor of native
   representations certified by isomorphisms?
10. How much of the existing `aCPO` API should remain the public interface even
    if its instances become generically derived?

## Immediate next experiment

Milestone 2J removes capability derivation as a reason to add reified syntax.
The next informative task is the native-presentation boundary:

1. Define the smallest `NativePresentation` record containing native basis and
   value conversions, round trips, order correspondence, and the inclusion and
   truncation commuting laws.
2. Derive the repeated wrapper monotonicity, continuity, ideal, and compactness
   bridge lemmas once from that record.
3. Instantiate the record for the existing colist and Boolean-cotree
   presentations without deleting their current regression oracles.
4. Recover the native `comap` and `cotree_map` proof boundaries and compare
   declarations, proof terms, error messages, and assumptions.
5. If that gate passes, freeze the semantic representation and attempt
   Milestone 3's operational lifting directly over pointed containers and
   their capabilities.
6. Add a reified signature code only if operational lifting requires induction
   over the construction of constants, products, sums, and recursive fields.
