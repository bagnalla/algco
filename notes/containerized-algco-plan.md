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

This plan grew out of the investigation in
[`cofold-extraction-productivity.md`](cofold-extraction-productivity.md). That
report remains the record of the extraction problem and the observation-indexed
productivity results. This document concerns the broader architecture suggested
by that work.

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

This is encouraging but not yet the decisive proof-ergonomics result.  The
prototype has not derived the complete algebraic CPO structure or reconstructed
a representative operation such as `comap`.  That vertical slice is the next
gate: its definition, continuity proof, constructor equations, and ordinary
program proofs should expose no container machinery and should be comparable
in size and clarity to the current AlgCo proofs.

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

The remaining part of Milestone 2 is algebraicity: compactness of `μ C`,
density through truncation, and the resulting `aCPO` instance.  Only that step
uses the finitary extension.  Afterward `comap` remains the decisive test of
the user-facing proof interface.

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

Use a parallel namespace, tentatively:

```text
theories/generic/container.v
theories/generic/fixedpoint.v
theories/generic/algebraic.v
theories/generic/operational.v
theories/generic/colist_instance.v
```

These names are provisional. Avoid changing imports of existing modules during
the prototype.

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
interface.  Next use finite position enumeration to prove compactness of
`μ C`, density of truncations, and the remaining `aCPO` laws.  Expose the
result through native colist-specific lemmas rather than requiring users to
transport goals manually.

As the proof-ergonomics test, reconstruct `comap` from structural recursion on
the native list basis and the generically supplied continuous extension.
Recover its continuity and `conil`/`cocons` equations with statements that do
not mention containers or conversions.  Compare those proof scripts directly
with the current implementation before proceeding.

Repeat only the essential fixed-point and truncation results for Boolean
cotrees. Success on cotrees is the first evidence that the abstraction is not
colist-specific.

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

Milestones 1, 1.5, and 2A establish the representation, specialization
boundary, and generic CPO.  The next informative task completes the
algebraic-operation slice:

1. Use the finite position enumeration to prove compactness of `μ C`.
2. Prove that the included truncation chain has supremum `x` and package the
   generic `Dense` and `aCPO` instances.
3. Expose the result to native colists without visible transports.
4. Define the native-list basis map structurally and obtain `comap` by
   continuous extension.
5. Recover continuity and the two native constructor equations.
6. Compare the resulting user proof with the existing `comap` development,
   including required axioms, simplification behavior, error messages, and
   proof length.

Do not add a functor-code language yet.  If this slice succeeds but the
one-time instance contains repetitive structural boilerplate, codes become a
promising derivation frontend with containers as their semantic backend.  If
the user-facing proof remains transport-heavy, adding another abstraction
layer would not address the primary failure.
