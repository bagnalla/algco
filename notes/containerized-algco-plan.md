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

A rewrite is justified only if one complete vertical slice is clearer and at
least as usable as the current type-specific development. Until that decision
point, all generic work should live alongside the current modules.

This plan grew out of the investigation in
[`cofold-extraction-productivity.md`](cofold-extraction-productivity.md). That
report remains the record of the extraction problem and the observation-indexed
productivity results. This document concerns the broader architecture suggested
by that work.

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

The compact-basis theorem requires finite observations. For containers, the
first sufficient condition should be:

```text
∀ s : Shape C, Pos C s is finite
```

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

Define the pointed prefix order, inclusion, and depth truncation generically.
Prove the `aCPO` laws under finite branching, then transport or compare them to
the existing colist instance.

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

The smallest informative implementation task is Milestone 1 only:

1. Define a simple container by shapes and positions.
2. Define its generic inductive and coinductive fixed points.
3. Instantiate the pointed colist signature.
4. Construct conversions to the existing `list` and `colist` types.
5. Prove the inductive round trip and a coinductive bisimulation round trip.
6. Record every required axiom, guardedness workaround, and extraction artifact.

Do not implement the generic order or operational lifting until this experiment
shows that the fixed-point representation itself is workable in Coq.
