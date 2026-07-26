# AlgCo 2 design sketch

## Status

This document is a provisional architectural synthesis, not a commitment to
rewrite AlgCo.  It records design consequences that have emerged from the
container prototype and the investigation of extracted `cofold`s.

The empirical record remains in:

- [`containerized-algco-plan.md`](containerized-algco-plan.md), for prototype
  milestones, proof sizes, and assumption audits;
- [`cofold-extraction-productivity.md`](cofold-extraction-productivity.md), for
  the extraction problem and observation-indexed account of productivity.

The rewrite gate is unchanged: a successor design must recover a complete
vertical slice, including native proof ergonomics, before replacing any of the
existing type-specific development.

## Emerging design thesis

AlgCo currently uses one order-theoretic interface for several related but
distinct purposes.  A successor should separate at least three layers:

1. **Denotational order theory:** ordinary directed completeness,
   Scott-continuity, compactness, and algebraicity.
2. **Sequential presentation:** a canonical natural-number-indexed sequence
   of finite approximants used to define extensions and support structural
   proofs.
3. **Operational computation:** pending computations, finite observations,
   realization, and coverage/productivity.

The layers should be connected by theorems rather than identified by
definition.  In particular, an order on `Prop`, `bool`, or another already
computed value type need not be an operational approximation order.  The
possibility of divergence belongs to the operational lifting, not implicitly
to every semantic `OType`.

Containers or a related strictly-positive code language remain promising as
the description from which the recursive parts of all three layers can be
derived.  Whether containers are the final public abstraction is still open.

## Directed completeness and the computational presentation

### Use both arbitrary directed families and canonical sequences

AlgCo 2 should not choose between arbitrary directed completeness and
countable approximations.  They answer different questions.

The semantic structure should use standard domain-theoretic definitions.  A
directed family must be explicitly nonempty:

```text
DirectedFamily A =
  an inhabited index type I,
  a family d : I → A,
  and ∀ i j, ∃ k, d i ⊑ d k ∧ d j ⊑ d k

DCPO A = every DirectedFamily A has a supremum

ScottCompact k =
  ∀ D, k ⊑ sup D → ∃ i, k ⊑ D i

ScottContinuous f =
  f is monotone and preserves all directed suprema
```

Nonemptiness is not cosmetic.  The current sequence-based definitions hide it
because `nat` is inhabited, whereas the existing definition of `directed` is
vacuously true for an empty index type.

Alongside this, AlgCo needs a canonical sequential presentation:

```text
SequentialPresentation A B =
  incl   : B → A
  approx : A → nat → B

  approx x is increasing
  incl (approx x n) ⊑ x
  x is the supremum of λ n, incl (approx x n)
  order and compactness laws for basis elements
```

For a pointed finitary signature `C`, the intended instance remains:

```text
B = μ C
A = ν C
approx x n = truncate n x
```

This sequential presentation is the source of AlgCo's low-friction proof
principle: define a function by structural recursion on `μ C`, then extend it
continuously to `ν C`.  Natural numbers also align approximation depth with
finite operational observations.

The presentation should not automatically be called “ω-algebraic.”  In
standard terminology that can imply a globally countable basis, while
`list A` is not countable for arbitrary `A`.  What AlgCo has is a canonical
sequence of compact approximants for each value, potentially drawn from an
uncountable basis type.

### Why full directed completeness does not weaken computability

An arbitrary directed supremum is a denotational operation, not necessarily an
algorithm.  Adding the theorem that it exists therefore does not make the
canonical truncation sequence less computational.

Conversely, indexing a supremum by `nat` does not by itself make it executable.
The current generic `nu_sup` uses strong LPO and indefinite description.  Its
index type is countable, but its selected witness has no useful extracted
computational content.  The actual computability story comes from explicit
truncations, operational evaluation, observations, and coverage theorems.

Full Scott-continuity is still useful.  Together with compact observations it
says that every finite output fact is forced by some finite member of a
directed input.  An effective semantics must additionally explain how the
witness is computed or operationally covered.

### Proposed terminology

The current library names are historically understandable but ambiguous.  A
successor should distinguish the two levels explicitly:

| Current concept | Provisional AlgCo 2 name |
|---|---|
| `CPO` over `nat → A` | `OmegaCPO` or `SequentialCPO` |
| `continuous` over sequences | `omega_continuous` |
| `compact` over sequences | `omega_compact` |
| arbitrary directed completeness | `DCPO` |
| preservation of arbitrary directed suprema | `scott_continuous` |
| standard directed compactness | `scott_compact` |
| current `aCPO` data | `SequentialPresentation` or `PresentedDomain` |

The exact names are open.  The important point is that documentation should
not silently call an ω-directed statement “Scott-open” or “compact” in the
unrestricted sense.

### Expected relationship for container fixed points

The compactness prototype suggests the following factorization:

- the distinguished bottom controls whether a layer exposes information;
- child projection transports existing suprema pointwise;
- finite branching is used only to merge one witness per child;
- the canonical depth truncations provide sequential density.

The proof that `μ C` is compact should plausibly generalize from countable
directed sequences to arbitrary nonempty directed families.  Finite branching
is substantive here.  If a constructor has infinitely many positions, one
`μ C` node may contain infinitely many children, and a directed family can
reveal successively more children without any member containing the whole
node.

The full `DCPO (ν C)` construction and Scott-continuity laws should be tested
separately.  They may introduce universe and choice complications even if the
mathematics is straightforward.

## Semantic values and operational computations

The order-theoretic layer should not be required to interpret every order as
partial computation.  AlgCo legitimately uses implication on `Prop` and the
truth order on `bool`; those are semantic information orders on values that
may already have been computed.

Operational partiality should be introduced explicitly, in a Moggi-like
value/computation split:

```text
T A = pending + returned A
```

For recursive signatures, the placement of `T` must be derived structurally
rather than added only at the outside.  The current container proposal uses a
lifted signature with a fresh pending shape at each recursive layer.  This
distinguishes:

```text
pending computation
returned semantic bottom
returned exposed constructor
```

The operational order and realization relation then explain which finite
claims a computation has made about a semantic value.  Productivity is stated
through observation coverage, not semantic maximality.

This remains compatible with a monadic account of computations.  What a plain
`T A` does not determine is where computations occur inside a recursive type,
or which payload fields are strict.  The signature or type code must retain
that information.

## Typeclass resolution and descriptor identity

### The concrete failure

The prototype fixed points are indexed by the underlying container:

```text
mu (pc_container C)
nu (pc_container C)
```

The order and compactness instances, however, depend on the larger pointed or
finitary package `C`.  Coq cannot generally reconstruct that package from the
carrier type.  During the compactness specialization it could not infer an
instance such as:

```text
OType (mu (colist_container A))
```

from the generic pointed-container instance.  A concrete colist registration
was needed, and some statements still have to name the intended `OType`
explicitly.

This is not merely a typeclass-search tuning problem:

- projections such as `pc_container` are not invertible during unification;
- two pointed packages can share an underlying container but choose different
  bottom shapes and therefore different orders;
- finiteness and decidability evidence is not present in the carrier type;
- adding more global overlapping instances would make the selected semantics
  less predictable.

The same problem will recur for `PType`, `CPO`, `Dense`, `aCPO`, operational
liftings, and realization structures.  It should be addressed before the
generic representation becomes a user-facing foundation.

### Design alternatives

#### 1. Keep the full descriptor in the fixed-point type

Define fixed points directly over a pointed or AlgCo signature:

```text
Basis S = μ indexed by S
Value S = ν indexed by S
```

The type head must retain `S`; a transparent abbreviation for
`mu (underlying S)` may reproduce the current problem.  Directly indexed
inductives/coinductives or small wrapper records would make the descriptor
available to unification.

This gives the most reliable generic instance search, at the cost of wrappers
or duplication between fixed points over differently enriched descriptors.

#### 2. Separate signature data from canonical laws

A code language can make shapes, positions, bottom, and perhaps finiteness
canonical functions of a syntactic code.  Instances are then keyed by a code
that remains visible in `Basis code` and `Value code`, instead of by a
proof-rich record that must be reconstructed.

This is one reason functor codes may ultimately be more convenient than fully
open containers.  It is not yet enough reason to abandon containers: an
enriched container descriptor can serve the same indexing role.

#### 3. Bundle domains rather than infer them from carrier types

A `Domain` record can package its carrier, order, completeness, and basis.
Generic constructions would take an explicit domain object, perhaps with a
coercion to its carrier type.  This permits multiple orders on one Coq type
without global-instance ambiguity, but makes some statements more explicit.

#### 4. Use module-scoped or concrete instances

The generic kernel can keep descriptor arguments explicit, while each native
specialization registers a coherent local stack of `OType`, `CPO`, `Compact`,
and `aCPO` instances.  This is close to the current prototype and provides a
good user boundary, but it creates repetitive instance plumbing and does not
solve generic inference by itself.

### Provisional direction

The most promising design is a hybrid:

- keep the semantic descriptor syntactically visible in generic `Basis S` and
  `Value S` types;
- keep generic kernel theorems explicit about `S` rather than relying on
  typeclass search to reconstruct it;
- separate computational signature data from optional proof evidence where
  possible;
- expose native types through one-time specializations with a coherent,
  concrete instance stack;
- consider a bundled `Domain` interface wherever multiple orders on one
  carrier are legitimate.

Proof ergonomics should decide among direct descriptor-indexed fixed points,
wrappers, and a code language.  Typeclass cleverness should not be used to
hide a semantically ambiguous choice.

## Proof ergonomics boundary

Users of common instances should normally see native types and familiar
reasoning principles:

```text
list A, colist A, list_le, colist_le, inj, prefix
```

The following may remain inside the generic kernel or one-time instance proof:

```text
shapes, positions, transports, descriptor wrappers, generic fixed points
```

Concrete specialization should provide constructor equations, induction
principles, continuity lemmas, and automation stated over the native API.  The
generic representation is successful only if routine proofs do not repeatedly
transport through representation isomorphisms.

The `comap` reconstruction remains the first decisive test of this boundary.

## Provisional decisions

1. Do not replace sequential approximation with arbitrary directed sets.
   Provide standard directed semantics and retain the canonical sequence as
   additional computational presentation.
2. Require arbitrary directed families to be nonempty explicitly.
3. Do not claim that a classically selected semantic supremum is executable.
4. Keep semantic and operational approximation orders distinct.
5. Do not expect Coq to infer a pointed/finitary descriptor from its projected
   carrier type.
6. Keep generic machinery behind native specializations unless a use case
   genuinely benefits from the generic representation.

These are working decisions for experiments, not yet compatibility promises.

## Open questions

- Should arbitrary directed families be represented by inhabited indexed
  families or nonempty predicates `A → Prop`?
- Should semantic orders remain preorders with explicit equivalence, or should
  the new kernel use partial orders or setoid quotients?
- Can full `DCPO (ν C)` and Scott-compactness of `μ C` be proved without
  making universe-polymorphic APIs unpleasant?
- Should the descriptor-indexing problem be solved by enriched containers,
  functor codes, wrappers, or bundled domains?
- Which structure should contain ordered nonrecursive payload fields?
- Can native constructor equations for `comap` be recovered without exposing
  conversions or dependent transports?
- How much of the semantic layer can remain constructive if operational
  productivity is treated separately?

## Next experiments

1. Finish sequential density and the current generic `aCPO` instance without
   refactoring the prototype.
2. Re-run the compactness argument for an arbitrary nonempty directed family
   and record the proof, universe, and assumption costs.
3. Build a minimal descriptor-indexed wrapper or fixed point and confirm that
   `OType`, `Compact`, and `CPO` resolution becomes deterministic.
4. Reconstruct native colist `comap` and compare its statements and proof
   scripts directly with the existing implementation.
5. Use those results, rather than the elegance of the generic kernel alone,
   to decide whether a larger rewrite is justified.
