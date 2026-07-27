# AlgCo 2 design sketch

## Status

This document is a provisional clean-slate design for AlgCo 2.  AlgCo 2 should
serve the same mathematical and proof-engineering purpose as AlgCo, but it is
not a source-compatible revision, migration target, or compatibility layer.
The document records design consequences that have emerged from the container
prototype and the investigation of extracted `cofold`s.

The empirical record remains in:

- [`containerized-algco-plan.md`](containerized-algco-plan.md), for prototype
  milestones, proof sizes, and assumption audits;
- [`cofold-extraction-productivity.md`](cofold-extraction-productivity.md), for
  the extraction problem and observation-indexed account of productivity.

The design gate remains conservative about complexity, not about compatibility.
Milestones 2F and 2G recover complete `comap` and branching `cotree_map` proof
shapes with competitive ergonomics.  Milestone 2H audits their duplication,
while Milestone 2I proves the common generic fold/cofold layer theorem.
Milestone 2J shows that direct container combinators derive bottom and
finiteness capabilities without reified syntax.  Milestone 2K proves that a
native/generic presentation boundary can be made sound and
assumption-disciplined, but also measures the considerable machinery required
solely because two representations coexist.  Milestone 2L obtains the same
proof ergonomics with generic fixed points as the only representation and
removes that experimental boundary.

The next architectural test has now been sharpened.  The point used by those
experiments need not belong to the signature of fully formed semantic values.
Instead, an unpointed, hole-free semantic final coalgebra `ν C` can be embedded
into the algebraic partial completion `ν (Lift C)`, whose finite basis is
`μ (Lift C)`.  Milestone 2L validates the generic fixed-point façade for a
pointed descriptor; it does not decide that the point belongs in `C` rather
than in `Lift C`.  The `zar` interaction-tree use case is the first required
branching acceptance test for this separation.

Milestone 2M's first implementation checkpoint now validates the carrier half
of this design.  `Semantic C` is defined for an arbitrary container, while
`FinitePartial C` and the algebraic `Partial C` retain a finitary presentation
for compactness and typeclass identity.  The existing `finitary_point` is the
required structural lift.  The canonical colist slice now has exact semantic
`nil`/`cons`, distinct partial `pending`/`returned_nil`/`returned_cons`, a
generic structural embedding, three-case basis induction, and a continuous
partial map.  Realization and totality remain the next checkpoint.

## Clean-slate constraint

Backward compatibility is not an AlgCo 2 goal.  In particular:

- AlgCo 2 should not preserve AlgCo names, module boundaries, carrier types,
  theorem statements, or extraction representations merely because they
  already exist;
- it should not carry parallel generic and historical public APIs, transition
  wrappers, conversion layers, or compatibility lemmas;
- the original development is empirical evidence and a source of mathematical
  requirements, not an implementation dependency or migration constraint; and
- a familiar datatype such as `list` may be selected only if it is the best
  clean-slate representation on proof, semantic, or runtime grounds.

The default is one canonical representation.  A second representation must be
justified by an intrinsic requirement such as materially better extraction,
and even then should remain an implementation mechanism rather than create a
second public reasoning API.  Git history and the experimental notes preserve
discarded designs; AlgCo 2 itself need not retain them.

`Semantic C` and `Partial C` are not parallel representations of one carrier.
They have different inhabitants and roles: only the latter contains incomplete
observations and carries the algebraic approximation order.  Each role should
still have one canonical generic representation, connected by a structural
embedding rather than a compatibility isomorphism.

## Emerging design thesis

AlgCo currently uses one order-theoretic interface for several related but
distinct purposes.  AlgCo 2 should separate at least four roles:

1. **Semantic values:** fully formed values and any intrinsic semantic order
   they carry.  A recursive value type may simply be the final coalgebra
   `ν C`; it need not contain an approximation hole or even be used as a CPO.
2. **Partial completion:** a domain `ν (Lift C)` that adds a fresh hole at each
   recursive layer and carries the directed-complete approximation order.
3. **Sequential presentation:** the compact basis `μ (Lift C)` and a canonical
   natural-number-indexed sequence of finite approximants used to define
   extensions and support structural proofs.
4. **Operational computation:** evaluators producing partial approximants,
   finite observations, realization, and coverage/productivity.

The layers should be connected by theorems rather than identified by
definition.  In particular, an order on `Prop`, `bool`, or another already
computed value type need not be an operational approximation order.  A genuine
least semantic value, when one exists, is also distinct from the fresh hole
introduced by `Lift`.  The possibility of incomplete observation belongs to
the partial completion, not implicitly to every semantic `OType`.

Containers or a related strictly-positive code language remain promising as
the description from which the recursive parts of all four roles can be
derived.  Whether containers are the final public abstraction is still open.

## Directed completeness and the computational presentation

### Use both arbitrary directed families and canonical sequences

AlgCo 2 should not choose between arbitrary directed completeness and
countable approximations.  They answer different questions.

The order-theoretic structure should use standard domain-theoretic definitions.
A directed family must be explicitly nonempty:

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

Alongside this, AlgCo needs canonical sequential approximation data.  The
current class called `Dense` contains only this data and does not prove
density, so `Approx` is the shorter working name for its replacement:

```text
Approx A B =
  incl   : B → A
  approx : A → nat → B

Dense (p : Approx A B) =
  approx x is increasing
  incl (approx x n) ⊑ x
  x is the supremum of λ n, incl (approx x n)
  monotonicity and finite-observation continuity laws

Algebraic A B p =
  Dense p
  inclusion reflects the basis order
  included basis elements are compact
```

`Approx` is provisional, but it is deliberately short.  `Presentation` is
another plausible name.  `Dense` should be reserved for a structure carrying
the convergence laws that justify the term.

For a finitary semantic signature `C`, the intended computational presentation
is now:

```text
Semantic C      = ν C
FinitePartial C = μ (Lift C)
Partial C       = ν (Lift C)
approx x n      = truncate n x
```

The `Approx`/`Dense`/`Algebraic` structure relates `FinitePartial C` to
`Partial C`.  This sequential presentation is the source of AlgCo's
low-friction proof principle: define a function by structural recursion on
`μ (Lift C)`, then extend it continuously to `ν (Lift C)`.  Natural numbers
also align approximation depth with finite operational observations.  The
unlifted initial algebra `μ C` may still describe finite completed semantic
values, but it is generally not a compact basis for `ν C`.

The completed prototype used an already-pointed descriptor `S` and wrote these
types as `Basis S = μ S` and `Value S = ν S`.  Its results can be reused by
taking `S = Lift C`; the experiment should not be read as evidence that every
semantic signature must itself be pointed.

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
| current `Dense` data (`incl` and `ideal`) | `Approx` |
| density laws currently stored in `aCPO` | `Dense` or `ApproxLaws` |
| complete current `aCPO` package | `Algebraic` or `PresentedCPO` |

The exact names are open.  The important point is that documentation should
not silently call an ω-directed statement “Scott-open” or “compact” in the
unrestricted sense.

### Expected relationship for container fixed points

The compactness prototype suggests the following factorization for the lifted
partial descriptor `Lift C`:

- the distinguished bottom controls whether a layer exposes information;
- child projection transports existing suprema pointwise;
- finite branching is used only to merge one witness per child;
- the canonical depth truncations provide sequential density.

Milestone 2C verifies the last point generically.  Density needs only a pointed
signature—now understood as the partial descriptor—and finite-truncation
continuity needs the current
decidable-pointed interface but not finite branching.  Continuity proves
leastness independently at each child, so it does not need to synchronize a
single stage across all positions.

Milestone 2D verifies the standard compactness claim as well:

```text
∀ b : μ (Lift C), ScottCompact (incl b : ν (Lift C))
```

Here a family is an arbitrary `d : I → ν (Lift C)`, with `inhabited I` carried
as an explicit premise.  Its supremum is supplied relationally.  Child projection
transports that supremum, induction chooses one witness member for each finite
child, and the position enumeration plus directedness synchronizes them.  Coq
accepts the index universe independently of the carrier universe.  Thus
countability was incidental to the earlier theorem, while finite branching is
substantive: with infinitely many positions, a family can reveal successively
more children without any member containing the whole finite-basis node.

The assumption cost is unchanged from the generic sequential proof:
excluded middle, constructive indefinite description, and `Eq_rect_eq`.
Because the supremum is supplied and only an existential witness is required,
the exposed-member lemma applies excluded middle directly to the indexed
family and does not invoke the strong-LPO sequence search used to construct
the existing semantic supremum.

This result does not construct arbitrary directed suprema.  The full
`DCPO (ν (Lift C))` construction and Scott-continuity laws should be tested
separately.  They may introduce universe and choice complications even if the
mathematics is straightforward.  In particular, the existing `CPO (ν C)`
instance for a generic pointed descriptor remains sequence-based.

## Semantic values and operational computations

The order-theoretic layer should not be required to interpret every order as
partial computation.  AlgCo legitimately uses implication on `Prop` and the
truth order on `bool`; those are semantic information orders on values that
may already have been computed.

Nor does an algebraic CPO intrinsically have to be pointed: directed
completeness concerns inhabited directed families and does not imply a least
element.  The problem is more specific.  For a recursive type such as streams,
finite observations need open recursive boundaries.  If those holes are
removed from both the values and the basis, finite completed values cannot
approximate an infinite value.  Giving the pure final coalgebra the discrete
order would make whole infinite values compact, which is mathematically valid
but destroys AlgCo's computational proof principle.

The clean split is therefore:

```text
Semantic C      = ν C
Lift C          = pending + returned C
FinitePartial C = μ (Lift C)
Partial C       = ν (Lift C)
```

`Lift C` adds a fresh nullary shape, ordered below every returned layer.  It is
both an algebraic partial completion of the recursive values and the natural
result domain for an evaluator.  This is Moggi-like in separating values from
computations, but it is not merely an outer `T (ν C)`: the lift occurs again at
every recursive boundary.  The embedding

```text
embed : Semantic C → Partial C
```

returns every semantic layer and recursively embeds its children.  Its image
is intended to be exactly the total elements of `Partial C`, up to the chosen
coinductive equivalence.

For the ordinary colist signature `C X = 1 + A × X`, the nullary semantic
shape means exact `nil`.  Lifting gives three operational layers:

```text
pending
returned_nil
returned_cons a tail
```

`returned_nil` is not an approximation hole and cannot refine to a cons.  If a
different semantic type genuinely has a least value, `pending` is still
distinct from `returned` applied to that value.  This avoids conflating
semantic orders—such as implication on `Prop`—with operational divergence.

The partial order and realization relation explain which finite claims a
partial value has made about a semantic value.  Realization is contravariantly
closed under loss of information:

```text
d₁ ⊑ d₂ → d₂ realizes v → d₁ realizes v
```

The converse is false: `pending` realizes every value but may refine to a
returned constructor inconsistent with a particular value.  An evaluation
chain must separately prove that every stage realizes its intended denotation.
Productivity is then stated through observation coverage, not semantic
maximality.

Totality means that no finite request encounters `pending`; it does not mean
maximality.  In particular, exact finite `nil` is total, and an infinite chain
of returned `Tau` constructors is also a fully formed interaction tree even
though the represented program does not terminate.  Construction
productivity, semantic program termination, and weak `Tau` equivalence must
remain separate notions.

AlgCo's continuous extensions should primarily operate on partial domains:

```text
f̂ : Partial C → D
```

Here `D` may be any suitable result domain, such as ordered propositions for a
WP.  Their proofs still reduce to structural induction over
`FinitePartial C`.  For a recursive result, take `D = Partial C₂`; a function
on fully formed values is recovered when `f̂ (embed v)` is total for every
semantic `v`.  It can then be factored through the total-image theorem to
obtain `Semantic C → Semantic C₂`.  If totality fails, the partial result is
meaningful evidence of a nonproductive or incomplete computation rather than
an ill-formed semantic value.  This totality-preservation theorem is the bridge
that lets the value/computation split retain AlgCo's original proof benefit.

This remains compatible with a monadic account of computations.  What a plain
`T A` does not determine is where computations occur inside a recursive type,
or which payload fields are strict.  The signature or type code must retain
that information.

## Interaction trees as an acceptance case

The vendored AlgCo development in `~/source/zar/` supplies a concrete reason
for the split.  Its cotree has `cobot`, `coleaf`, `cotau`, and `conode`, and its
finite basis has the corresponding `abot` hole.  However, `icotree` maps
interaction-tree `Ret`, `Tau`, and `Vis` constructors to leaf, tau, and node;
it never produces `cobot`.  This is strong evidence that `cobot` is a
partial-completion hole rather than a constructor of the fully formed
interaction-tree semantics.

For an event signature `E : Type → Type` and result type `R`, the relevant
semantic container is schematically:

```text
Shape = Ret (r : R) | Tau | Vis (X : Type) (e : E X)

Pos (Ret r)   = Empty
Pos Tau       = unit
Pos (Vis X e) = X
```

The partial domain is obtained by adding `pending` with `Lift`; `Tau` remains
an ordinary returned semantic layer.  The first vertical slice should use
`zar`'s Boolean event signature, where every visible response type is finite.
The current compactness argument does not make a full visible node compact
when its response type is infinite, so arbitrary event signatures require
either an explicit finitary restriction or a different finite-observation
basis.

`zar` also records the desired proof pattern: `cotwp` is obtained by continuous
extension from a structurally recursive finite-tree transformer, `itwp` is its
composition with `icotree`, and representative laws reduce to induction over
the finite tree basis.  AlgCo 2 should reproduce that shape over the canonical
generic carriers and show that the resulting operations respect the intended
`Tau`/`eutt` reasoning.  This is an acceptance test, not a requirement to port
the whole project.

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

Milestone 2C confirms both sides of this diagnosis.  A concrete colist module
can register a coherent `OType`/`PType`/`Compact`/`CPO`/`Dense`/`aCPO` stack,
after which ordinary typeclass search succeeds.  The generic instances still
need the descriptor supplied explicitly.  Concrete registration is therefore
a viable specialization boundary, but it does not remove the need for a
descriptor-indexed generic design.

Milestone 2E tests that generic design with actual record wrappers
`Basis S` and `Value S`, indexed by a visible pointed descriptor.  Bottom
decidability and finite positions are separate capabilities keyed by `S`.
For colists, registering only those two capabilities is sufficient for
ordinary typeclass search to derive the generic `OType`, `PType`, `Compact`,
`CPO`, `Dense`, and `aCPO` instances.  The resulting proof term applies the
generic `aCPO_indexed_container` directly; it does not reconstruct the five
algebraicity obligations in the colist module.

This isolates the earlier failure: the problem was the loss of descriptor
identity in the raw carrier head, not an inherent inability of Coq to reuse
the generic theorem.  It also exposes a remaining coherence condition.
`DecidableBottom S` and `FinitePositions S` contain computational choices, so
a public API should provide one canonical instance per descriptor or pass the
choice explicitly.

### Approximation data, laws, and instance identity

The current `Dense` class is data in `Type` containing only `incl` and `ideal`.
Its name promises a theorem that is not present until the separate `aCPO`
instance proves `supremum_ideal`.  The proposed split is therefore:

```text
Approx A B             raw inclusion and approximation functions
Dense A B p            laws proving that p converges densely
Algebraic A B p         compact-basis and order-embedding laws
```

Milestone 2C exposed a related Coq issue.  The current `aCPO` class is indexed
by the particular `Compact`, `Dense`, and `CPO` instance terms selected during
elaboration.  The concrete colist `aCPO` consequently had to reassemble five
short obligations even though the generic theorem had already proved them for
extensionally the same operations.

The approximation data genuinely matters: two presentations of the same
carrier can choose different inclusions or approximation sequences.  Proofs
that a fixed presentation is compact or complete should not create the same
identity friction.  The redesign should therefore give approximation data an
explicit stable identity while keeping proof-only law instances reusable—by
bundling the laws with the data, using proof-irrelevant fields carefully, or
making generic construction parameters explicit rather than relying on an
ambient instance stack.

### Design alternatives

#### 1. Keep the full partial descriptor in the fixed-point type

Define the algebraic fixed points directly over a pointed partial signature:

```text
Basis S = μ indexed by S
Value S = ν indexed by S
```

The type head must retain `S`; a transparent abbreviation for
`mu (underlying S)` may reproduce the current problem.  Directly indexed
inductives/coinductives or small wrapper records would make the descriptor
available to unification.

The unlifted `Semantic C = ν C` remains indexed by `C`; normally `S = Lift C`.
This gives the most reliable generic instance search, at the cost of wrappers
or duplication between fixed points over differently enriched descriptors.
Milestone 2E confirms the instance-search claim for one-field wrappers.  It
also shows that capabilities can be keyed by a stable pointed descriptor
rather than included in the carrier index itself.

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

The generic kernel can keep descriptor arguments explicit, while each
descriptor specialization registers a coherent local stack of `OType`, `CPO`,
`Compact`, and `aCPO` instances over its canonical aliases.  This is close to
the current prototype and provides a good user boundary, but it creates
repetitive instance plumbing and does not solve generic inference by itself.

### Provisional direction

The most promising implementation design is a hybrid:

- keep the pointed partial descriptor syntactically visible in generic
  `Basis S` and `Value S` types, with `S = Lift C` in the normal construction;
- retain the unlifted semantic descriptor `C` in `Semantic C`, and expose an
  explicit structural embedding into `Value (Lift C)`;
- keep generic kernel theorems explicit about `S` rather than relying on
  typeclass search to reconstruct it;
- separate computational signature data from optional proof evidence where
  possible;
- make `Basis S` and `Value S`, or transparent descriptor-specific aliases of
  them, the canonical carriers rather than converting to independently
  declared native types;
- use a short raw-data interface such as `Approx`, and reserve `Dense` for
  actual convergence laws;
- consider a bundled `Domain` interface wherever multiple orders on one
  carrier are legitimate.

Proof ergonomics should decide among direct descriptor-indexed fixed points,
wrappers, and a code language.  Typeclass cleverness should not be used to
hide a semantically ambiguous choice.

## Proof ergonomics boundary

Users of common instances should normally see concise descriptor-specific
names and familiar reasoning principles over the canonical generic carriers.
The names must distinguish semantic values from partial values without exposing
raw descriptor plumbing; the exact vocabulary remains open.  For example:

```text
Colist A, PartialColist A, ColistBasis A, colist_le, incl, prefix
```

These names should be transparent aliases or a single canonical specialization,
not a second datatype connected by an isomorphism.  Named constructors,
destructors, induction principles, folds, truncations, and computation lemmas
should hide:

```text
raw shapes, position injections, transports, and descriptor plumbing
```

Concrete specialization should provide constructor equations, induction
principles, continuity lemmas, and automation directly over those canonical
types.  The generic representation is successful only if routine proofs see
ordinary structural reasoning and never cross a representation isomorphism.

Milestone 2E showed that descriptor-indexed carriers can hide the generic
instance stack.  Its native conversion boundary was part of the experiment,
not a feature AlgCo 2 must preserve.

Milestone 2F establishes the desired operation-level proof shape: structural
recursion on a compact basis, generic continuous extension, and short
constructor equations.  It happened to cross through native lists and colists
for comparison with AlgCo.  A clean-slate implementation should reproduce the
proof shape without that conversion.

The first direct `cocons` proof revealed an important placement rule.  It
repeated the shifted-supremum argument hidden by AlgCo's existing
`co_fold_cons`.  That argument is representation infrastructure, not an
operation obligation.  Factoring it once into `indexed_co_fold` and
`indexed_cofold` constructor rules restores the existing proof shape: the
`comap` proof supplies only continuity of `cocons`.  AlgCo 2 should therefore
derive or specialize fold/cofold computation principles together with each
signature, rather than exposing only a bare algebraic CPO.

One elaboration seam remains relevant: generic ideal rewriting sometimes
requires explicitly unfolding the current basis alias.  A clean specialization
therefore needs stable transparent names and deliberate simplification lemmas,
rather than opaque typeclass-indexed abbreviations.

Milestone 2G establishes the same proof shape for a genuinely branching
signature.  The Boolean-cotree descriptor has nullary bottom and leaf shapes
and a node whose position type is `bool`.  Registering only bottom decidability
and finite positions again selects the generic wrapper `aCPO` directly.  The
experiment's inclusion and ideal equations compute as the expected tree
operations.

The reusable indexed `tfold` node rule assembles the two child suprema
pointwise with `supremum_apply` and transports the resulting function-space
supremum through a `wcontinuous` node algebra.  Consequently, the public
`cotree_map_node` proof supplies only continuity of `conode`; its statement and
proof contain no generic representation details.  This answers the main
branching ergonomics question positively.

The internal proof exposed two API details.  Nested child simplification can
reveal `value_ideal` before a specialized ideal rewrite, so the specialization
layer needs deliberate projection/simplification lemmas.  Coq also made the node
algebra implicit until an explicit `Arguments` declaration restored a useful
call shape.  These are manageable and local, but AlgCo 2 should treat
elaboration behavior as part of the generated specialization interface.

The experiment's remaining cost is volume rather than client ergonomics.  Raw
native conversions, inverse proofs, and order correspondences are structurally
similar across colists and cotrees.  This is evidence against a dual
representation in a clean-slate design.  Containers are validated as a
semantic backend; any frontend should be judged by whether it provides concise
constructors and proof principles over that one representation.

Milestone 2H sharpens that conclusion.  Native conversions, coinductive round
trips, and native order correspondence are unavoidable if independently
declared native datatypes are retained.  AlgCo 2 should avoid creating those
obligations in the first place.  Descriptor capabilities and the duplicated
shifted-supremum proofs are genuinely generic and belong in the container
backend.

Milestone 2H proposed a pointed polynomial grammar generated by
constants, finite indexed families of recursive occurrences, sums, and
products.  A pointed code adds a canonical outer `1`.  The prototype
interpreted it as semantic bottom; under the refined design it is more cleanly
understood as the hole introduced by `Lift`.  The code is compiled
transparently to the existing container representation:

```text
ColistCode A = P (K A × R)
CotreeCode A = P (K A + Rᶠ bool)
```

With the refined reading, the first code is the partial completion of total
streams.  A partial colist with exact termination instead applies `P` to
`K unit + (K A × R)`.  The cotree code already contains its returned leaf
alternative, so its outer `P` is directly the fresh partial hole.

The finite-recursion primitive is intentionally narrower than an arbitrary
`Πᶠ i. D i`.  It compiles to one shape with positions `I`; a general product
of coded fields would instead introduce function-valued shapes and an
unnecessary extensional-equality problem even for the Boolean node.

Milestone 2J subsequently tests a smaller alternative: apply those
constructors directly in the container algebra while carrying
finite-position evidence compositionally.  The displayed grammar remains a
useful notation and comparison point, but no longer motivates an AST by
itself.

Milestone 2H proposed a separate `NativePresentation` to package basis/value
conversions, round trips, order correspondence, and approximation commuting
laws.  Milestone 2K implements and evaluates that proposal.  It should be read
as a controlled experiment in the cost of dual representations, not as a
component AlgCo 2 is committed to retain.

Milestone 2I confirms the generic fold boundary.  A single
`value_fold_layer` theorem now contains the shifted-supremum and pointwise
child-supremum argument used by both colist cons and cotree node.  Separate
weaker rules handle the designated bottom and nonbottom nullary shapes, so a
leaf theorem does not acquire global continuity obligations for unrelated
constructors.  The public `comap` and `cotree_map` proofs retain their native
statements and continuity-only obligations.

The generic theorem introduces no new axiom.  It inherits dependent equality,
classical logic, and constructive indefinite description from the current
indexed algebraic CPO.  Functional extensionality appears only when the
Boolean-cotree specialization equates the generic fold with native `tfold`'s
function-valued node result.

There is one important API coupling in that result.  The current
`value_fold` and its equations require `FinitePositions S` because
`value_fold` is defined using `co` over a full `aCPO (Value S)`, and the
current algebraic-CPO construction uses finite branching to establish
compactness of its basis.  The layer proof itself does not enumerate
positions or merge finitely many child witnesses: it uses the canonical
truncation chains and their layer-shift law, pointwise suprema, and weak
continuity of the algebra.  It does not use compactness or the reconstruction
field of `aCPO`.  A useful weaker sequential presentation would normally keep
reconstruction to justify the sequence as a presentation of each value, but
need not demand compact approximants.  Finiteness should therefore not yet be
treated as an intrinsic assumption of the fold equation.  A future experiment
should factor such an interface from `aCPO` and test the same theorem on an
infinitely branching signature.  The direct-combinator experiment remains
finitary, so this generalization need not block it.

Milestone 2J confirms that explicit syntax is unnecessary for the structural
capabilities considered so far.  A `finitary_container` bundles an ordinary
container with complete position enumerations; direct constant, recursive,
sum, and product combinators preserve that bundle.  `finitary_point` adds the
canonical nullary point—now understood as `Lift`'s hole—and a generic indexed
bridge supplies `DecidableBottom` and `FinitePositions`.  Because the
evidence-bearing bundle
remains in the descriptor head, both instances resolve for composed colist
and Boolean-cotree folds without per-datatype registrations.

The direct encoding has only minor local costs.  Product positions are
coproducts, so the composed colist tail uses an injection that should be hidden
behind a named position.  Generic fold theorem applications still name the
descriptor explicitly when starting from a projected shape.  Neither issue is
improved merely by putting the same constructors behind an interpretation
function.

An explicit code's remaining distinctive feature is reification: later code
can induct over how the signature was assembled.  AlgCo 2 should demand a
concrete use for that feature before adding another representation.  The
partial-completion experiment should first construct `Lift C` directly from
containers and finite-position evidence; only a demonstrated need to
distinguish constant, sum, product, and recursive syntax would justify
restoring the code frontend.

Milestone 2K confirms that the proposed native-presentation boundary is
technically coherent, with one important internal refinement: basis and value
presentations must not be one proof record.  `NativeBasisPresentation` and
`NativeValuePresentation` separately package two conversions, a native round
trip up to preorder equivalence, and generic/native order correspondence.  The
split preserves assumption locality when a function-branching basis conversion
uses functional extensionality but the value-order argument does not.

An additional `NativeApproximation` layer contains native inclusion and
truncation together with exact commuting equations.  Exact equality is useful
for native rewrite rules, but it is a stronger and occasionally more
axiom-dependent boundary than order equivalence.  Separating it prevents those
assumptions from contaminating conversion continuity.  The generic order layer
derives both-direction monotonicity, mixed below laws, arbitrary-supremum
preservation, sequence continuity, and Scott-compactness transport.  The exact
layer derives native truncation chains and compact native inclusions.

During Milestone 2K, the colist and Boolean-cotree comparison modules consumed
these derived monotonicity and continuity facts without changing their native
definitions or constructor proofs.  The old and new value-continuity results
had identical assumption profiles: only dependent equality, with no functional
or native coinductive extensionality.  Functional extensionality remained
localized to exact branching-basis and operation results where function
equality was actually used.  Milestone 2L subsequently removed this
experimental presentation layer.

The clean-slate conclusion is negative: the presentation layer solves a
problem created by choosing two representations.  Its generic module is
substantial, and each instance still needs conversions, round trips, order
correspondence, and exact commuting laws.  Factoring the wrapper order theory
once does not justify retaining that boundary when AlgCo 2 has no compatibility
obligation.

Consequently, `NativeBasisPresentation`, `NativeValuePresentation`, and
`NativeApproximation` are experimental evidence, not proposed AlgCo 2
infrastructure.  Milestone 2L confirms that `Basis S` and `Value S` directly
support specialized names and proof principles with the desired low-friction
experience.  The presentation modules have therefore been removed rather than
carried as dormant adapters; their implementation remains available in Git
commit `038393d` as experimental evidence.

That conclusion concerns the canonical representation of a given fixed point,
not the placement of the approximation hole.  Milestone 2L's descriptor `S`
is already pointed.  Under the refined design its `Basis S` and `Value S`
prototype `FinitePartial C` and `Partial C` for `S = Lift C`.  The unlifted
`Semantic C = ν C` has a different intrinsic role; it is not a native wrapper,
conversion target, or compatibility representation of the partial domain.

Milestone 2L also identifies one genuine container-specific cost.  A layer's
children are represented by a function `position s → μ C`; in intensional Coq,
arbitrary functions out of empty or singleton position types are not equal by
computation to the canonical functions used by named constructors.  The
specialized colist and cotree induction principles therefore use functional
extensionality internally.  The generic structural induction theorem is
constructive, and client proofs see only the familiar constructor cases.
Direct coinductive map continuity and equations do not inherit functional or
native coinductive extensionality.

This localized axiom does not outweigh the removal of the entire conversion
boundary, but it is now a concrete comparison criterion for functor codes.  A
direct sum/product interpretation would be preferable if it removes the ghost
function equality while retaining accepted positivity, instance resolution,
and client proof ergonomics.  Reification still lacks an independent use, so
the semantic/partial split should first be attempted directly over containers.

## Provisional decisions

1. Do not replace sequential approximation with arbitrary directed sets.
   Provide standard directed semantics and retain the canonical sequence as
   additional computational presentation.
2. Use universe-polymorphic indexed families as the working representation,
   and require their index type to be inhabited explicitly.
3. Do not claim that a classically selected semantic supremum is executable.
4. Do not require a semantic recursive signature `C` to contain an
   approximation bottom.  `Semantic C = ν C` may be only a final coalgebra (or
   setoid), rather than the algebraic CPO on which AlgCo extensions operate.
5. Derive the partial descriptor `Lift C` by adding a fresh nullary hole, and
   put the canonical algebraic structure on `Partial C = ν (Lift C)` with
   compact basis `FinitePartial C = μ (Lift C)`.
6. Keep intrinsic semantic orders and the partial approximation order
   distinct.  If a semantic type genuinely has a least value, its returned
   image remains distinct from `pending`.
7. Treat `Semantic C` and `Partial C` as two intrinsically different roles,
   not as generic/native duplicate representations or a compatibility layer.
8. Do not expect Coq to infer a pointed/finitary descriptor from its projected
   carrier type.
9. Use descriptor-indexed generic fixed points as the canonical carriers for
   each role; common signatures may expose transparent aliases and named proof
   principles, but not independently declared native copies.
10. Reserve `Dense` for a law-bearing notion; use `Approx` as the working short
   name for raw inclusion and approximation data.
11. Retain a stable pointed descriptor in generic `Basis S` and `Value S` type
    heads, normally with `S = Lift C`, while keying optional decidability and
    finiteness capabilities by `S` rather than putting them in the carrier
    index.
12. Prove the fold/cofold layer equation once over the container backend, then
   expose thin descriptor-specific corollaries over the same carriers.
13. Retain containers as the working backend for linear and finite branching
    signatures; judge functor codes by how much specialization boilerplate they
    derive, not by a need to repair client proof ergonomics.
14. Treat simplification lemmas and explicit argument declarations as part of
    a descriptor specialization's supported interface.
15. Prefer evidence-preserving container combinators to a reified
    pointed-polynomial code; introduce syntax only if a later transformation
    demonstrably requires induction over signature construction.
16. Do not independently declare generic and native carriers for the same
    AlgCo 2 type.  The Milestone 2K presentation obligations are costs to avoid,
    not an API to standardize.
17. Avoid heavy declaration-generating metaprogramming in the first frontend;
    first measure what remains after generic fixed-point proofs are factored.
18. Provide separate hole and returned-nullary fold rules alongside the
    general recursive layer theorem, so constructor-local proofs do not inherit
    irrelevant global algebra obligations or conflate `pending` with `nil`.
19. Treat `FinitePositions` on the current value-fold equations as coupling to
    the full `aCPO`/`co` interface, not as a proved semantic necessity; test a
    weaker sequential-extension interface separately after the current
    finitary experiments.
20. Use the Boolean-event interaction trees from `zar` as a required vertical
    slice for cotree-style reasoning, including `Tau`/`eutt` laws.
21. Treat the native-presentation implementation as a completed cost
    experiment, preserved in notes and Git history but removed from the active
    design.  Do not restore it unless a new intrinsic requirement independently
    forces a second representation.
22. Do not preserve historical names, wrappers, theorem statements, module
    structure, or runtime representations for compatibility.
23. Judge AlgCo 2 against AlgCo's purpose and benefits—especially low-friction
    structural proofs over compact bases—not against source-level migration or
    API equivalence.

These are working design decisions; backward compatibility is deliberately
excluded from them.

## Open questions

- Should a future `DCPO` interface bundle the inhabited index type, family,
  and directedness proof, or retain the premise-oriented API that worked for
  the compactness theorem?
- Should semantic orders remain preorders with explicit equivalence, or should
  the new kernel use partial orders or setoid quotients?
- Does `Semantic C` need any generic order structure, or should only
  `Partial C` carry the approximation CPO unless a semantic order is supplied
  independently?
- Should `Semantic C` be represented directly as `ν C`, or as the total
  subtype of `Partial C` when that gives better Coq and extraction ergonomics?
  In either case the two must be proved equivalent, not silently identified.
- Can full `DCPO (Partial C)` be constructed without making the
  universe-polymorphic API unpleasant or suggesting that its selected suprema
  are executable?
- Can totality be shown to characterize exactly the image of
  `embed : Semantic C → Partial C` without an awkward choice or quotient
  principle?
- Does constructing `Lift C` genuinely need a reified polynomial descriptor,
  or do the validated container combinators suffice?
- Should computational capabilities such as bottom-shape decisions and
  position enumerations be canonical fields, uniquely registered classes, or
  explicit construction parameters?
- What is the cleanest division of monotonicity, continuity, density, and
  compact-basis laws between `Approx`, `Dense`, and the algebraic structure?
- Which structure should contain ordered nonrecursive payload fields?
- How much of the semantic layer can remain constructive if operational
  productivity is treated separately?
- Can a direct sum/product fixed-point interpretation remove the functional
  extensionality needed to canonicalize empty and singleton container-child
  functions without making positivity or specialization ergonomics worse?
- What is the weakest sequential-presentation interface sufficient to define
  `value_fold` and prove its layer equation without importing compactness of
  the basis, and does it support a useful infinitely branching example?
- For interaction trees with infinite response types, should AlgCo 2 restrict
  the algebraic interface to finitary events or replace full visible nodes by
  finitely supported observations?
- Should `eutt` remain a relation respected by operations over the raw final
  coalgebra, or should some semantic layer quotient weak `Tau` behavior?

## Next experiments

Milestone 2M's carrier split and colist embedding now pass.  The remaining
experiments are:

1. Define generic realization and totality on the lifted carrier.  Prove that
   embeddings are realized and total, that realization is downward closed,
   and that exact `returned_nil` is total.
2. Define colist requests and coverage, keeping totality distinct from
   “produces at least `k` cons cells,” and prove evaluator-stage soundness
   separately from monotonicity.
3. Compare direct `ν C` semantic values with the total subtype of `Partial C`
   before fixing the final public representation.
4. Repeat the observation account for Boolean cotrees, where a request is a
   finite prefix-closed frontier rather than merely a scalar depth.
5. Instantiate the event container for `zar`'s Boolean interaction trees and
   reproduce one continuous-WP proof by structural induction over the partial
   basis, including the relevant `Tau`/`eutt` compatibility.
6. Use the interaction-tree slice to expose the precise finitary-event
   boundary and to decide whether lifting needs reified signature syntax.
7. Reconsider a direct sum/product backend or extraction-specific
   representation only after these semantic tests reveal an intrinsic need;
   neither may create a compatibility API.
