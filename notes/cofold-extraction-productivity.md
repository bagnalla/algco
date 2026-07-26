# Operational productivity of extracted `cofold`

## Status

The original working notes behind this unfinished idea have now been recovered
from `/mnt/c/Users/nubin/Dropbox/notes/reals.txt`, last modified May 16, 2023.
They propose a semantic notion of productivity stated using compact input
approximations, strict output progress, and maximal output values. The original
proposal has not been formalized verbatim, and several side conditions were
left implicit. A corrected observation-indexed replacement has now been
formalized in [`theories/productivity.v`](../theories/productivity.v). A
verbatim copy of the recovered passage is preserved in the appendix below.

The recovered definition identifies an important direction, but arbitrary
strict output progress is not by itself a characterization of totality. A
strictly increasing chain can keep refining some observations while starving
another forever. The relevant sufficient condition in the Coq artifact of the
probable source paper uses a stronger, observation-directed relation that
resolves the next missing finite prefix. This distinction was not explicit in
the original notes.

The likely complete solution therefore combines an observation-indexed notion
of totality with a separate operational interpretation of the selected
extraction equation. Maximality can be recovered as a derived characterization
for domains in which maximal elements really are the fully observed values;
it cannot play that role uniformly because AlgCo also uses non-operational
orders such as implication on `Prop` and `false ⊑ true` on `bool`. A final
correctness result must separately establish semantic soundness, operational
adequacy, and productivity of the extracted computation.

The first operational regression model is now formalized in
[`theories/cofold_operational.v`](../theories/cofold_operational.v). Its generic
flat layer uses `option B` to distinguish a pending computation from an
atomically returned result. A demand-aware lifted step may return without
inspecting its recursive approximation. A logical-relation theorem proves
that every finite operational result agrees with the AlgCo denotation, and
monotonicity of the lifted step makes the fuel approximations an increasing
flat chain.

The `colist_existsb` instance distinguishes a pending computation from a
returned `false` and models the lazy demand behavior of Boolean disjunction.
Its inductive big-step semantics is equivalent to returning at some finite
fuel. The development proves the central counterexample: `bad_bool` denotes
`false`, while neither the fuelled evaluator nor the big-step semantics returns
any Boolean. This initial model still treats colist constructors and predicate
applications as atomic and terminating. Observation-indexed coinductive
results and an adequacy connection to an independently formalized target
language remain open.

## The present development

The denotational definition is

```coq
Definition cofold {A B} `{o: PType B} (f : A -> B -> B) : colist A -> B :=
  co (fold ⊥ f).
```

It is defined by taking the supremum of results on finite approximations of a
colist. Under continuity hypotheses, Coq proves the expected equations for
`conil` and `cocons`. See
[`theories/colist.v`](../theories/colist.v#L1215).

Extraction replaces this denotational construction with direct lazy recursion:

```haskell
\o p f l ->
  case l of
    Conil       -> bot o p
    Cocons a l' -> f a (cofold o p f l')
```

The accompanying comment says this is safe for productive colists, meaning
colists with no occurrence of `conil`; see
[`theories/colist.v`](../theories/colist.v#L1262). That condition ensures an
infinite constructor spine in Coq. It does not ensure that computing each
constructor payload, or any other observation demanded by `f`, terminates in
the extracted program.

The sieve application proves denotational/structural productivity in
[`theories/sieve.v`](../theories/sieve.v#L289) and then extracts a `cofold`
whose step emits one constructor before its recursive result is used; see
[`theories/sieve.v`](../theories/sieve.v#L426). This makes the outer shape
promising, but it is not yet an operational productivity proof for all work
performed beneath that constructor, notably filtering to find later elements.

## The counterexample and what it rules out

The development already contains the decisive counterexample:

```coq
Definition colist_existsb {A} (P : A -> bool) : colist A -> bool :=
  cofold (fun a x => P a || x).

Definition bad_bool : bool :=
  colist_existsb (const false) (nats O).

CoFixpoint bad_stream : colist bool :=
  cocons bad_bool bad_stream.
```

Coq proves both

```coq
productive bad_stream
bad_stream = const_colist false
```

in [`theories/colist.v`](../theories/colist.v#L1835). Nevertheless, evaluating
the first payload after extraction demands

```haskell
False || False || False || ...
```

and diverges.

This shows something stronger than merely “the current productivity predicate
is too weak.” Since `bad_stream` and `const_colist false` are equal in Coq, **no
extensional predicate on the final Coq value can distinguish them**. The desired
condition must refer to the implementation/equation being extracted, its
evaluation approximations, or intensional evidence retained alongside the
value.

## The missing distinction: two bottoms

AlgCo's `⊥` is the least element of the mathematical result domain. It can be
an ordinary, completely evaluated value. For example, `false` is the bottom of
the Boolean information order used here.

Lazy Haskell has an additional bottom: nontermination or failure to produce an
observable value. Operationally,

```text
⊥H < False
⊥H < True
```

whereas AlgCo's Boolean order has `false` itself as its least semantic value.
The current Coq model therefore identifies a defined semantic bottom with a
computation that never returns. That identification is harmless for the
denotational equations but insufficient for justifying extraction.

The reconstructed solution is to lift the result domain with a fresh bottom,
for example:

```coq
option B
```

with the intended meanings

```text
None     = no operational result has been produced
Some ⊥B  = the computation returned AlgCo's defined semantic bottom
Some b   = the computation returned b
```

For nested or coinductive result types, this lifting must occur recursively at
observable positions. A single `option (colist A)` only records whether the
outer computation returns; it does not record whether later constructors or
their payloads are defined.

## One order is currently doing several jobs

The deeper issue is not just the absence of one additional bottom. AlgCo's
`OType` interface allows one preorder to be used for several mathematically
distinct purposes:

| Kind of order | AlgCo example | Intended meaning |
| --- | --- | --- |
| Semantic or logical refinement | `false ⊑ true`; `P ⊑ Q` means `P -> Q` | Increasing truth, entailment, or other domain-specific information |
| Codata observation | A finite colist prefix is below a longer prefix | Increasing observable structure |
| Operational definedness | Divergence is below a returned value | Increasing evaluation progress |

The first two orders are useful in the existing denotational mathematics. A
CPO is an order-theoretic structure and its order need not be an operational
approximation relation. The problem arises only when continuity or convergence
in one of those semantic orders is taken to imply progress of an extracted
program.

`colist` makes the distinction especially visible. Its `conil` constructor is
both the least prefix approximation and, according to the source comment,
“bottom / divergence.” After extraction, however, `Conil` is an ordinary
returned Haskell constructor, distinct from divergence before a constructor is
produced. Treating finite words as compact approximations to infinite words is
perfectly coherent denotationally; relating that representation to a lazy
target language requires the extra operational distinction.

In particular, maximality in AlgCo's current Boolean or proposition order does
**not** characterize termination:

```text
false ⊑ true
False ⊑ P ⊑ True
```

Only `true` or `True` is maximal, but a computation that returns `false`—or
returns `False` as a proposition-valued semantic result—has still returned.
Consequently, the word
“maximal” in this report must always be read in one of two ways:

1. maximal with respect to a separate, flat operational order in which every
   returned base value is maximal; or
2. shorthand for a type-indexed convergence/totality predicate, if the lifted
   computation domain retains AlgCo's non-discrete semantic order.

The second formulation is more general. If `return false ⊑ return true` is
preserved in the computation domain, both computations should be classified as
convergent even though only one is maximal.

## The recovered compact-basis proposal

The original notes define a function `f : A -> B` to be productive on an input
`x` when every compact approximation of `x` either already produces a maximal
output or can be finitely refined so that the output strictly improves. In a
form adapted to AlgCo's preorders, the intended definition appears to be:

```text
CompactProgress f x :=
  forall b,
    compact b -> b ⊑ x ->
      maximal (f b) \/
      exists b',
        compact b' /\
        b ⊑ b' /\ b' ⊑ x /\
        f b ⊏ f b'.
```

For a preorder, `maximal y` should mean

```text
forall z, y ⊑ z -> z ⊑ y
```

rather than literal equality. The original notes omitted the condition
`b' ⊑ x`; it is essential, because progress must follow refinements compatible
with the particular input `x`, not some unrelated branch of the domain.

### Why arbitrary strict progress is insufficient

The implication suggested by the notes can be proved if the codomain really
satisfies the stated `CPO+` axiom: every ascending, non-stabilizing sequence has
a maximal supremum. The difficulty is that this is a very strong property, and
the motivating pointwise domain of partial streams does not satisfy it.

For example, consider streams over flat `option A`. Let `q n` define the first
`n` even-numbered positions while leaving every odd-numbered position `None`.
Then `q` is increasing and strictly improves at every step, but its supremum
still contains `None` at every odd position and is therefore not maximal. The
chain makes infinitely much progress without serving the finite request to
observe position `1`.

The distinction can be summarized as:

```text
recurring strict growth
  does not imply
every finite observation eventually appears
  which, for finite observations, is equivalent to
a fully defined supremum.
```

If a chain is already known to have a fully defined supremum, then every finite
observation must occur at a finite stage, provided observations are
Scott-open. In particular, a pointwise stream whose supremum contains
`Some a` at position `i` must contain that value at position `i` in some finite
approximant. The counterexample concerns the attempted derivation of a fully
defined supremum from strict growth alone.

The accompanying Coq artifact of Rusu and Nowak's paper avoids arbitrary
strictness. For streams it defines a special `lts` relation with two cases:

```text
None :: s   lts   Some a :: s

s1 lts s2
-----------------------------
Some a :: s1   lts   Some a :: s2
```

Thus a step passes through an already-defined prefix and resolves the next
hole. Its key lemma says that if the source stream is defined through depth
`n`, an `lts` step makes the target defined through depth `n + 1`. A recurrence
hypothesis requiring such steps arbitrarily far along the approximation chain
therefore proves every finite prefix defined. This is a frontier-progress or
fairness property, not merely the strict part of the pointwise order.

There is a second obstacle to formalizing the recovered statement directly
against AlgCo's current interfaces. The definition of `compact` in
[`theories/aCPO.v`](../theories/aCPO.v#L34) says that a chain whose supremum is
exactly `x` must eventually reach `x`. It is not the usual way-below condition

```text
x ⊑ sup q -> exists n, x ⊑ q n,
```

and does not by itself supply the cofinality of arbitrary compact elements
used by the proposed converse. AlgCo does, however, already provide the
canonical approximation chain `incl ∘ ideal x`. The first formalization
should use that chain and finite observations directly. A later development
could add a separate way-below/cofinal-basis interface and recover an
arbitrary-basis version of the original conjecture.

The original conjecture relating productivity to “maps maximal to maximal”
also needs a qualification: it must quantify productivity only over maximal or
otherwise designated-total inputs. If productivity is required literally at
every partial input, it is stronger than maximal-element preservation. For
example, identity on the truth-ordered Booleans maps maximal `true` to itself,
but it cannot make progress within the fixed partial input `false`.

There is also a small typo in the recovered notes. Maximal-element preservation
should conclude that an extension `z` of `f x` is equivalent to `f x`; the
written expression `f z = z` is ill-typed for a general `f : A -> B`.

### What it says about `bool`

The recovered notes explicitly recognize that continuity has different
computational meanings for different orders. Under `false ⊑ true`, `false` is
treated as incomplete information and `true` as the only total answer. This is
the Sierpiński/semidecision interpretation of Booleans:

```text
false = no positive answer has been obtained yet
true  = a positive answer has been obtained
```

The compact-progress predicate therefore rejects both an infinite unsuccessful
existential search and a constant semantic-`false` function. That is coherent
for semidecision, but it is not the operational semantics of an ordinary
Haskell `Bool`, where both `False` and `True` are returned values.

This explains both the strength and the limitation of the original idea. It is
a semantic totality criterion *relative to a domain representation*. It cannot
turn an arbitrary AlgCo `OType` into an operational domain merely by calling
its maximal elements “computed values.”

## Observation-indexed totality

The more robust formulation asks whether every finite demand made by a
consumer is eventually answered. It distinguishes two indices:

```text
r   a finite observation request
n   evaluation fuel or approximation stage
```

Productivity has the characteristic quantifier order

```text
forall r, exists n, observation r is available after stage n.
```

The stage may depend on the request; no finite stage must contain an entire
infinite result.

### Observation systems

Schematically, associate an operational domain `D_A` with:

```text
Request_A             a type of finite requests
Observes_A r d         d answers request r
Total_A d              d is fully defined at type A
```

The basic laws are:

```text
upward closure:
  Observes_A r d -> d ⊑ d' -> Observes_A r d'

totality:
  Total_A d <-> forall r, Observes_A r d

finiteness / Scott openness:
  directed q -> supremum s q -> Observes_A r s ->
  exists n, Observes_A r (q n)
```

The last law says that a finite observation cannot become available only at an
infinite limit. For a directed approximation chain `q`, define coverage by

```text
Covers_A q := forall r, exists n, Observes_A r (q n).
```

If `s` is the supremum of `q`, upward closure and Scott openness give the
central equivalence:

```text
Covers_A q <-> Total_A s.
```

The forward direction sends each observation from a finite approximant to the
supremum. The reverse direction uses the finiteness of each observation to
find a stage at which it was already present.

For a continuous function `f : A -> D`, AlgCo's canonical chain gives the
specialization

```text
q_x n := f (incl (ideal x n)).
```

Continuity makes `f x` the supremum of `q_x`, so the desired basis-level
characterization becomes

```text
Total_D (f x)
  <->
forall r, exists n,
  Observes_D r (f (incl (ideal x n))).
```

This retains the recovered idea that finite input approximations must account
for the total output, but replaces undirected strict improvement with coverage
of every required observation.

### Examples of requests

For a scalar computation represented by a flat `option B`, there is one
request: return a value. It is observed by every `Some b` and not by `None`.
Coverage is ordinary termination:

```text
exists n b, q n = Some b.
```

For an infinite colist, request `k : nat` asks for the first `k` constructors.
Coverage says

```text
forall k, exists n,
  the first k constructors are available in q n,
```

which is the usual finite-observation formulation of productivity. For a tree,
requests can instead be finite paths or finite observation trees. This makes
fairness explicit: refining the left branch forever does not answer a request
on the right branch.

For mixed types, the observation relation is type-directed. Observing a codata
layer may require an outer constructor, a total payload, and enough access to
the suspended tail for subsequent requests. This makes explicit whether a
constructor with a divergent payload counts as an observation.

### Frontier progress as a sufficient proof principle

Direct coverage is the semantic specification. A frontier relation is a
convenient local way to prove it. For linearly observed streams, define

```text
FrontierStep d d'
```

to mean that `d'` resolves the next missing observation of `d`. It should
satisfy a rule such as

```text
Observes k d -> FrontierStep d d' -> Observes (S k) d'.
```

If an increasing approximation chain either reaches a total stage or takes
frontier steps arbitrarily far along the chain, induction on `k` proves
coverage. For branching types the step relation must be indexed by the
requested branch, or accompanied by a fairness argument. Arbitrary `d ⊑ d'`
or `d ⊏ d'` cannot supply that guarantee.

Maximality is now a possible theorem about a particular observation system:

```text
Total_A d <-> maximal d.
```

It holds for flat operational values and often for prefix domains. It is not
built into the definition, so a returned `false` can be total even when
`false` is nonmaximal in AlgCo's semantic Boolean order.

### Why the proposed `cofold` interface remained unfinished

The last recovered note proposes a subset type of productive functions and
making `cofold` accept only such functions. There are two opposing problems:

* Requiring a step function to satisfy compact progress on every partial
  recursive argument is too strong and can reject ordinary constructors whose
  tails are still partial.
* Requiring only that the step function map maximal arguments to maximal
  results is too weak: it does not ensure that least-fixed-point iteration or
  the selected recursive program ever reaches a maximal value.

The progress condition therefore has to be established for the concrete chain
generated by the `cofold` functional or by the extraction equation, not merely
for its step function in isolation. This is the likely point at which the
original formalization work remained unfinished.

## A candidate approximation semantics

For an inductive/scalar codomain, define a fuelled interpretation of the actual
extraction equation. Schematically:

```coq
run 0       f l             := None
run (S n)   f conil         := Some ⊥B
run (S n)   f (cocons a xs) := lift_f a (run n f xs)
```

`lift_f` is the operational lifting of `f`; it may sometimes return without
forcing its recursive argument. For Boolean disjunction, for example,
`true || _` can produce `Some true`, while `false || x` must inspect `x`.

The successive `run n f l` values should form an increasing chain in an
operational approximation order. Extraction termination can always be stated
directly as:

```text
exists n b, run n f l = Some b
```

If the `option` lifting uses the *flat operational order*

```text
None ⊑ Some b
Some a and Some b are incomparable when a <> b
```

then this is also equivalent, for a scalar result, to:

```text
the supremum of the approximation chain is maximal (fully defined)
```

It is not in general equivalent if `Some` preserves AlgCo's semantic order on
`B`. In that case convergence should be expressed as membership in the image
of `Some`/`return`, with a separate recursive totality predicate for structured
values.

For a coinductive result, replace whole-value termination by finite
observability:

```text
for every finite observation depth k,
there exists finite evaluation fuel n that defines the observation to depth k
```

Thus the type of the result determines the obligation:

| Result shape | Operational requirement |
| --- | --- |
| Inductive/scalar | The computation eventually returns a total value. |
| Coinductive | Every finite observation is available after finite work. |
| Mixed inductive/coinductive | Apply termination and productivity recursively according to the type structure. |

Under this semantics, every finite approximation of `bad_bool` remains
`None`: its disjunction always needs one more recursive result. Its limit is
operationally undefined, so `bad_bool` and consequently the payloads of
`bad_stream` fail the new criterion. In contrast, a successful existential
search with a witness at a finite position can return without evaluating the
infinite remainder.

The difference between the semantic and operational approximation chains is
worth making explicit. Before finding a witness, a denotational existential
fold may return the semantic approximation `false`; an evaluator cannot return
`false` yet, because a later witness may change the answer:

```text
infinite input with no witness:
  semantic      false, false, false, ...
  operational   None,  None,  None,  ...

input with a witness at a finite position:
  semantic      false, ..., false, true, true, ...
  operational   None,  ..., None,  Some true, ...

finite input with no witness:
  operational   None, ..., None, Some false
```

Thus the denotational prefix folds cannot themselves serve as a fuelled
operational semantics.

## Soundness, adequacy, and productivity

The word *adequacy* must be used carefully because there are three objects in
play:

```text
the actual extracted target-language expression e
the formal operational approximants run n e
the existing AlgCo denotation v
```

They require two different connections. First, finite semantic soundness says

```text
if run n e produces observation r with answer a,
then v gives answer a to observation r.
```

This is partial correctness. It does not say that evaluation produces any
observation. In particular, it can hold vacuously for a divergent computation.

Second, computational adequacy connects the formal operational model to
actual target evaluation:

```text
e evaluates far enough to produce observation r with answer a
  <->
exists n, run n e produces observation r with answer a.
```

At a flat scalar type this reduces to the familiar statement that a program
terminates exactly when its operational denotation is not the fresh
operational bottom. At a coinductive type it is an observation-by-observation
equivalence rather than whole-value termination.

Productivity or totality is the additional liveness assertion

```text
forall finite requests r,
  exists n a, run n e produces r with answer a.
```

Combining operational adequacy, semantic soundness, and totality establishes
that the target program produces every required finite observation and that
all of those observations agree with `v`.

The existing AlgCo denotation cannot be computationally adequate for arbitrary
extracted implementations by itself. A literal `false` and `bad_bool` have the
same AlgCo value, while one target computation returns and the other diverges.
A richer operational object `d` must retain that distinction, together with a
realizability relation

```text
R_A d v
```

saying that every observation produced by `d` agrees with `v`. Divergence may
realize a semantic value vacuously, so the separate condition `Total_A d` is
essential.

Finally, `Extract Constant` inserts an opaque target-language string that Coq
does not inspect. Within this development one can prove the above properties
for a formal evaluator or operational relation matching that string. A fully
end-to-end adequacy result for the generated Haskell would additionally need a
formal target-language semantics and a verified connection to extraction.
Without that machinery, the theorem is conditional on the inserted Haskell
equation faithfully implementing the formalized operational relation.

## A value/computation formulation

A Moggi-style separation gives a natural home to the operational layer:

```text
A       values that have already been produced
T A     computations that may eventually produce an A

return : A -> T A
bind   : T A -> (A -> T B) -> T B
```

Here `A` can retain AlgCo's semantic preorder. `T` adds partiality without
requiring the least semantic value of `A` to represent nontermination. This is
the role of a partiality/lifting monad in
[*Notions of Computation and
Monads*](https://person.dibris.unige.it/moggi-eugenio/ftp/ic91.pdf).

One concrete intensional presentation is Capretta's delay monad:

```text
now   : A -> Delay A
later : Delay A -> Delay A
```

An infinite sequence of `later`s diverges. See
[*General Recursion via Coinductive
Types*](https://arxiv.org/abs/cs/0505037). If finite differences in the number
of steps should be ignored, the quotient/equality of the delay construction
requires some care; see
[*Partiality, Revisited*](https://arxiv.org/abs/1610.09254).

Convergence can then be a relation

```text
c ⇓ a
```

rather than maximality in a combined order. This lets both `return false` and
`return true` converge while retaining `false ⊑ true` as a separate semantic
fact.

### The operational translation must be type-directed

A uniform outer `T A` is sufficient only for scalar results. In a lazy
language, a constructor or lambda can be produced while computations beneath
it still diverge:

```haskell
Cocons undefined tail
\x -> undefined
```

The first expression has an outer constructor but an undefined payload; the
second is a defined function value whose application diverges. Therefore the
placement of computations must follow the type structure and evaluation
strategy. Schematically:

```text
Op Bool       = T Bool
Op (A * B)    = T (Op A * Op B)       -- placement depends on field strictness
Op (A -> B)   = T (Val A -> Op B)
```

Call-by-push-value makes precisely this distinction between value and
computation types, with explicit operations for returning and thunking
computations; see
[*Call-By-Push-Value*](https://link.springer.com/book/10.1007/978-94-007-0954-6).

### Coinductive values still fit the split

Let one colist layer be

```text
Layer A X = 1 + A * X.
```

A possibly partial operational producer can be represented by a coalgebra

```text
step : S -> T (Layer A S)
```

or, when the relevant final coalgebra exists, schematically as

```text
CoList_op A = ν X. T (Layer A X).
```

Observing the codata runs one computation. It may diverge before revealing a
layer, return an end marker, or return a constructor and a new state. For lazy
payloads, the payload position must itself use the operational interpretation
of `A`.

Productivity is then a coinductive convergence condition. For an infinite
stream it has the form

```text
Productive s :=
  step s ⇓ Cons (a, s') /\ Total_A a /\ Productive s'.
```

For a genuinely finite-or-infinite list, a convergent end marker would also be
total. For AlgCo's productive colists, the end-marker case is excluded because
finite prefixes represent incomplete observations.

This shows that a value/computation split does not prevent an encoding of
coinductive types. A codata value can be understood as a stable handle to an
indefinite sequence of suspended computations. What must be proved is that
each demanded observation converges.

### Relation to compact bases

The compact-basis account is a compatible but different presentation. In an
algebraic domain of partial infinite trees or streams:

* finite partial observations form a compact basis;
* an infinite value is the directed ideal generated by those observations;
* evaluation progressively produces compact observations; and
* a totality predicate selects observations with no operational holes.

The computation type `T A` need not itself be the compact basis. Rather,
iterating the coalgebra produces the finite observations that form the basis of
the coinductive behaviour. The monad explains failure to produce the next
observation; the algebraic domain explains reconstruction of an infinite value
from all finite observations.

### A non-domain-theoretic alternative

Guarded recursion separates productivity from both semantic refinement and
partiality by introducing a temporal modality:

```text
Stream A = A * ▷ Stream A.
```

The recursive occurrence must be available “later,” so productivity follows
from typing. Clock quantification can recover ordinary coinductive types. See
[*Guarded Dependent Type Theory with Coinductive
Types*](https://arxiv.org/abs/1601.01586). A partiality monad can remain
orthogonal: `▷` accounts for productive temporal progress, while `T` accounts
for possible divergence. This is conceptually clean but would be a much larger
change to AlgCo than adding an operational adequacy layer.

## Sources of the recovered idea and its operational completion

The recovered compact/maximal terminology makes Rusu and Nowak the probable
primary source. A second paper supplies the separate observation that the
actual equations chosen for extraction require their own check.

### Primary source: productive convergence via maximal approximations

[*Defining Corecursive Functions in Coq Using
Approximations*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol222-ecoop2022/LIPIcs.ECOOP.2022.12/LIPIcs.ECOOP.2022.12.pdf)
(ECOOP 2022) defines a sequence of approximants to converge *productively* when
it is increasing and its limit is maximal in the codomain CPO. More
specifically, its `CPO+` condition says that every ascending sequence has a
maximal limit, and its main sufficient condition says that approximants must
either reach a maximal value or make strict progress arbitrarily far along the
sequence. This is nearly exactly the pattern generalized in the recovered
notes from iteration indices to compact refinements of an input. Its stream
model uses `option A`: `None` records an undefined element, and maximal streams
contain no `None` values.

That is the likely source of the fresh-bottom/maximality formulation above,
but its generic strict-progress argument must not be transferred without
checking the `CPO+` premise. Pointwise streams over `option A` admit the
even-position counterexample described above, so recurring strict growth alone
does not force a maximal limit in that domain.

The accompanying
[*Coq artifact*](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.8.2.2)
does not use the strict part of the pointwise stream order for its key
productivity proof. It defines the stronger `lts` relation that passes through
an already-defined prefix and replaces the next `None` by `Some a`. The
`defined_upto_lts_mono` lemma proves that this advances definedness by one
position, and the functional hypothesis `F_prod` requires such advances
arbitrarily far along the iteration sequence. The formal result is therefore
an observation-directed frontier argument.

The paper also says that its general definition of productive convergence was
not formalized directly in the accompanying development. The difference
between the broad paper condition and the specialized artifact likely explains
both the recovered idea and why its direct AlgCo generalization was never
completed.

Maximality still transfers cleanly when the relevant order is an operational
information order whose returned values are total/maximal. For an AlgCo result
type with a non-discrete semantic order, the analogous condition must instead
use a separate operational order or an explicit observation-indexed totality
predicate.

### Operational complement: recheck extraction equations

[*Friends with Benefits: Implementing Corecursion in Foundational Proof
Assistants*](https://eprints.whiterose.ac.uk/id/eprint/191511/1/amico.pdf)
(ESOP 2017) addresses the remaining extraction issue directly.

Its “Certified Lazy Programming” discussion notes that arbitrary proved
equations chosen for code generation can destroy termination or productivity,
even when the equations are extensionally valid in the logic. It proposes
(re)checking productivity and termination on the equations actually used for
extraction. Its framework distinguishes recursive calls, which require a
well-founded decrease, from corecursive calls, which require constructor
progress. “Friendly” operations are those permitted around corecursive calls
because they preserve productivity.

This diagnoses why the recovered semantic predicate is not by itself an
extraction theorem. The missing obligation belongs to the hand-written
`Extract Constant cofold` equation and the functions instantiated into it, not
only to the extensional Coq denotation.

The complete reconstruction is therefore a combination:

1. formalize observation coverage and frontier progress for finite requests;
2. instantiate them in a separate, type-directed operational interpretation;
3. prove finite semantic soundness against the existing AlgCo denotation; and
4. connect the formal approximants to the **actual extraction equation**, as
   required by the certified-lazy-programming analysis.

### A more general type-directed account

[*Totality for Mixed Inductive and Coinductive
Types*](https://arxiv.org/abs/1901.07820) provides a broader semantic model for
programs with arbitrary recursion and nested inductive/coinductive types. Its
parity-based totality criterion captures why an infinite productive outer spine
does not excuse divergent inductive payloads. It is a useful model if the goal
is a generic checker rather than a theorem specialized to `cofold`, although it
is a less direct match to the AlgCo development and may not be the paper
originally remembered.

## Proposed formalization

A reasonably incremental formalization would separate six results.

### 1. Observation coverage and frontier progress

Add a small observation-indexed kernel, initially parameterized rather than
built into `OType`. Define finite requests, `Observes`, `Total`, and `Covers`,
then prove that for a directed chain with supremum `s`:

```text
Covers q <-> Total s.
```

The reverse implication assumes that each observation is Scott-open. Derive
the specialization to AlgCo's canonical chain

```text
fun n => f (incl (ideal x n))
```

for continuous `f`. Define a separate frontier-step relation and prove it a
sufficient condition for coverage in linearly observed domains. Instantiate
the result first for colist prefix observations, showing that coverage agrees
with the existing `productive` predicate and, separately, when it agrees with
maximality.

Do not make a global `CPO+` instance or arbitrary `CompactProgress` theorem the
first dependency. A later module can add standard way-below compactness and a
cofinal-basis property, then recover the strongest correct fragment of the
original compact-refinement conjecture.

### 2. Two interpretations and a realizability relation

Keep AlgCo's existing semantic interpretation, but associate each relevant
source type with an operational interpretation and a logical relation:

```text
V_A         the existing semantic interpretation of A
D_A         the operational domain/partial computation interpretation of A
R_A d v     operational object d correctly realizes semantic value v
Total_A d   operational object d is fully defined at type A
```

Start with a flat operational lifting for scalar results and then define
observation-indexed interpretations for `colist`, `cotree`, and other extracted
coinductive types. This can be implemented with a partiality monad, a fuelled
evaluator, or an equivalent small-step relation; it need not initially require
a second full CPO library.

It is important that the lifting distinguish all of the following:

```text
no result yet
a returned semantic bottom
a returned partially observable coinductive value
a fully defined finite observation
```

### 3. Type-directed operational lifting

Define how operational partiality occurs at each type constructor. Base values
can be discrete with respect to the operational order while retaining their
AlgCo semantic order. Products, sums, functions, and coinductive types must
reflect the demand/strictness behaviour of the extraction target. Define
`Total_A` recursively over this interpretation.

### 4. Approximation interpreter for extraction equations

Define finite-fuel versions of the Haskell equations used for `cofold` and,
eventually, `coopfold`. The interpreter must model demand: a lifted step
function should not be forced to inspect its recursive argument when the source
function could return without doing so.

Prove monotonicity in the operational approximation relation, or the
corresponding fuel-extension lemma if using an evaluator rather than a CPO.
Use the scalar `colist_existsb` example as the first regression test: a literal
returned `false` must be total, a finite witness must eventually produce
`true`, and the infinite no-witness computation must remain operationally
undefined at every finite fuel.

### 5. Soundness, operational adequacy, and totality

First prove finite semantic soundness:

```text
if a finite operational approximation produces an observation,
that observation agrees with the denotational Coq `cofold`
```

Separately connect the formal approximation relation to evaluation of the
selected target equation:

```text
the target program produces an observation
  <->
some finite formal approximation produces it
```

This is the computational adequacy statement. Because an `Extract Constant`
body is opaque to Coq, an end-to-end version requires either a formal target
language and verified extraction connection or an explicit assumption that
the inserted equation implements the formal evaluator.

Finally prove or assume observation coverage for the program at hand. The
combined missing extraction theorem is conditional:

```text
if the formal operational computation covers every required observation,
then the extracted computation is terminating/productive; every observation
it produces agrees with the denotational value of `cofold`
```

This avoids claiming that every use of generic `cofold` is executable. Such a
claim is false for arbitrary `B`, `f`, and input colists.

### 6. Program-specific progress proofs or a syntactic checker

For each extracted program, establish operational convergence/totality either
directly or through a reusable sufficient criterion. Semantic maximality in an
AlgCo `OType` is not, by itself, such a criterion.

For sieve, the outer `sieve_f` is guarded by `cocons`, so producing the next
outer constructor is immediate once its input head is available. Producing
later constructors also involves `cofilter`, which may skip arbitrarily many
inputs. Its proof therefore needs an eventual-progress fact: after each emitted
prime, a later candidate survives the accumulated filters. Existing
completeness and unboundedness-of-primes arguments may provide the mathematical
ingredient, but they must be connected explicitly to finite evaluation of the
filtering computation.

A later phase could package common cases as a friendly-function, sized-type, or
mixed recursion/corecursion check. Such a check would be sufficient rather than
necessary, while the lifted approximation semantics would remain the statement
of what extraction correctness means.

## Appendix: recovered original passage

The following is preserved verbatim from lines 26–70 of the external working
notes. Apparent omissions and the ill-typed `f z = z` expression are retained
here as historical source text and corrected in the analysis above.

```text
semantic notion of productivity:

Look at Hasse diagram of codomain of function. A function f is
productive on input x if for all compact b <= x, f(b) is maximal (has
no further refinements) or there exists compact b' such that b <= b'
and f(b) < f(b'). f is productive everywhere or just "productive" if
it's productive at all points. Productive functions with compact
domains are terminating. For some order relations, continuity is
equivalent to productivity. Depending on the order relation,
continuity may instead correspond to semidecidability (e.g., false <=
true order on bool).

When exactly does continuity correspond to computability? should be a
order-theoretic property of the domain and codomain types. What is the
weakest condition P such that continuous /\ P <-> productive? Maybe
check other papers that we compared with.

Computable functions should send maximal (i.e., those with complete
information) elements to maximal elements. When we use the false <=
true ordering, we are saying that false is a state of incomplete
information, so a function that maps an entire stream to false will
not terminate because the output remains in a state of incomplete
information forever.

Is it true that "continuous + maps maximal to maximal <-> productive"?

Continuous f : A -> B:
forall g : nat -> A, f (sup g) = sup (f \circ g)

Maximal to maximal property for function f : A -> B:
forall x : A, (forall y : A, x <= y -> x = y) ->
  forall z : B, f x <= z -> f z = z.

Productive f : A -> B:
forall a : A, forall b : B(A), b <= a ->
  maximal (f b) \/ exists b' : B(A), b <= b' /\ f b < f b'.

Perhaps can prove that productive functions into compact domains are
definable by induction, and productive functions in general are
equivalent to coinductive inductive functions (can infinitely produce
next refinement of output by an inductive step).

Subset type for productive functions, make cofolds (or any function
with an associated extraction primitive) take only productive
functions as arguments and be productive themselves.
```

## Scope and nearby issue

This note concerns the semantic justification of extracted folds. There is also
an apparently separate mechanical problem in the hand-written `coopfold`
extraction for tries: the string in
[`theories/cotrie.v`](../theories/cotrie.v#L1097) contains `Cotrie_Node` and an
unbound `pC`. That should be repaired independently and should not be confused
with the productivity/termination question.

## Concise statement of the missing theorem

The recovered notes identify two distinct missing connections. The corrected
semantic core is approximately:

```text
Let q be a directed chain with supremum s, and let finite observations be
upward closed and Scott-open. Then

  Total s <-> forall request r, exists n, Observes r (q n).

For continuous f, instantiate q with

  fun n => f (incl (ideal x n)).
```

A frontier-progress relation can be used as a sufficient local proof of the
right-hand side, but arbitrary strict increase cannot. Maximality is a derived
reformulation only for domains satisfying `Total s <-> maximal s`; it does not
justify extraction in an arbitrary AlgCo order.

The operational theorem was probably not

```text
productive l -> extracted cofold f l is productive
```

because `bad_stream` refutes that shape. A defensible operational target is
closer to:

```text
If the type-directed operational approximants of the selected extraction
equation cover every finite request, then the target computation produces all
of those observations. If a finite approximation produces an observation, it
agrees with the denotational Coq value cofold f l.
```

The first sentence is operational adequacy plus coverage; the second is finite
semantic soundness. The remaining substantive work is to formalize the
approximants, connect them to the opaque extraction equation, and supply
tractable frontier/fairness conditions. Those conditions must be proved for
the chain generated by the selected `cofold` equation rather than assumed only
of its step function. A concrete proof is still required for sieve and the
other extraction examples.
