# Related work and alternative frameworks for AlgCo

## Status and scope

This report records a related-work survey current to July 27, 2026.  It asks
which papers and projects provide something similar to AlgCo, taking the
distinctive AlgCo package to be:

1. a coinductive carrier equipped with an approximation order;
2. an inductive type of compact basis elements and a canonical sequence of
   approximants;
3. a continuous-extension principle that turns a monotone function on the
   basis into a continuous function on the completed carrier; and
4. proof principles that reduce properties of those extensions to ordinary
   induction over basis elements.

This is narrower than merely supporting coinduction, productive corecursion,
or domain theory.  Those facilities solve related problems, but most of them
address only one side of AlgCo's definition-and-proof interface.

The main source for AlgCo is Bagnall, Stewart, and Banerjee,
[*Inductive Reasoning for Coinductive Types*](https://arxiv.org/abs/2301.09802)
(2023).  Chapter 9.2 of Bagnall's
[*Formally Verified Samplers From Discrete Probabilistic Programs*](https://bagnalla.github.io/papers/Bagnall_Accepted_Dissertation_SP23.pdf)
contains a longer comparison with the work known at the time.

This report complements the local
[`AlgCo 2 design sketch`](algco2-design.md).  In particular, that sketch's
separation between semantic values, algebraic partial completions, sequential
presentations, and operational computation is also useful for classifying
related systems.

## Executive summary

- **Haddock is the closest overall Coq comparison currently available.**  It
  formalizes algebraic CPOs, compact elements, ideal completion, continuous
  extension from compact elements, and partial corecursive functions.  Its
  main user-facing definition principle is nevertheless a least fixed point of
  a continuous functional, and its totality and bisimilarity arguments are
  coinductive rather than AlgCo-style basis induction.

- **Lochbihler and Hölzl provide the closest precursor to AlgCo's central
  consumer-view construction.**  They define lazy-list filtering as the
  continuous extension of a function on finite lists and reduce proofs to list
  induction.  Their construction is specific to lazy lists in Isabelle/HOL.

- **Rusu and Nowak provide the closest earlier Coq treatment based directly on
  approximants.**  They define non-guarded corecursive functions as limits of
  sequences of approximations subject to semantic productivity obligations.
  Their later line of work led to Haddock.

- **Isabelle/HOLCF is the closest mature general-purpose domain-theory
  ecosystem.**  It has CPOs, continuous-function spaces, compact bases,
  recursive domains, fixed-point induction, and substantial automation, but
  it starts with domain representations rather than deriving an AlgCo
  interface for native Coq coinductives.

- **Dafny, Isabelle's AmiCo package, Agda, Paco, cawu, and Interaction Trees
  are important alternatives for particular parts of the problem.**  Dafny
  turns coinductive predicate proofs into induction on finite unfoldings;
  AmiCo and Agda broaden productive corecursion; Paco and cawu improve
  greatest-fixed-point proofs; Interaction Trees specialize an ergonomic
  algebraic interface to effectful computations.

No other project located in this survey combines AlgCo's exact collection of
native Coq coinductives, a generic algebraic-CPO hierarchy, continuous
elimination into general codomains, and proofs by induction over compact basis
elements.  This is a landscape assessment rather than a formal novelty or
priority claim.

## The AlgCo baseline

For an algebraic CPO `A` with basis `B(A)`, AlgCo supplies an inclusion

```text
incl : B(A) → A
```

and a canonical increasing family

```text
ideal : A → ℕ → B(A)
```

whose included values converge to their argument.  A monotone map

```text
f : B(A) → C
```

into a CPO `C` has a continuous extension

```text
fᶜᵒ(a) = supₙ f(ideal a n).
```

Uniqueness of continuous extension yields the central proof rule: two
continuous functions `A → C` are equal if they agree on all included basis
elements.  When `B(A)` is inductive, agreement is proved by structural
induction.  Continuous and cocontinuous predicates similarly reduce liveness-
and safety-shaped statements to finite approximants.

The paper instantiates this structure for conats, coinductive lists,
coinductive tries, and finitely branching infinitary trees.  Its applications
include an infinitary sieve, a regular-expression implementation based on
tries, and weakest pre-expectation semantics for coinductive samplers.  The
current implementation is centered on
[`theories/aCPO.v`](../theories/aCPO.v), with the newer generic experiments in
[`theories/generic/`](../theories/generic/).

AlgCo's general continuous extension uses a nonconstructive supremum and is
not executable in general.  Particular constructions such as lazy coiteration
and `cofold` have extraction interpretations.  The distinction between their
denotational equations and operational productivity is analyzed separately in
[`cofold-extraction-productivity.md`](cofold-extraction-productivity.md).

## Comparison at a glance

| Framework | Representation | Main definition principle | Main proof principle | Relation to AlgCo |
|---|---|---|---|---|
| AlgCo | Native Coq coinductives equipped with algebraic-CPO instances | Continuous extension from a monotone basis map | Structural induction over compact basis elements | Baseline |
| Haddock | Coinductive domains constructed by completion of partial finite values | Least fixed point of a Haddock-continuous functional; also unique extension from compacts | Domain reasoning plus coinductive totality and bisimilarity | Closest overall mathematical and Coq overlap |
| Lochbihler–Hölzl | Isabelle lazy lists with CCPO and topology instances | Least fixed point as producer; continuous extension as consumer | Fixed-point induction or induction on finite lists | Closest match to the continuous-extension technique, but list-specific |
| Rusu–Nowak | Coq codata obtained as limits of approximation sequences | Limit of semantically productive approximants | Approximation and productivity arguments | Direct approximant-based Coq predecessor |
| Isabelle/HOLCF | Lazy and partial values represented directly as domains | Least fixed points and recursive domain equations | Fixed-point, domain, and coinductive reasoning | Closest mature domain-theory environment |
| Dafny | Native codatatypes and greatest predicates | Corecursive functions and greatest fixed points | Induction over finite prefix predicates, largely SMT-automated | Closest proof-level user experience for predicates |
| Isabelle AmiCo | Native Isabelle codatatypes | Corecursion under registered friendly operations | Coinduction up to friendly operations | Alternative for definitions rejected by guardedness |
| Interaction Trees | One generic coinductive free-monad-like datatype | Guarded corecursion, iteration, and event interpretation | Equational rewriting and parameterized coinduction | Specialized algebraic interface for recursive effects |

## Closest matches

### Haddock

Cheval, Nowak, and Rusu's
[*Formal Definitions and Proofs for Partial (Co)Recursive Functions*](https://www.sciencedirect.com/science/article/pii/S2352220824000531)
(2024) and its
[`haddock` Coq development](https://github.com/vladmgrusu/haddock) are the
closest comparison found in this survey.

The overlap is substantial.  The documented development contains modules for:

- CPOs, compactness, and continuity;
- ideals and algebraic CPOs;
- completion of a pointed partial order by an algebraic CPO;
- unique completion of monotone maps between compact elements as continuous
  maps (`FunComp.v`);
- streams as completions of finite approximations;
- rose trees, totality, and bisimilarity; and
- examples including stream filtering, tree mirroring, Collatz iteration, and
  while loops.

Thus Haddock is not merely another productivity checker.  It contains almost
the same domain-theoretic spine as AlgCo, including algebraicity and extension
from compact elements.

The main architectural differences are:

1. **Carrier construction.**  Haddock begins with finite partial values
   carrying a definition order and constructs its coinductive carrier by a
   variant of ideal completion.  AlgCo's published instances begin with Coq
   coinductive carriers and prove that they possess the required algebraic-CPO
   structure.

2. **Primary function definition.**  Haddock defines potentially partial
   recursive and corecursive functions as least fixed points of continuous
   higher-order functionals.  Its Haddock-continuity criterion is designed to
   make the required continuity proofs practical.  AlgCo usually defines a
   function by recursion on compact basis elements followed by continuous
   extension.

3. **Primary proof style.**  Haddock introduces coinductive predicates for
   totality and bisimilarity and supplies corresponding coinductive proof
   principles.  AlgCo's characteristic benefit is instead to reduce equality
   and appropriate properties of continuous extensions to induction over the
   basis.

4. **Partiality.**  Haddock intentionally represents partial recursive and
   corecursive functions.  For example, filtering a stream that eventually
   contains no further matches may produce an undefined output.  This is a
   broader operational/semantic concern than the published AlgCo continuous-
   elimination interface.

Haddock is especially relevant to the proposed AlgCo 2 separation

```text
Semantic C      = ν C
FinitePartial C = μ (Lift C)
Partial C       = ν (Lift C).
```

Its completion construction, explicit totality predicate, and partial stream
examples offer a useful comparison for AlgCo 2's partial-completion and
realization layers.  The decisive comparison is not whether both libraries
contain a definition named `Algebraic`, but whether routine functions and
proofs retain AlgCo's low-friction structural-induction interface.

### Recursive functions on lazy lists via domains and topologies

Lochbihler and Hölzl's
[*Recursive Functions on Lazy Lists via Domains and Topologies*](https://www.cs.vu.nl/~jhl890/pub/lochbihler2014recursive.pdf)
(ITP 2014) is the closest precursor to AlgCo's central construction.  The
associated Isabelle material lives in the maintained
[`Coinductive` AFP entry](https://isa-afp.org/entries/Coinductive.html).

The paper treats difficult functions such as lazy-list filtering through two
views:

- the **producer view** defines the function as a least fixed point in a CCPO;
- the **consumer view** defines it as the continuous extension of its behavior
  on finite lists.

The consumer view gives an induction rule over finite lazy lists and supports
short proofs of equations about filtering.  This is essentially the
stream-specific instance of AlgCo's later general recipe.  AlgCo's own
related-work discussion explicitly describes this work as defining `filter`
by continuous extension and reducing its proofs to induction.

The important limitations relative to AlgCo are scope rather than soundness:
the construction is specialized to lazy-list transformers, uses Isabelle's
CCPO and topological infrastructure, and does not package a general algebraic-
CPO elimination principle for conats, tries, trees, real-valued semantics, and
predicates.

### Defining corecursive functions in Coq using approximations

Rusu and Nowak's
[*Defining Corecursive Functions in Coq Using Approximations*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.12)
(ECOOP 2022) presents two implemented techniques for definitions that Coq's
built-in guardedness checker rejects.  The evaluated artifact is linked from
the paper page.

Both methods regard a corecursive result as the limit of a sequence of
approximations.  Instead of relying solely on syntactic guardedness, the user
establishes semantic productivity: for every requested finite observation,
the approximation process eventually produces a sufficiently informative
result.  The examples include the familiar problematic shapes of stream
filtering and tree mirroring.

This work is close to AlgCo in three respects:

- it is implemented in Coq;
- finite approximants mediate the construction of infinite values; and
- it expands the class of definitions beyond primitive guarded corecursion.

It is less general in the particular direction AlgCo emphasizes.  It does not
start from an abstract algebraic CPO `A`, accept an arbitrary target CPO `C`,
and derive every continuous `A → C` from a monotone `B(A) → C`.  Its primary
question is whether a codata-producing approximation process is productive.
AlgCo's question is how continuous consumers and transformers can be defined
and proved correct by induction once algebraicity is available.

The 2024 Haddock work can be read as the more systematic, partiality-aware
continuation of this approximation-based line.

## General domain-theory environments

### Isabelle/HOLCF

[`HOLCF`](https://isabelle.in.tum.de/library/HOL/HOLCF/index.html) is a mature
embedding of domain theory in Isabelle/HOL.  Its facilities include CPOs and
pointed CPOs, continuous-function spaces, algebraic domains and compact bases,
fixed points, recursive domain equations, the `Fixrec` package for recursive
functions, and the `Domain` package for lazy recursive datatypes.  Huffman's
[*HOLCF '11: A Definitional Domain Theory for Verifying Functional Programs*](https://pdxscholar.library.pdx.edu/open_access_etds/113/)
describes the modern architecture and automation.

HOLCF can express much of the mathematics beneath AlgCo and is considerably
broader as a domain-theory environment.  It can model partial and infinite
lazy values, solve recursive domain equations, and derive fixed-point and
domain induction rules.  It is therefore the strongest candidate if the goal
is to move the entire development into an established domain logic.

Its center of gravity is different.  Lazy values are modeled as elements of
domains from the outset, and definitions are normally fixed points in those
domains.  AlgCo instead exposes a compact-basis restriction/extension
interface for familiar Coq coinductive structures and deliberately makes
ordinary structural induction the routine client proof method.

### Kahn networks in Coq

Paulin-Mohring's
[*A Constructive Denotational Semantics for Kahn Networks in Coq*](https://www.lri.fr/~paulin/PUBLIS/paulin07kahn.pdf)
(2007) is an important Coq predecessor.  Its
[`KahnNetworks` development](https://www.lri.fr/~paulin/KahnNetworks/HTML/all-gal.html)
formalizes ordered types, ω-CPOs, monotone and continuous functions,
continuous-function spaces, products, fixed points, fixed-point induction, and
domains of possibly infinite streams.  It applies them to Kahn networks and a
streaming sieve.

This project shares AlgCo's use of Coq, CPO-valued streams, continuity, and a
sieve case study.  It targets compositional denotational semantics for network
feedback, however, rather than the algebraic-basis theorem that turns
coinductive elimination into primitive recursion and induction.

### Other formalized domain theory

Two further projects are mathematically adjacent but less direct substitutes:

- Dockins,
  [*Formalized, Effective Domain Theory in Coq*](https://doi.org/10.1007/978-3-319-08970-6_14)
  (ITP 2014), develops constructive profinite domains, sums, products,
  function spaces, powerdomains, and recursive domain equations.  Its focus is
  effective denotational models rather than proof principles for native
  coinductive data.

- Steinberg, Théry, and Thies,
  [*Computable Analysis and Notions of Continuity in Coq*](https://arxiv.org/abs/1904.13203)
  (2019), uses the Incone library to implement algorithms on infinite inputs
  through finite information.  It is a close conceptual cousin on continuity
  and approximations, but its setting is represented spaces and computable
  analysis rather than algebraic coinductive datatypes.

## Same pain point, different techniques

### Dafny: coinduction reduced to prefix induction

Leino and Moskal's
[*Co-induction Simply*](https://mmoskal.github.io/pdf/coinduction-fm.pdf)
(FM 2014) underlies Dafny's support for codatatypes, greatest predicates, and
greatest lemmas.  The
[`Dafny reference manual`](https://dafny.org/latest/DafnyRef/DafnyRef)
describes the current interface.

For a greatest predicate `P`, Dafny introduces a finite prefix predicate
`P#[k]` and uses the equivalence

```text
P(x) ⇔ ∀ k, P#[k](x).
```

A greatest lemma is translated into a terminating prefix lemma whose recursive
calls decrease `k`.  Thus the trusted verification problem is an ordinary
induction over observation depth, while the user may read the source proof as
coinductive.  SMT automation handles much of the surrounding proof glue.

This is very close to AlgCo's user-facing slogan, but the scope differs.
Dafny's transformation establishes greatest predicates and coinductive
lemmas.  It is not an elimination principle constructing arbitrary
CPO-valued continuous functions from monotone basis functions.

### Isabelle AmiCo and friendly corecursion

Blanchette, Popescu, and Traytel's
[*Foundational Extensible Corecursion*](https://arxiv.org/abs/1501.05425)
(2015) introduced an extensible corecursor based on corecursion up to
well-behaved operations.  Blanchette, Bouzy, Lochbihler, Popescu, and Traytel's
[*Friends with Benefits*](https://traytel.bitbucket.io/papers/esop17-amico/index.html)
(2017) describes its implementation as AmiCo.  The machinery is available in
Isabelle through `corec`, `corecursive`, `friend_of_corec`, and
`coinduction_upto`; see the current
[*Defining Nonprimitively (Co)recursive Functions in Isabelle/HOL*](https://isabelle.in.tum.de/doc/corec.pdf)
tutorial.

A friendly operation consumes at most the permitted amount of input before
producing a constructor.  Once registered, it may surround recursive calls in
later definitions.  The package dynamically synthesizes stronger corecursors
and coinduction-up-to principles as the collection of friends grows.

The examples are directly relevant to AlgCo's tries: the Isabelle tutorial
defines coinductive languages and operations corresponding to union,
concatenation, Kleene star, and intersection.  AmiCo is therefore a strong
alternative for definitions that fail Coq's guardedness checker.

The difference is introduction versus elimination.  AmiCo proves that a
codata-producing equation is productive under friendly contexts.  It does not
generally define a continuous consumer from codata into an unrelated CPO such
as extended nonnegative reals, nor replace the resulting proofs with basis
induction.

### Agda copatterns and sized types

Abel, Pientka, Thibodeau, and Setzer's
[*Copatterns: Programming Infinite Structures by Observations*](https://www.cs.mcgill.ca/~dthibo1/papers/popl170-abel.pdf)
(POPL 2013) provides an observation-oriented syntax for constructing infinite
values.  Agda's current
[`Coinduction`](https://agda.readthedocs.io/en/stable/language/coinduction.html)
documentation presents coinductive records and copattern definitions.

Sized types make observation depth explicit in types and can justify recursive
calls beneath size-preserving operations.  The current
[`Sized Types`](https://agda.readthedocs.io/en/stable/language/sized-types.html)
documentation uses coinductive languages, concatenation, and Kleene star as
examples.  Veltri and van der Weide's
[*Guarded Recursion in Agda via Sized Types*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2019.32)
explains the connection with guarded recursion.

Copatterns supply a general introduction form for codata, and sizes broaden
the definitions accepted as productive.  They do not supply AlgCo's
continuous elimination from an algebraic domain into arbitrary codomains.

### Paco and Coinduction All the Way Up

[`Paco`](https://plv.mpi-sws.org/paco/) implements parameterized coinduction
in Coq.  It replaces primitive coinductive proof terms with a semantic
guarding discipline, making greatest-fixed-point proofs more compositional and
incremental.  AlgCo already uses Paco internally where ordinary coinduction is
still required.

Pous's
[*Coinduction All the Way Up*](https://perso.ens-lyon.fr/damien.pous/cawu/)
(LICS 2016) develops the companion construction and a general theory of
coinduction up to, encompassing parameterized coinduction and second-order
reasoning.  Most of the theory has a standalone Coq formalization.

Both projects concern coinductive predicates and relations, particularly
bisimulation.  They improve the proof theory of greatest fixed points rather
than define deterministic functions out of coinductive structures.  They are
complementary to AlgCo, not replacements for its continuous-extension
interface.

### Interaction Trees

Xia et al.'s
[*Interaction Trees: Representing Recursive and Impure Programs in Coq*](https://arxiv.org/abs/1906.00046)
and the maintained
[`InteractionTrees` library](https://github.com/DeepSpec/InteractionTrees)
provide a generic coinductive datatype for recursive computations with
uninterpreted events and continuations.  Handlers interpret events, monadic
combinators compose computations, and weak bisimulation supplies the main
equational theory.

The library relies internally on coinductive arguments, including Paco, but
its public algebraic laws often let clients prove compiler and semantics
results by rewriting and structural induction.  Interaction Trees therefore
share AlgCo's important engineering goal of hiding coinductive proof details
behind a compositional interface.

The scope is intentionally specialized.  Interaction Trees are a particular
coinductive free-monad-like representation for effectful computations; they
do not recognize arbitrary coinductive carriers as algebraic CPOs or derive
all continuous consumers from compact restrictions.  In return, their
operations are designed for execution and extraction.  This tradeoff is
especially relevant to AlgCo 2's planned interaction-tree acceptance test.

### CoCaml and regular coinductives

Jeannin, Kozen, and Silva's
[*CoCaml: Functional Programming with Regular Coinductive Types*](https://websites.umich.edu/~jeannin/papers/cocaml.pdf)
(2017) and the
[`CoCaml project`](https://www.cs.cornell.edu/projects/CoCaml/) extend an
OCaml-like language with computations over regular coinductive values.  Such
values have finite, possibly cyclic representations.  Recursive eliminations
are parameterized by equation solvers, with examples including infinite
lists, infinitary lambda terms, automata, and p-adic numbers.

CoCaml is notable because it supports genuine computation from certain
coinductive inputs into non-coinductive results.  Its finite-graph restriction
and solver-based semantics make this possible operationally.  The restriction
also excludes general nonregular streams and trees admitted by AlgCo, and the
project is a programming-language implementation rather than a mechanized
verification framework.

### Recent structural coinduction

Downen and Ariola's
[*A Contextual Formalization of Structural Coinduction*](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contextual-formalization-of-structural-coinduction/FB2EFC7777D2AFA8662245C80C246315)
(JFP 2025) develops a proof style for corecursive programs that mirrors the
case structure and hypothesis discipline of structural induction.  Its
foundation is a syntactic program logic justified by abstract-machine
observational equivalence, not algebraic CPOs or compact approximation.

This is a useful recent conceptual neighbor to AlgCo's ergonomic goal, but it
does not provide an AlgCo-like Coq library or continuous-elimination theorem.

## Taxonomy

The related work becomes clearer when divided by the problem it primarily
solves.

### Continuous elimination from infinite data

The closest members of this class are:

- AlgCo;
- Haddock's completion of monotone maps on compact elements;
- Lochbihler and Hölzl's consumer view for lazy lists; and
- CoCaml for the restricted class of regular coinductives.

Only the first three are based directly on domain-theoretic continuity, and
only AlgCo packages the construction as a general proof method over several
native Coq coinductive carriers.

### Domain-theoretic fixed points and recursive domains

This class includes:

- Haddock;
- Isabelle/HOLCF;
- Kahn Networks in Coq; and
- Dockins's effective domain formalization.

These frameworks are natural comparisons for semantic expressiveness,
partiality, and recursive equations.  Their normal proof principles are
fixed-point or domain induction, not necessarily structural induction over a
compact presentation exposed to ordinary users.

### Productive construction beyond syntactic guardedness

This class includes:

- Rusu and Nowak's approximation methods;
- Isabelle AmiCo and friendly corecursion;
- Agda copatterns and sized types; and
- Interaction Trees' guarded constructors and iteration combinators.

They primarily answer whether a proposed infinite output is productive.
AlgCo's continuous elimination additionally covers consumers into types that
are not coinductive and need not have constructors available to guard a
recursive call.

### Better proofs of coinductive propositions

This class includes:

- Dafny greatest lemmas and prefix predicates;
- Paco;
- cawu; and
- contextual structural coinduction.

These systems improve coinductive relations or predicates.  They do not by
themselves solve the problem of defining a functional map such as
`Stream R≥₀∞ → R≥₀∞`.

## What remains distinctive about AlgCo

The individual ingredients of AlgCo are established ideas: algebraic CPOs,
compact bases, continuous extensions, coinductive data, and approximation
orders all have substantial prior literatures.  The distinctive contribution
is their proof-engineering combination:

1. familiar coinductive structures are recognized as algebraic CPOs;
2. their compact restrictions are ordinary inductive types;
3. continuous maps into general CPOs are defined from monotone functions on
   those inductive types;
4. uniqueness of extension turns functional equalities into inductive proofs;
5. continuous and cocontinuous properties give corresponding finite-
   approximation proof rules; and
6. the same interface supports streams, language tries, branching samplers,
   and non-codata semantic codomains.

Most nearby systems improve either codata introduction or coinductive
propositions.  AlgCo's central operation is instead a continuous elimination
principle.  This distinction explains why copatterns, guarded recursion,
friendly corecursion, and Paco are useful but not equivalent.

The principal costs of the AlgCo design are also distinctive:

- it applies only where an appropriate algebraic CPO and tractable basis can
  be exhibited;
- the published framework uses classical choice, excluded middle, functional
  extensionality, and coinductive extensionality assumptions;
- general continuous extensions are denotational rather than executable; and
- extraction for selected extensions needs a separate operational adequacy
  and productivity account.

## Implications for AlgCo 2

The survey suggests several concrete comparison obligations for the clean-
slate design.

### Compare the partial-completion layer directly with Haddock

Haddock should be the primary external comparison for:

- ideal completion versus the proposed generic `ν (Lift C)` construction;
- the relationship between compact partial values and completed values;
- totality as a coinductive predicate versus realization from `Partial C` to
  `Semantic C`;
- partial stream filtering; and
- assumptions required for suprema, equality, and completion.

The desired AlgCo 2 advantage should be stated empirically: descriptor authors
pay the generic setup cost once, while routine function definitions and proofs
reduce to structural recursion and induction on `μ (Lift C)`.

### Preserve the Lochbihler–Hölzl consumer view

Any redesign should continue to support the exact success case that motivated
the consumer view:

1. define a function on finite partial lists;
2. extend it continuously to completed colists; and
3. prove its principal equations and algebraic laws by list-like induction.

If the generic container presentation makes this materially harder for users,
it has lost the core ergonomic result even if the underlying domain theory is
more standard.

### Use Dafny as a proof-interface benchmark

Dafny demonstrates the value of exposing finite observation depth only in the
generated proof obligation, while allowing the source lemma to retain a direct
coinductive reading.  AlgCo 2 can use this as an ergonomics benchmark for
continuous and cocontinuous properties: common proofs should not require users
to unfold supremum definitions or manually manage approximation indices.

### Use AmiCo as a definition benchmark

The coinductive-language examples in Isabelle's `corec` tutorial are a useful
external benchmark for union, concatenation, and Kleene star.  AlgCo 2 should
make clear what it gains in proof induction and general codomains, and what it
loses in direct executability or definition automation, relative to friendly
corecursion.

### Use Interaction Trees as the execution benchmark

Interaction Trees show the payoff of specializing a coinductive representation
around an executable algebra of effects.  The planned Boolean-event
interaction-tree slice should compare:

- construction and interpretation ergonomics;
- equational reasoning;
- weak versus strong observational equivalence;
- extraction behavior; and
- whether the semantic/partial split adds useful proof power without forcing
  noncomputable machinery into the runtime interface.

## Recommended reading order

For the central mathematical idea:

1. AlgCo, Sections 2 and 4;
2. Lochbihler and Hölzl's consumer view;
3. Haddock's algebraic CPO, completion, and function-completion modules; and
4. the HOLCF compact-basis and domain-package material.

For definitions rejected by guardedness:

1. Rusu and Nowak's approximation construction;
2. Haddock's stream filter and rose-tree mirror;
3. Isabelle's `corec` tutorial; and
4. Agda's coinductive-language sized-type example.

For proof ergonomics:

1. AlgCo's equivalence and continuous-property principles;
2. Dafny's prefix predicates and greatest lemmas;
3. Paco and cawu; and
4. Downen and Ariola's structural coinduction.

For executable recursive computations:

1. Interaction Trees;
2. CoCaml's solver-based regular coinductives;
3. AlgCo's extracted `cofold` examples; and
4. the operational caveats in
   [`cofold-extraction-productivity.md`](cofold-extraction-productivity.md).

## Primary links

- Alexander Bagnall, Gordon Stewart, and Anindya Banerjee,
  [*Inductive Reasoning for Coinductive Types*](https://arxiv.org/abs/2301.09802),
  2023.
- Horațiu Cheval, David Nowak, and Vlad Rusu,
  [*Formal Definitions and Proofs for Partial (Co)Recursive Functions*](https://www.sciencedirect.com/science/article/pii/S2352220824000531),
  2024; [`haddock` source](https://github.com/vladmgrusu/haddock).
- Andreas Lochbihler and Johannes Hölzl,
  [*Recursive Functions on Lazy Lists via Domains and Topologies*](https://www.cs.vu.nl/~jhl890/pub/lochbihler2014recursive.pdf),
  2014; [`Coinductive` AFP entry](https://isa-afp.org/entries/Coinductive.html).
- Vlad Rusu and David Nowak,
  [*Defining Corecursive Functions in Coq Using Approximations*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.12),
  2022.
- Brian Huffman,
  [*HOLCF '11: A Definitional Domain Theory for Verifying Functional Programs*](https://pdxscholar.library.pdx.edu/open_access_etds/113/),
  2011; [current HOLCF session](https://isabelle.in.tum.de/library/HOL/HOLCF/index.html).
- Christine Paulin-Mohring,
  [*A Constructive Denotational Semantics for Kahn Networks in Coq*](https://www.lri.fr/~paulin/PUBLIS/paulin07kahn.pdf),
  2007.
- K. Rustan M. Leino and Michał Moskal,
  [*Co-induction Simply*](https://mmoskal.github.io/pdf/coinduction-fm.pdf),
  2014; [current Dafny reference](https://dafny.org/latest/DafnyRef/DafnyRef).
- Jasmin Blanchette, Andrei Popescu, and Dmitriy Traytel,
  [*Foundational Extensible Corecursion*](https://arxiv.org/abs/1501.05425),
  2015.
- Jasmin Blanchette, Aymeric Bouzy, Andreas Lochbihler, Andrei Popescu, and
  Dmitriy Traytel,
  [*Friends with Benefits*](https://traytel.bitbucket.io/papers/esop17-amico/index.html),
  2017.
- Li-yao Xia et al.,
  [*Interaction Trees: Representing Recursive and Impure Programs in Coq*](https://arxiv.org/abs/1906.00046),
  2020; [`InteractionTrees` source](https://github.com/DeepSpec/InteractionTrees).
- Chung-Kil Hur, Georg Neis, Derek Dreyer, and Viktor Vafeiadis,
  [`Paco`](https://plv.mpi-sws.org/paco/), 2013.
- Damien Pous,
  [*Coinduction All the Way Up*](https://perso.ens-lyon.fr/damien.pous/cawu/),
  2016.
- Jean-Baptiste Jeannin, Dexter Kozen, and Alexandra Silva,
  [*CoCaml: Functional Programming with Regular Coinductive Types*](https://websites.umich.edu/~jeannin/papers/cocaml.pdf),
  2017.
- Andreas Abel, Brigitte Pientka, David Thibodeau, and Anton Setzer,
  [*Copatterns: Programming Infinite Structures by Observations*](https://www.cs.mcgill.ca/~dthibo1/papers/popl170-abel.pdf),
  2013.
- Paul Downen and Zena M. Ariola,
  [*A Contextual Formalization of Structural Coinduction*](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/contextual-formalization-of-structural-coinduction/FB2EFC7777D2AFA8662245C80C246315),
  2025.
