# DR-0021 — Arbitrary-domain quantified semantic foundation

Date: 2026-08-20

## Question

Can the finite quantified semantics and exact threshold-projection theorem be extended
soundly to arbitrary nonempty domains, and which additional hypotheses are actually
needed?

## Counterexample-first result

The naive unrestricted projection theorem is false. On `D=[0,1)`, the truth evidence
`g(d)=d` has supremum `1` but no value reaches `1`. At threshold `1`, the continuous
existential projects truth-positive although no projected instance is truth-positive.
This counterexample is formalized by
`InfiniteFO.existential_projection_counterexample` and embedded into the actual formula
`∃x P(x)` by `InfiniteFO.formula_projection_counterexample`.

## Decision

Install a separate arbitrary-domain semantic module, `Nullivance.InfiniteFO`, with:

- nonempty arbitrary domains;
- infimum/supremum continuous quantifiers and the matching FOUR quantifiers;
- explicit square-valued predicate models and a structural boundedness theorem;
- a threshold-local witness condition only on supremum channels;
- exact projection under that recursive condition;
- an unconditional finite-domain specialization.

A second verified layer identifies a natural sufficient class: on a nonempty compact
topological domain, upper semicontinuity of the relevant universal-falsity and
existential-truth families implies all threshold witnesses. This condition is tracked
recursively by `InfiniteFO.UpperSemicontinuousQuantifiers` and yields
`InfiniteFO.compact_upperSemicontinuous_exact_projection`.

The third verified layer removes the formula-relative premise for the equality-free
fragment. `InfiniteFO.AtomContinuous` requires continuity of every assignment-induced
predicate occurrence. The parametric compact maximum/minimum theorem then proves
continuous evaluation through arbitrarily nested quantifiers, from which
`InfiniteFO.compact_atomContinuous_exact_projection` follows automatically.

The fourth layer resolves the crisp-equality boundary in both directions. Simply
deleting the equality-free restriction is unsound: on compact `[0,1]`, the formula
`∃x (¬(x = y) ⊕ P(x))` with `y = 1` and continuous `P(x) = (x,0)` has existential
truth supremum `1` but no truth-positive instance at threshold `1`. This is the checked
formula-level counterexample
`InfiniteFO.compact_continuousAtom_with_equality_projection_counterexample`.
Conversely, `InfiniteFO.PredicateFree` formulas, which may contain equality but no
predicate atoms, evaluate only at square corners. Their quantified suprema and infima
remain crisp, so `InfiniteFO.predicateFree_exact_projection` proves exact projection
on every nonempty domain without topology, compactness, or finiteness.

The fifth layer verifies a nontrivial mixed fragment rather than stopping at the two
pure fragments. `InfiniteFO.BinderEqSafe` tracks the finite set of variables bound by
enclosing quantifiers. A nonreflexive equality is admitted only when neither side is
in that set. A masked-assignment induction proves continuity in the active bound
variables while fixing all free variables; compactness then supplies every required
maximum. The resulting theorem
`InfiniteFO.compact_binderIndependentEquality_exact_projection` strictly contains
the equality-free compact theorem and admits examples such as
`∃x ((y=z) ∧ P(x))`. The endpoint-puncture counterexample is mechanically rejected
because its equality uses the active variable `x`.

The sixth layer adds a polarity- and connective-sensitive refinement on compact
Hausdorff domains. Crisp equality truth is the indicator of the closed diagonal and
is therefore upper semicontinuous even when it depends on a quantified variable;
equality falsity is not granted that status. `InfiniteFO.CoordinateUSCSafe` propagates
the requested truth/falsity coordinate through negation and each binary connective.
`InfiniteFO.PolarityProjectionSafe` requests only universal-body falsity and
existential-body truth, exactly the two supremum channels that need witnesses. This
admits `∃x ((x=y) ∧ P(x))` and `∀x (¬(x=y) ∨ P(x))`, strictly extending the
binder-independent class, while mechanically rejecting the endpoint-puncture
formula. `InfiniteFO.compact_polaritySafeEquality_exact_projection` is the resulting
checked projection theorem. Rejection by this static analysis is not interpreted as
a semantic counterexample.

The seventh layer makes this reasoning executable and recognizes connective
domination. `InfiniteFO.CoordRegularity` is the finite abstract domain
`zero/one/upper/unknown`; its abstract minimum and maximum retain constant identities
and absorbing values. `InfiniteFO.analyzeCoordinate_sound` proves that the computed
classes have their advertised semantics, while
`InfiniteFO.compact_regularityCertified_exact_projection` turns a successful Boolean
`regularityProjectionCheck` into exact projection. The analyzer strictly extends the
polarity grammar: it certifies an existential body whose unsafe subbranch is conjoined
with constant-zero truth. A checked predicate-free example is exact despite receiving
`false`, formally recording that failure means `unknown`, never `refuted`.

The eighth layer makes the executable certificate independently inspectable.
`InfiniteFO.CoordExplanation` records the atomic reason and the precise abstract
minimum/maximum transfer rule at each connective. Its executable reconstruction is
proved equal to `analyzeCoordinate` by
`InfiniteFO.explainCoordinate_inferredRegularity`. A global
`InfiniteFO.ProjectionAnalysisReport` stores every quantified-coordinate report and
the first unresolved path. `InfiniteFO.firstUnknownQuantifier_isNone` proves that this
diagnostic is absent exactly when `regularityProjectionCheck` succeeds. Therefore a
Boolean failure is localized and explained, while still carrying no semantic claim of
refutation.

The ninth layer combines two independently proved witness mechanisms at each
quantified node. `InfiniteFO.predicateFreeCheck` is proved equivalent to the
predicate-free grammar, and `InfiniteFO.witnessCoordinateCheck` accepts either this
crisp certificate or the earlier regularity certificate. The structural theorem
`InfiniteFO.thresholdRegular_of_witnessProjectionCheck` permits the selected mechanism
to vary across nested quantifiers and yields
`InfiniteFO.compact_witnessCertified_exact_projection`. This strictly resolves the
old false negative `∃x ¬(x=y)` through crispness, while a kernel reduction confirms
that the compact endpoint-puncture counterexample remains rejected. A matching
first-unwitnessed diagnostic is proved complete for the combined Boolean checker.

The tenth layer replaces the independent union by a reduced product.
`InfiniteFO.CoordProductFacts` tracks exact zero, exact one, crispness, and upper
semicontinuity simultaneously. `InfiniteFO.reducedCrisp` imports constant information
from the regularity component into the crisp component before a parent connective is
analyzed. `InfiniteFO.analyzeCoordinateProduct_sound` proves the concrete meaning of
all four projections. The product checker strictly extends the ninth layer: it
certifies `∃x ((P(x) ∨ (z=z)) ∧ ¬(x=y))`, whose predicate-containing left branch is
reduced to constant one and therefore contributes crispness to the parent. The
independent union rejects this example, while
`InfiniteFO.compact_productCertified_exact_projection` proves it exact. The known
endpoint-puncture counterexample remains rejected, and a complete product diagnostic
records all four failed facts at that node.

The eleventh layer audits the product as an abstract domain rather than only as an
executable checker. `InfiniteFO.CoordProductFacts.Refines` is proved to be a partial
order, and its concretization is antitone with respect to precision. The canonical
reduction is proved extensive, monotone, idempotent, concretization-preserving, and
least among reduced refinements; analyzer outputs are reduced and consistent.
Explicit minimum and maximum transfers are proved semantically sound and monotone.
The stronger hypothesis that these four facts form a constant-complete analysis is
then independently tested and refuted: `(x=y) ∧ ¬(x=y)` is universally truth-zero but
does not receive the `zero` flag, while `(x=y) ∨ ¬(x=y)` is universally truth-one but
does not receive the `one` flag. The analyzer therefore remains a sound sufficient
procedure, not a best correct approximation; correlation tracking is the identified
next refinement.

The twelfth layer implements that first correlation refinement in the separate
`Nullivance.RelationalFO` module. `InfiniteFO.ExactComplement` relates the complete
truth--falsity pair by `t+f=1`; equality receives this certificate. The analyzer is
proved sound through negation, conjunction, disjunction, and both arbitrary-domain
quantifiers. Its quantifier proof establishes the dual infimum/supremum equations
directly and does not assume attainment. `InfiniteFO.PairProductFacts` combines two
coordinate products with this relation. Its cross-coordinate reduction exchanges
dual constants and crispness, preserves concretization, and is idempotent. A direct
syntactic correlation rule then proves the exact values of crisp `φ∧¬φ` and `φ∨¬φ`.
It strictly repairs both equality false negatives that refuted constant completeness,
while retaining all old facts. `oplus` remains outside the complement transfer because
the checked input `(x=x) ⊕ ¬(x=x)` evaluates to `(0,0)`.

The thirteenth layer makes the relational refinement structurally recursive.
Verified paired transfers for negation, conjunction, disjunction, and consensus now
consume already reduced child facts. A quantified merge transports recursive
constant, crisp, and complement certificates across arbitrarily nested binders while
retaining upper semicontinuity only from the existing syntax-aware geometric analysis.
`InfiniteFO.analyzeRelationalRecursive_sound` proves the complete interpreter sound.
Checked regressions show a hidden excluded-middle constant restoring a predicate
parent's upper semicontinuity and a contradiction constant passing through an
existential and then a universal quantifier. Finally, the recursive relational
projection checker strictly certifies
`∃x (((x=y) ∨ ¬(x=y)) ∧ P(x))`, which the old product checker rejects, and proves its
exact projection on compact Hausdorff domains with continuous predicate atoms.

The threshold witness at `τ` is

`τ ≤ sup(range g) → ∃d, τ ≤ g(d)`.

This is strictly weaker than requiring the supremum to be attained. Infimum channels
need no analogous witness: for nonempty bounded real families,
`τ ≤ inf(range g)` is equivalent to `∀d, τ ≤ g(d)`.

## Impact

- Theorem 2.24 remains correct and is recovered as a specialization.
- The earlier warning about unattained suprema is promoted to the checked refutation
  Theorem 2.32.
- No infinite-domain tableau, compactness, completeness, or decidability theorem is
  claimed. Those remain separate research problems.
- The compact result is formula-relative. Deriving its regularity hypothesis solely
  from continuous atomic predicates is now verified for equality-free formulas.
- Crisp equality cannot be added freely to the automatic continuity theorem: the
  checked compact formula counterexample above refutes that extension. The pure
  predicate-free equality fragment is nevertheless exact on every nonempty domain,
  binder-independent equality gives a verified sufficient mixed fragment, and the
  polarity-sensitive refinement safely admits some binder-dependent equalities on
  compact Hausdorff domains. The executable regularity analyzer further recognizes
  constant domination, reconstructs its certificates from checked reason trees, and
  localizes conservative failures without changing their meaning. The disjunctive
  witness checker additionally covers every predicate-free formula and may mix crisp
  and regularity mechanisms across nested quantifiers. The reduced product additionally
  exchanges constant information between the two analyses and strictly enlarges this
  executable class. Its order, reduction, and minimum/maximum transfers now have a
  formal abstract-interpretation audit. Checked equality/complement examples refute
  constant completeness. The paired relational refinement now repairs those two
  examples soundly and strictly. Its recursive extension carries the resulting facts
  through parent contexts and nested quantifiers and yields a strictly stronger exact
  projection checker. It still makes no global completeness claim, so none of these
  analyzers is claimed to characterize every safe mixed formula.
- The submitted finite-domain manuscript need not change merely because this semantic
  foundation exists; publication claims should be expanded only after a separate
  manuscript-level audit.

## Rejected alternatives

1. State unrestricted exact projection: rejected by the checked `[0,1)` counterexample.
2. Require every infimum and supremum to be attained: sound but unnecessarily strong.
3. Change closed thresholding `τ ≤ x` to strict thresholding: rejected because it would
   alter the established propositional semantics and does not uniformly eliminate all
   limit-boundary issues.
4. Assume only compactness or only continuity: both are rejected by checked boundary
   examples. The identity family on `[0,1)` is continuous but lives on a noncompact
   domain; the endpoint-drop family on compact `[0,1]` is not upper semicontinuous.
5. Delete the equality-free premise while keeping only continuous predicate atoms:
   rejected by the checked compact formula `∃x (¬(x = y) ⊕ P(x))` at `y = 1`.
6. Claim that the four-flag reduced product discovers every semantic constant:
   rejected by the checked contradiction and excluded-middle equality pairs. Their
   exact value depends on a relation between sibling results that unary flags discard.

## Remaining scope

The module establishes semantics, boundedness, two independent projection obstructions,
repaired projection, the compact continuous-atom equality-free class, and the
arbitrary-domain predicate-free equality class, and a compact binder-independent
mixed class, and a strictly larger compact Hausdorff polarity-safe class. It does not
yet establish an infinitary proof calculus, characterize the maximal safe mixed
fragment, represent arbitrary correlations beyond the implemented direct
  formula/negation relation, characterize completeness of the recursive abstract domain,
  turn an unknown diagnostic into a semantic counterexample, or prove any completeness
  theorem over arbitrary domains.

## Relative-completeness audit

The recursive relational analyzer is now proved complete for the three
classical-edge flags—truth crispness, falsity crispness, and exact complementarity—on
the equality-only fragment generated by negation, the truth-lattice connectives, and
nested quantifiers. This is a property-completeness result for the abstract domain,
not full semantic constant completeness.

The stronger truth-one completeness claim is formally refuted by the De Morgan formula
`(p ∧ q) ∨ (¬p ∨ ¬q)`: it is universally truth-one, but the analyzer leaves its
truth-one flag unset. The failure isolates missing Boolean canonicalization rather
than an unsound inference. A future precision extension must therefore add a verified
normal form or a richer correlation domain and separately prove that it preserves the
existing soundness boundary.

The first such extension is now verified. Polarity normalization exposes complement
pairs modulo De Morgan laws and quantifier duality, preserves the continuous semantics
exactly, and strictly repairs the original De Morgan witness. It does not establish
full canonicalization: a second checked tautology requiring distributivity remains
undetected. The next precision layer must therefore use a representation such as a
verified decision diagram or another canonical Boolean quotient; repeated local
rewrite rules alone would not justify a completeness claim.

That decision-diagram layer is now implemented in `Nullivance.BooleanROBDD` for the
quantifier-free Boolean equality skeleton. Symmetry-normalized atoms receive a fixed
order, Shannon compilation is proved evaluation preserving, fixed-order ROBDD equality
is proved equivalent to agreement under every Boolean valuation, and the output has
checked reduction and ordering invariants plus a duplicate-free shared-subgraph table.
The relational wrapper is sound and Boolean-complete for constant truth/falsity. It
repairs the distributive witness above.

The scope boundary is intentional and executable. Equality transitivity is valid in
every concrete model but fails under an independent Boolean valuation of the three
atoms, and quantified formulas are rejected by the translator. The next layer must
combine ROBDD reasoning with a verified equality-theory procedure before any
quantifier integration or stronger completeness claim is attempted.

That equality-theory layer is now implemented in `Nullivance.EqualityTheoryROBDD`.
A persistent union--find supplies reflexive, symmetric, and transitive closure;
disequalities are checked against its classes. The central traversal theorem is an
iff between checker acceptance and evaluation in every realizing concrete model.
Its completeness direction uses the canonical quotient model of a consistent state.
The theory-aware analyzer is sound, refines the normalized analyzer, repairs the
transitivity witness, and detects the corresponding inconsistent conjunction.

Quantifier integration remains deliberately separate. The existing translator still
rejects `all` and `ex`, and the theory-aware wrapper provably falls back to the prior
analyzer on such input. The next research obligation is therefore a binder-aware
representation and proof of its interaction with equality classes, not an extension
of the present quantifier-free completeness statement by assertion.

The binder-aware interface is now formalized in
`Nullivance.QuantifiedEqualityROBDD`. Free and bound variables are executable;
capture-safe substitution is proved semantically correct under its exact freshness
premise on arbitrary domains. Covered scopes give exact universal and existential
instantiation, and a fresh union--find binder is proved to preserve the outer state.
Every witness is classified into an existing equality class or a class fresh from the
scope, with realization proofs for both branches.

An executable recursive kernel is proved exact for the entire quantified equality
fragment on each finite nonempty domain, and it agrees with compiled ROBDD evaluation
at quantifier-free leaves. Fresh-witness availability is now correlated globally by
the rank-indexed `CapacityEquiv` relation and its numerical realization
`CardinalityCapacity`. The verified induction consumes at most one fresh
representative per genuinely new binder value and consumes none for an old equality
class.

The resulting cutoff theorem closes the previously recorded pure-equality obligation:
closed formulas of rank at most `k` agree on all domains having at least `k` elements;
in particular all infinite domains agree, and their value is computed by the verified
finite kernel on a canonical domain of size `rank+1`. The checked rank-two sentence
`exists x, forall y, x=y` still distinguishes one from two elements and documents why
the lower-capacity premise cannot be erased. This result does not extend to formulas
with predicate atoms or establish completeness of the broader continuous relational
analyzers.

The semantic cutoff is now connected to a complete executable ROBDD(T) baseline in
`Nullivance.QuantifiedEqualityDecision`. An explicit variable environment expands
each binder over canonical representatives without textual substitution. Expansion
is proved exactly equivalent to the finite kernel on every covered finite domain and
is then compiled by the verified ROBDD compiler. A persistent equality state records
all pairwise disequalities among cutoff representatives. The theory checker accepts
exactly the canonical target, and the resulting total decision bit is proved correct
for every closed pure-equality sentence on every infinite nonempty domain.

This closes the correctness and completeness obligation for the stated fragment. A
second, orbit-reduced implementation now branches directly over the equality classes
already introduced on the current binder path plus one capacity-consuming fresh class.
Equivariance under finite-domain permutations proves that all unused representatives
are semantically interchangeable. The optimized expansion is proved exactly equivalent
to finite evaluation and to the full-enumeration ROBDD on closed inputs, and therefore
correct on every infinite nonempty domain. Its concrete binder list has at most `u+1`
children for `u` used classes and never exceeds full enumeration; a checked three-binder
example is strictly smaller before ROBDD compilation. A global asymptotic bound for an
additional memoized shared orbit-state graph remains a performance research problem,
not a missing semantic theorem.

The first global complexity layer is now formalized separately. Its exact terminal
recurrence is `L(n+1,u)=uL(n,u)+L(n,u+1)`, producing the Bell/Touchard values at the
empty root; Lean proves the conservative global bounds `L(n,0) ≤ n!` and total nodes
at most `(n+1)n!`. Memoization cannot key only on `u`: an executable counterexample
shows two live environments with the same class count but different equality results.
The canonical key therefore includes the residual formula and its live free-variable
environment. Equal keys are proved to produce identical Boolean syntax, and a verified
association-list cache query/update preserves an explicit no-collision invariant.

The table is now threaded through every recursive child. Binary and binder siblings are
evaluated sequentially so later calls see earlier entries. A simultaneous well-founded
proof shows exact equality with the non-memoized orbit formula and preservation of the
table invariant at every return. Native regressions record real hits, misses, stored
states, and output size; the three-distinct-elements case has two cache hits across 42
requests, while a deliberately repeated closed subformula produces a direct sibling hit.
These measurements establish actual reuse, but they are not promoted to a universal
average-case speedup claim.

The linear association list is now retained only as a reference semantics for cache
operations. `Nullivance.QuantifiedEqualityHashMemo` executes the same traversal with
`Std.HashMap`; lawful decidable equality makes the structural hash collision-safe.
Lean proves empty-table and insertion-level extensional simulation, then independently
proves the hash traversal equal to the non-memoized orbit expansion and therefore to
the list traversal, ROBDD result, and infinite-domain decision.

The performance statement is deliberately representation-neutral. An executable
cache-free recurrence counts the full request tree at the chosen cutoff. For every run,
actual requests are below this recurrence and hash-table growth is below misses; from
the empty root, distinct stored states are consequently bounded by misses and by the
cutoff recurrence. This closes the finite unique-state obligation without asserting an
unverified constant-time, amortized, or wall-clock bound for `Std.HashMap`.

The state inequality has subsequently been sharpened to an equality. A simultaneous
structural proof tracks the size of every newly inserted residual formula. Calls below
a node can insert only formulas no larger than a strict child, so they cannot insert the
parent key after its failed lookup. Consequently each miss increases map size exactly
once and an empty-root run satisfies `unique states = misses`.

A second induction converts the executable request recurrence to a closed syntactic
bound. With at least `quantifierRank` fresh names available, requests are bounded by
the syntax-node count times the Bell/Touchard equality-partition count. The previously
proved Bell-to-factorial comparison then yields `states ≤ |phi|·qr(phi)!`. This is a
finite combinatorial theorem about reachable memo states; it remains distinct from a
machine-time complexity theorem for the hash-table implementation.
