# DR-0018 -- Progress-scheduler independence without fairness

Date: 2026-08-13

Status: accepted.

## Intent

Generalize the verified deterministic reference search from one fixed traversal order to
arbitrary selection of active branches, while retaining a theorem precise enough to
prove termination, semantic correctness, and countermodel production in Lean.

The intended operational claim is not that an implementation may idle forever. It is
that whenever work remains, a scheduler may choose any active branch occurrence, must
perform its exact head decomposition, and must retain all children. The final verdict
must not depend on those choices.

## Prerequisites

- finite signed branches and closure: Definition 3.2;
- the sixteen decomposition rules: Definition 3.3;
- reference branch state, child generation, and worklist weight: Definition 3.78;
- deterministic execution and semantic exactness: Definition 3.79 and Theorem 4.34;
- canonical atomic valuation: Definition 4.9;
- declarative semantic completeness: Theorem 4.13.

No undefined prerequisite is used by the accepted definition.

## Candidates considered

1. **Infinite traces with an idle transition and weak fairness.** A scheduler would
   produce a sequence indexed by natural numbers; fairness would require every
   continuously enabled occurrence eventually to be selected. This can model delays,
   but it introduces occurrence ancestry, enabledness through branching, stuttering,
   and a liveness proof that are irrelevant to an implementation that always performs
   available work. Rejected as the canonical operational layer; retained as optional
   future work.

2. **Finite progressing forest relation.** A state is a finite list of active branches.
   One transition selects any nonterminal list occurrence and replaces it by all of its
   children. Accepted. It exposes every genuine scheduling choice while excluding idle
   administrative behavior.

3. **Keep only the deterministic depth-first reference execution.** This was already
   verified by Definitions 3.78–3.79 and Theorem 4.34, but it cannot express or prove
   independence from active-branch selection order. Rejected as insufficient for the
   present strengthening, not as an algorithm.

The user approved proceeding with candidate 2 after the tradeoff was explained.

## Accepted definition

Definition 3.80 introduces:

- `SearchForest`, a finite list of `SearchBranch` occurrences;
- `ForestTerminal`, `ForestAtomicAcc`, `ForestClosed`, and `ForestSat`;
- `ForestStep`, replacing one nonterminal occurrence by all `children`;
- `ForestReach`, the finite reflexive-transitive progress trace;
- `ProgressScheduler`, a dependent function choosing a legal successor of every
  nonterminal forest;
- `treeCost`, the number of nodes in the full remaining expansion tree;
- `forestCost`, the sum of `treeCost` over all current forest occurrences.

Duplicates remain distinct list occurrences. This is required both for precise
scheduler selection and for the cost argument.

## Counterexample-first stress tests

### Idle transition

If `F → F` is legal, the constant sequence is infinite and no natural-valued strict
decrease theorem can hold. A separate fairness hypothesis would be needed. The accepted
relation excludes idle steps.

### Selecting a terminal branch

For terminal `W`, `children(W)=[]`. Permitting its selection deletes an open leaf. A
forest containing only that leaf would then become empty and vacuously closed. The
nonterminal premise in `ForestStep.expand` is therefore load-bearing.

### Dropping one branching child

For `{T⁺(p∨q),T⁻p}`, the `T⁺p` child closes and the `T⁺q` child is satisfiable.
A scheduler retaining only the first child reports a false proof. `ForestStep` inserts
the complete `children(W)` list.

### Naive global worklist weight

Let a branching head share an untouched tail of weight `r`. Both children copy that
tail. The sum of child worklist weights can exceed the parent weight when `r` is large,
so `Σ weight(W)` is not a termination measure for forests. The recursive equation

`c(W)=1+Σ_{W'∈children(W)}c(W')`

accounts exactly for future duplication. Replacing `W` by its children decreases the
forest cost by one.

### Empty forest

The empty forest is terminal and closed by bounded universal quantification. It is not
reachable from the singleton initial forest: every live branch has one or two children,
and terminal branches cannot be selected. The correctness theorem therefore requires
`ForestReach (initialForest B) F`; omitting reachability makes the theorem false for
satisfiable `B` and `F=[]`.

### Duplicates and selection order

Duplicate branches or formulas are counted separately. Every step removes one selected
occurrence, and the full-tree cost decreases by one regardless of its position. The
semantic invariant is existential over forest members, so reordering does not change
its meaning.

No counterexample survived the accepted hypotheses.

## Proof architecture

1. Prove the `treeCost` child equation by exhaustive formula/sign cases.
2. Deduce strict `forestCost` decrease and well-foundedness of `ForestStep`.
3. Derive an explicit contradiction from any proposed infinite transition sequence.
4. Prove a forest is terminal iff no transition is enabled and obtain terminal
   reachability by well-founded induction.
5. Prove immediate-child semantic exactness and lift it through `ForestStep` and
   `ForestReach`.
6. Preserve atomic accumulators through the same trace induction.
7. At terminal states, use atomic closure/canonical valuation to prove closure iff input
   unsatisfiability, then compose with Theorem 4.13.
8. Extract an open member on failure and transport its canonical valuation backward to
   the input.
9. Compare two terminal outputs through their common equivalence to input
   unsatisfiability.

## Impact analysis

- Definition 3.80 and its Lean declarations are new and conservative. No syntax,
  semantic clause, sign, decomposition rule, or declarative closure constructor changes.
- Theorem 4.33 changes from an underspecified `[DRAFT]` fairness claim to the exact
  progress-scheduler theorem and becomes eligible for `[VERIFIED]` after the full gate.
- Theorem 4.34 remains the executable deterministic reference theorem. Theorem 4.33
  generalizes only active-branch selection order and reuses its verified local execution
  facts; neither theorem is circularly used to establish declarative completeness
  (Theorem 4.13).
- The former statement about a transition system that permits idle steps is not claimed.
  Its historical wording is retained struck through in Theorem 4.33's scope correction.
- DR-0017's statement that Theorem 4.33 remains `[DRAFT]` is superseded by this record;
  its distinction between verified reference execution and undefined stuttering
  fairness remains valid.
- No existing `[VERIFIED]` result depends on Theorem 4.33, so no downstream status
  reversion is required.

## Verification targets

- `Operational.treeCost_children`
- `Operational.forestStep_cost_lt`
- `Operational.forestStep_wellFounded`
- `Operational.no_infinite_forestSteps`
- `Operational.run_eq_flatMap_children`
- `Operational.sat_constraints_iff_children`
- `Operational.forestStep_sat_iff`
- `Operational.ForestReach.sat_iff`
- `Operational.ForestReach.atomicAcc`
- `Operational.no_forestStep_iff_terminal`
- `Operational.exists_terminal_reachable`
- `Operational.terminal_reachable_closed_iff_unsat`
- `Operational.terminal_reachable_closed_iff_closes`
- `Operational.terminal_reachable_open_countermodel`
- `Operational.terminal_outputs_agree`

## Verification gate

Promotion of Definition 3.80 and Theorem 4.33 to `[VERIFIED]` requires a full
`lake build`, proof-hole and axiom scans, docs--Lean synchronization, regenerated claim
ledger, banned-word and whitespace checks, and an updated manuscript artifact.

**Gate outcome (2026-08-13): passed.** The supporting declarations named above remain
covered by the release source/axiom scans, docs--Lean synchronization gate, full build,
manuscript compilation, and rendered-page inspection.
