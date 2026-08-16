# DR-0019 -- Refutation of the head-sensitive replay bridge

Date: 2026-08-13

Status: accepted refutation and scope correction.

## Intent

Decide Conjectures 3.39 and 3.50 without using the already verified semantic shortcut.
The load-bearing question is whether every admissible propositional closure of a replay
trace can be converted into the existing inductive `ReplayClosesCore` certificate.

## Exact statement tested

The strongest natural formalization of Conjecture 3.50 is

```text
forall T,
  ReplayTrace.Admissible T ->
  Closes T.groundBranch ->
  ReplayClosesCore T.
```

The propositional premise is already an inductive constructor proof. The conclusion is
the inductive replay certificate defined in Definition 3.44. This removes the undefined
phrase “constructor-respecting derivation” without weakening the intended bridge.

Conjecture 3.39 named Conjecture 3.50 as its precise trace-level refinement. Its
certificate-level content is therefore decided by the same test. The separate final
implication `Closes (rigidGroundConstraints n ++ groundBranch B) -> QClosesExtCore B`
is not part of the refutation; it remains verified as Theorem 3.75.

## Counterexample

Take `n = 1`, so the domain has two elements. Let `phi = P(x0)`, let `rho0` and `rho1`
be the constant-zero and constant-one assignments, and put

```text
T = [qFoldConjTail T+ [(rho0,phi),(rho1,phi)], q(T-,rho1,phi)].
```

The two grounded predicate atoms are distinct by injectivity of `groundAtomCode`. The
trace is admissible. Its propositional projection is

```text
[T+(p0 and (p1 and top)), T-p1].
```

Two `conjTpos` steps expose `T+p1`, after which `closeT` closes the branch.

Inverting a hypothetical `ReplayClosesCore T` forces the head-fold constructor
`qFoldConjTposCons`. Its child trace begins with atomic `q(T+,rho0,phi)`, followed by the
residual fold and `q(T-,rho1,phi)`. No fold constructor can act because the residual fold
is not the head; no formula constructor can act on the atomic first item. The only
remaining close constructor would equate the distinct ground atoms `p0` and `p1`.
Therefore the child certificate, and hence `ReplayClosesCore T`, cannot exist.

## Refutation-first stress tests

- **Empty tail:** already refuted the merely well-formed bridge in Proposition 3.46 but
  was excluded by admissibility; it did not decide Conjecture 3.50.
- **Nonempty tail:** the new witness has two elements and satisfies admissibility.
- **Head position:** the structured fold is initially the head, so the failure is not
  caused by an arbitrary leading rigid item.
- **Canonical derivation:** the ground proof uses only the intended fold decomposition
  constructors and an atomic close pair; no macro constructor occurs.
- **Domain size one:** a one-element fold has no nontrivial residual item before the
  closing target, so it does not expose this obstruction. Domain size two is minimal.
- **Semantic consequence:** Theorem 3.77 still yields core closure of the quantified
  projection. The failure is intensional certificate reconstruction, not soundness or
  semantic completeness.

## Repair candidates

### Candidate A -- Focused/reachable trace states

Add an explicit cursor or zipper and quantify only over traces reachable from an initial
quantified branch by certified replay transitions. This preserves the head-sensitive
certificate but requires a new reachability invariant and proof that every ground
constructor can update the focus. The present counterexample shows that admissibility
alone cannot serve as that invariant.

### Candidate B -- Membership-based residual-fold constructors

Replace or extend the head-only fold constructors with rules that select a structured
fold occurrence by membership, as the quantified-formula constructors already do. This
repairs the counterexample and makes the certificate insensitive to irrelevant trace
prefixes. It changes Definition 3.44 and therefore requires an R4 impact audit and new
soundness and completeness proofs.

### Candidate C -- Binary quantified target calculus

Introduce a core target whose quantifier rules decompose one instance plus a residual
tail, matching propositional `foldConj` and `foldDisj` literally. Then prove equivalence
with `QClosesExtCore`. This gives the closest derivation-by-derivation correspondence but
adds the largest proof-theoretic layer.

## Decision

Do not alter a core definition merely to rescue a false conjecture. Record Conjectures
3.39 and 3.50 as `[REFUTED]`, retain the counterexample, and preserve Theorems 3.74,
3.75, and 3.77. Candidate B is the recommended next design experiment because it
targets the exact obstruction with the smallest conceptual extension. DR-0020
subsequently accepts it as the separate `ReplayClosesCoreMem` certificate, proves its
sound projection and the cascade regression, and leaves its universal completeness as
Conjecture 3.84. This does not alter the refutation recorded here because the conclusion
type of Conjecture 3.50 remains `ReplayClosesCore`.

## Impact analysis

- Conjecture 3.50 changes from `[CONJECTURE]` to `[REFUTED]`.
- Conjecture 3.39 changes from `[CONJECTURE]` to `[REFUTED]` for its explicitly intended
  certificate-level reading through Conjecture 3.50.
- Theorem 3.75 remains `[VERIFIED]`; its exact final implication is unaffected.
- Theorem 3.77 remains `[VERIFIED]`; it already states the strongest universal semantic
  bridge supported by the current definitions.
- `ReplayTrace.Admissible`, `ReplayClosesCore`, and all prior verified replay lemmas are
  unchanged, so no verified downstream item reverts status.

## Lean evidence

- `FiniteFO.replayCascadeTrace_admissible`
- `FiniteFO.replayCascadeGround_ne`
- `FiniteFO.replayCascadeTrace_ground_closes`
- `FiniteFO.replayCascadeTrace_not_replayClosesCore`
- `FiniteFO.admissible_ground_replay_bridge_refuted`

Promotion of the refutation evidence requires a targeted and full `lake build`, source
and axiom scans, docs--Lean synchronization, and claim-ledger regeneration.
