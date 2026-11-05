# DR-0140 — Proof-carrying symbolic relations for infinite counter generators

2026-11-05; base `cd87b74`; Lean `leanprover/lean4:v4.32.1`.

## Claim card and representation change

DR-0139's finite lists cannot certify advancing counters, even when their
traces agree. Replace the list by a symbolic predicate R on pairs, together
with Lean proofs that the starts are related, related states have equal
marks, and a synchronized transition preserves R. The universal obligations
are **proof fields**, not a Boolean test over infinitely many pairs.
The generator's original semantics and core axioms are unchanged.

## Soundness and exact semantic scope

Induction keeps every synchronized pair in R and gives equal marks at all
natural indices. A separate fuel induction proves exact equality of bounded
first-hit searches from any related pair, not just the starts. Zero fuel,
success offsets and timeout are preserved; no runtime cost equivalence is
inferred. A reference contact contract transfers by the trace equality law.

Any accepted list from DR-0139 gives such a proof using pair membership as R.
Conversely, arbitrary equal traces admit a symbolic relation: the set of
synchronized pairs reachable after some common number of steps. The start,
output and closure proofs follow directly. This is **semantic existence**,
not a terminating relation synthesizer, finite symbolic syntax, or decidable
test for equivalence on arbitrary generators. It does not contradict
DR-0136's observation-only impossibility result.

## A constructive infinite-state family

The first machine starts at b, adds d each step, and outputs an arbitrary
Boolean predicate mark(n). For a positive natural a, the second starts at
a*b, adds a*d, and outputs mark(n/a). The relation y=a*x is preserved by
the transitions, and at related states division is exact. Thus the proof
applies to all budgets, starts b, strides d (including zero), positive
scales a, and marks. These generators are executable when mark is executable;
their symbolic relation has an explicit arithmetic description.

The nonconstant example uses b=0, d=1, a=2 and the odd-number mark. The
two state sequences are 0,1,2,... and 0,2,4,...; both output
false,true,false,true,... . Kernel evaluation checks the first six marks,
the second machine's first six states, and resumed search from related
states 2 and 4. Universal equivalence comes from the theorem, not these tests.

For every choice of marks and every comparison partner, the first machine
starting at 0 with stride 1 has **no** accepted finite-pair-list certificate:
such a list would contain a pair with every natural first coordinate.
Choose an index larger than the sum of all first coordinates to contradict
finite membership. The symbolic result therefore covers a family that the
previous concrete-list format provably cannot cover.

The positivity assumption is necessary for this family: with a=0 and a mark
true only at 1, the first machine succeeds at offset 1 while the scaled
machine stays at zero and times out. This kernel-checked counterexample is
retained; division by zero is not silently treated as invertible.

## Remaining obligations

This extension consumes proof-carrying relations. It does not automatically
infer them from sample data or validate them using a finite Boolean checker.
A restricted symbolic language with an executable sound checker, its
completeness limits and counted costs remain separate work. No claim about
general cognition, physical measurement accuracy or unrestricted quantified
logical completeness is made.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionSymbolicGeneratorRelation.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 in the C worktree. Direct module check had no
diagnostics; the full build completed 2157 jobs. All eleven public audits
use only standard logical axioms or none. In particular the generic symbolic
orbit, trace, existence equivalence and bounded-scan theorems are axiom-free.
Both regressions use kernel evaluation. The module scan found no proof holes,
custom axioms or native decision bridges. Working-file SHA-256:
`6FF7F2A8DC5297DBAE541424BE8FA14F0BBE814EE17A221B256E712656726377`.
