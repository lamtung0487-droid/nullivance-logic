# DR-0139 — Checkable finite relation certificates for generator traces

2026-11-05; base `67952cd`; Lean `leanprover/lean4:v4.32.1`.

## Claim card

DR-0138 gives a bounded equivalence procedure on finite carriers. Can a
separately supplied list of paired states certify that two generators have
the same entire output trace, without trusting the list or enumerating
the full product carrier? The candidate certificate is a typed finite list,
not a parser for untrusted bytes. The start, transition and mark functions
of both generators are independently supplied. Equality must be decidable
on whole states; neither a digest nor equality of their marks suffices.

The checker requires:

1. The pair of initial states occurs in the list.
2. At every listed pair the two marks agree.
3. The successor pair of every listed pair is also listed.

Duplicates are allowed. Extra unreachable pairs are allowed only if they
also pass both local tests. A Boolean all-test and finite membership
decisions implement these conditions; no infinite quantification runs.

## Soundness, completeness and their different domains

Induction on the number of transitions shows that every synchronized
reachable pair stays in the checked list. The mark condition then proves
equality at every natural index. This proof does **not** assume either
state type finite. A proved reference contact contract therefore transfers
to the candidate, including when the types are infinite but the paired
reachable orbit is finite.

For finite carriers, the format is complete. Let D be the product cardinal.
The canonical certificate lists paired orbit positions 0 through D-1.
Every later paired state equals some one of those states. To prove this,
temporarily mark only that particular later state and apply DR-0137's
first-mark cutoff; changing marks leaves the state trajectory unchanged.
Thus the list contains the start and is successor-closed. If the traces
agree, every mark test also passes. Conversely soundness already proves
trace agreement from acceptance. Existence of any accepted list is therefore
equivalent to acceptance by DR-0138's full equivalence comparison.

The canonical construction is executable, although inefficient: it recomputes
states at each index and can keep duplicates. It demonstrates completeness,
not an optimized certificate producer. Small lists supplied from elsewhere
are checked with the same soundness theorem. No speedup or new counted-cost
bound is claimed here; list membership can entail linear search.

## Adversarial tests and a proved limit

Kernel checks accept singleton and duplicated certificates for two constant
orbits on Nat, despite the infinite carriers. They reject an empty list and
a closed list that omits the true start. A separate regression compares two
initially unmarked starts; one advances to a marked state while the other
stays unmarked. The forged singleton contains the start and agrees on its
marks, but fails closure and is rejected.

Infinite-carrier completeness is **false** for this certificate format.
Compare a generator with itself: start 0, successor n+1, always false marks.
The traces trivially agree. An accepted finite list would contain (n,n) for
every natural n. But each first coordinate in a finite list is at most the
sum of all its first coordinates; choosing n equal to that sum plus one is
a contradiction. This refutes completeness only for finite lists of concrete
pairs, not for symbolic inductive relations, and not for the core logic.

The checker verifies generator-relative trace equivalence, not empirical
validity of either generator or authenticity of measurements. Core semantics
and axioms are unchanged.

## Reproduction

From `Nullivance/`:

    lake env lean Nullivance/RecognitionGeneratorCertificate.lean
    lake build
    lake env lean ResearchValidation.lean
    lake env lean RecognitionValidation.lean

All four commands exited 0 in the C worktree. The direct module check produced
no diagnostics and the build completed 2156 jobs. Eleven new public theorem
audits report only standard `propext`, `Classical.choice`, `Quot.sound`
or subsets. The two finite regressions were checked by kernel evaluation.
The module scan found no proof holes, custom axioms or native decision bridge.
Working-file SHA-256:
`C60A42D11270C41275CC9599BB5E9084F62547A68A81791571B4825DCF55B7A4`.
