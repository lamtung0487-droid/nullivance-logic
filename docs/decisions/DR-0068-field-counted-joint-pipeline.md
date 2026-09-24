# DR-0068 — Thread field-level cursor charges through the joint pipeline

Date: 2026-09-24. Base: 98a334a. Status: [VERIFIED] for the scoped declarations.

## Claim card and adversarial cases

Question: can DR-0067's decomposed cursor-validation charges be carried through
the complete checked continuation and paired certificate export, while
preserving the result and the two previous counters? Input: a probe stream,
possibly stale saved cursor, and finite fuel. Target: exact certificate
erasure, exact agreement with DR-0066's order and certificate-index counters,
and a joint upper budget. Cases: stale cursor, zero fuel, accepted timeout,
tested success, and source mismatch. No hidden-state assumptions are added.

## Algorithm and proof

`fieldCountedJoint` validates the actual prefix summary with DR-0067's
field-level comparator, then uses the existing counted search and shared
paired export on acceptance. Rejection returns no certificates and no export;
an accepted timeout retains the existing empty certificate pair.

`fieldCountedJoint_erasure` proves identical output to
`checkedJointCertificates` for every input. `fieldCountedJoint_old_counts`
proves exact equality of rational-*order* and certificate-index counters with
`sharedCountedJoint`, not merely equality of results. The new joint bound is:

* rational-order nodes: at most `8*c.next + 24*fuel + 16`;
* rational-equality charged nodes: at most 48;
* source-presence tests: exactly 8;
* source-index-equality charged nodes: at most 8;
* certificate-index equality nodes: at most 7.

The final four field/certificate bounds apply to the one validation and at
most one final export in this invocation, including rejected and timeout
branches. The equality charges remain DR-0067's pessimistic abstract budget:
they do not claim actual short-circuit executions or bit complexity. The
previous opaque whole-box equality call is replaced by the explicit field
charges in this new pipeline; the old interface remains untouched.

Kernel regressions cover accepted zero fuel, stale-cursor rejection, one-step
timeout, and a two-step successful search. Semantic soundness of the exported
certificate is inherited through exact erasure to the checked joint reference,
whose original occurrence-index and matching-state hypotheses remain intact.

## Reproduction and remaining limit

In `Nullivance/` under pinned Lean 4.32.1, run `lake build`,
`lake env lean ResearchValidation.lean`, and
`lake env lean RecognitionValidation.lean`; inspect the four new axiom audits
and scan the modified module for proof holes. This is an algorithmic cost
refinement, not recognition of every latent state. Next, if actual operation
complexity is desired, instrument short-circuit branches and rational record
equality or supply a representation-aware bit-cost model. No claim about
elapsed-time speedups is made.
