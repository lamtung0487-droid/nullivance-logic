# DR-0027 — Recognition, observation loss, and extension criteria

Date: 2026-09-06

## Why this branch of research

The user asks whether NPL can develop into a full logic of recognition.
Before inventing additional dynamics, determine precisely what its current
observation interface permits. This increment supplies an optional formal
specification layer in `Nullivance/Recognition.lean`. It imports Generative;
the existing semantic/proof core does not import it. No original axiom,
connective, threshold rule, or equality algorithm is changed.

## What recognition means here

For states S, observations O, an observation map and a predicate P on states,
`Recognizable observe P` means some decoder from O to Prop recovers P exactly.
This is information-theoretic in the elementary sense of distinguishability,
not a Shannon-entropy claim. A Prop-valued decoder's mathematical existence
does not imply computability, finite observation time, learnability, reliability
under noise, or a theory of consciousness.

The proved necessary-and-sufficient criterion is that P be constant on each
class of states having identical observations. Postprocessing cannot repair
a distinction already erased by observation. Adding observations preserves
existing recognizability. A family of tests supports recognition exactly when
every pair disagreeing on P is separated by at least one test. The whole test
signature may be infinite; a finite terminating selection algorithm is not
supplied by this theorem.

## Stronger result for the existing alpha/Theta layer

For EVERY admitted GenFrame (not merely the canonical example), take channels
with alpha=0 and structure constantly zero, versus channels with alpha=0 and
neutral structure. The positive structure dimension guarantees those structures
are different. Use the respective channel twice in each state.

The first state is quasivant, the second is not, and both initialize to (0,0).
`every_frame_silent_ambiguity` proves this uniformly. Consequently no exact
quasivance decoder exists from init alone for any admitted frame, and no
postprocessing of init can provide one. Replacing the stability function while
retaining the current multiplicative interface does not remove this example.

This refutes the proposed capability of universal latent-quasivance recovery
from the current two-coordinate interface, NOT the consistency or correctness
of the core logic. It is not a claim that latent structure cannot exist.

## Time and interaction

Define observation-stable dynamics: equal present observations always lead to
equal next observations. This holds exactly when a deterministic next-observation
rule can be defined from the current observation (an existence proof using
choice, not an implementation). Induction proves that such dynamics preserve
indistinguishability at every time. Even an entire infinite observation trace
then cannot recover a predicate that differed between the initial states.

Applied to the generative layer, simply appending time does not recover
quasivance under that stability condition. It remains possible for dynamics or
interventions to expose additional state information when the condition fails.
A constructive Bool-pair example observes the first coordinate and then swaps
coordinates: the hidden second bit is not initially recognizable but becomes
recognizable after the interaction. This is an example, not alpha/Theta dynamics
and not evidence for biological recognition.

## Proposed knowledge layer (kept distinct from evidence)

`Known observe P s` means P holds in EVERY state compatible with the observation
at s. The actual state is one such state, so knowledge in this definition is
factive and cannot contain both P and not-P. Additional true observations
preserve knowledge. Recognition of P is equivalent to this knowledge operator
recovering P at every state.

This proposed operator uses ordinary Prop as a specification. It must not be
identified with NPL's four-valued evidence support: conflicting reports may
support both sides, whereas factive knowledge cannot. No embedding theorem
between this operator and the four-valued consequence relation is claimed.

## Verification protocol

From `Nullivance/`:

```text
lake build
lake env lean RecognitionValidation.lean
lake env lean ResearchValidation.lean
```

The dedicated validation file audits sixteen structural results and prints all
four toy states' observations before/after interaction. Native numerical proofs
are not used in this module.

Validation completed: full build passed (2040 jobs); both audit entry points
passed. The sixteen recognition results use only the standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`, or subsets (six audited declarations
are axiom-free). The four toy outputs match the observation/swap definitions.
Earlier equality regression outputs remain unchanged. No proof holes or custom
axiom declarations occur in the new module. No release/PDF rebuild was performed.

## Conditions for a genuine recognition extension

1. Specify the target of recognition: a property, an identity class, or a whole
   latent state. Whole-state recovery requires stronger distinctions than
   recovering one property.
2. Specify accessible observations and interventions. A decoder may not read
   latent structure that its interface has not supplied.
3. Construct admissible alpha/Theta dynamics or an enriched observation map,
   and prove separation of the target properties; do not assume it.
4. Give executable finite tests where possible; prove termination and exact
   scope, or explicitly state approximation/noise assumptions.
5. Formalize memory, agents, and evidence updates separately. Prove a bridge to
   the existing four-valued logic, retaining the evidence/knowledge distinction.
6. Audit conservativity: existing core formulas and theorems must remain valid
   under the extension in the stated sense.

Verdict: the project can host a precisely specified recognition research layer,
but a complete recognition logic has not been established. Current init alone
provably lacks information needed for one central proposed recognition task.
Novelty relative to recognition/epistemic literature has not been assessed in
this local formalization increment. Equality-partition validity enumeration,
cost proofs, and publication integration remain separate unfinished tasks.
