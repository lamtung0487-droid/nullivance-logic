# Claim-to-proof and scope review — DR-0149 snapshot

Editorial revision: DR0149-r3, 2026-11-09. Original review: 2026-11-08. Mathematical baseline:
`48bd5f4260fd7982176d7a2060be4e956e1fd49c`.

This is an internal artifact/prose audit, **not external academic peer review**.
No claim of exhaustive novelty assessment or complete recognition theory follows.
The review reads definitions, theorem signatures and relevant proof bodies,
checks their use in the prose, then resolves and audits all explicit manuscript
anchors in Lean. Mechanical anchor validation alone would not establish semantic
agreement. The historical design records are provenance, not automatically
validated prose or a list of 149 independently novel theorems.

## Scope matrix

All names below occur under `Nullivance`; the generated publication audit prints
the full qualified types and axiom dependencies. The manuscript prints the exact
qualified anchor beside each main mathematical statement.

| Manuscript topic | Formal evidence / source | Hypotheses preserved and excluded overclaim |
|---|---|---|
| Exact threshold projection | `Continuous.exact_projection` | Finite syntax, min/max/swap; not commuting arbitrary infinite suprema. |
| Signed tableaux | `Metatheory.Closes.unsat`, `closes_of_unsat`, `derives_iff_consequenceC` | Signed consequence; infinite propositional premise sets are not infinite quantified domains. |
| Finite quantified calculus | `FiniteFO.qDerivesExtCore_iff_qconsequence4Sig` | Signature well-formedness of branch and conclusion; fixed finite-domain language. Failed replay conjectures are not premises. |
| Infinite/finite equality | `InfiniteFO.decideQuantifiedEqualityHashed_*_correct` | Closed quantified-equality fragment; infinite/nonempty or finite/nonempty carrier as stated. No arbitrary predicates. |
| Open equality | `decideFiniteOpenEquality_correct`, `checkedFiniteOpenEquality_sound`, `decideFreshCompactOpenEquality_finite_capacity_correct` | Supplied assignment, enumeration/fragment conditions, or rank-plus-named-class capacity. Not all-assignment validity. |
| Unique cache states | `runQuantifiedEqualityOrbitHashed_unique_states_eq_misses`, `*_syntax_mul_bell`, `*_syntax_mul_factorial` | Empty-root run; rank specialization for syntax envelope. State count is not runtime. |
| Hash costs | `runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds` | Instrumented pinned implementation; request and table-size counters. Does not assume expected constant-time collision resolution or charge key bit cost. |
| Generative interface | `Generative.GenState.init_mem`; `Recognition.every_frame_silent_ambiguity` | Positive dimension, admissible stability map. Quasivance means both zero-intensity, nonneutral channels; converse of effective silence is false. |
| Fiber recognition | `recognizable_iff_fiber_constant` | Prop-valued decoder existence; not executable for arbitrary properties. |
| Time / intervention | `stable_evolution_indistinguishable`, `activeProbeSignature_eq`, `activeProbeSignature_injective` | Negative result assumes observational stability. Positive scalar probes are proposed interventions on separate copies; not physical experiments. |
| Knowledge bridge | `truthSupport_known_of_adequate`, `bothSupport_no_unconditional_knowledge` | Report adequacy and fiber constancy; B remains permitted evidence, not contradictory factive knowledge. |
| Finite histories | `summarizeProbes_exact`, `historyFeasible_iff_exists`, `classifyHistory_complete` | One fixed scalar state, independent coordinate bounds, exact rationals. Invalid is not vacuous affirmation. |
| Actual witnesses | `boxWitnessCandidates_represent`, `exportHistoryWitness_realizes` | 81 candidate entries preserve the specific equality tests for quasivance, not arbitrary continuum properties. Membership and unit bounds are checked. |
| Infinite compatibility | `stream_exists_iff_all_prefixes_feasible`, `stream_exists_iff_pairwise_feasible` | Closed rectangular constraints; coordinate suprema explicitly bounded/nonempty. Not finite certification of every property. |
| Small conflict certificates | `stream_infeasible_iff_two_observation_certificate`, `two_observation_bound_is_sharp` | At most two records, possibly the same index. No waiting-time bound follows. |
| Sourced memory import | `importTrusted_isSome`, `importTrusted_output`, `importTrustedCounted_spec` | Reconstructed canonical prefix summary, fixed stream. Exactly 8n rational-order nodes and one box-equality call, not one primitive comparison or cryptographic authenticity. |
| Finite digest obstruction | `finite_digest_cannot_justify_import` | Universal exact equality inference from an arbitrary finite digest is impossible; not a cryptographic-security theorem. |
| Byte envelope | `decodeCursorEnvelope_encode`, `restoreActiveEnvelopeCounted_success` | Size/canonical encoding and subsequent semantic checking; decoding alone does not authenticate source data. |
| Threshold cache check | `checkThresholdCache_spec`, `checkThresholdCacheCounted_accepted`, `checked_cache_nonrealizable_counterexample` | Equality to rebuilt cache, not equality of whole histories or realizability. List/tag inspections plus fixed Boolean-gate costs differ from rational comparison counts. |
| Threshold information | `finite_positive_thresholds_not_recognizable`, `countableThreshold_recognizes_quasivance` | Unrestricted scalar states, positive finite thresholds versus entire countable signature; no finite zero-recognition algorithm inferred. |
| Adaptive resolution | `separated_stream_adaptive_resolution` | Common fitting state, precision delivery, finite positive thresholds strictly separated from max intensity. Margin absent from executable inputs but present existentially in the proof. |
| Compact replay | `compactReplay_extension`, `bootSources_bound`, `bootSources_eight_attained`, `no_bootSummary_history_inverse` | In-order chunks, correct stream extension, fixed requests/fuel. At most eight source slots is representation-specific, not universal memory lower bound; summary is not an archive. |
| Exact boundary | `boundary_ready_iff_contact`, `boundary_contact_or_alternative`, `centeredBoundary_timeout` | Positive threshold equals the fitting state's max intensity. A below alternative may depend on the prefix. Precision alone does not guarantee finite stopping. |
| Cycle setup | `compareResidueCycles_exact`, `euclidCounted_log_bound`, `preparedCycleWork_log_bound`, `guardedCycles_result` | Explicit residue counters and counted Euclid; logarithmic step count, not logarithmic bit runtime. |
| Unknown periodicity | `periodicQuery_admissible_collision`, `no_finite_negative_periodic_recognizer` | Deterministic observation-only adaptive queries, no supplied description/bound. Counterexamples retain common state and precision. Not all program-analysis or randomized models. |
| Certified period bound | `contactPeriodBound_cutoff`, `scanObservedContact_permanent` | Positive period P <= B of the contact predicate at all indices. Promise is not learned from finite samples. |
| Recognition bridge / costs | `scanObservedContact_boundary`, `scanObservedContact_first_prefix`, `scanObservedContactCounted_exact`, `scanObservedContactCounted_boundary` | StreamFits, positive equality threshold; exact (k+1,k) or (B,B). Includes final failing transition; excludes sample production and rational bit cost. |
| Sharpness | `scanObservedContact_cutoff_sharp`, `contactPeriodBound_positive` | Leading-prefix bound only; B=0 cannot have the promise. Not a bounded adaptive-query lower bound. |

## Corrections made during this audit

1. Two initially misqualified core anchors were corrected to the **Metatheory**
   namespace; the final audit must pass, not merely suppress the errors.
2. The HashMap amortized-operation theorem has no closed-fragment hypotheses;
   those belong to semantic correctness, while rank is used for the syntax
   envelope. The prose now separates these statements.
3. Active probes now explicitly operate on independent copies of the original
   scalar state and assume proposed intervention access.
4. The manuscript now distinguishes three notions of memory agreement:
   numerical cache equality, a sourced prefix invariant, and lossless equality
   of original histories. None silently entails the others.
5. The periodic negative conclusion is explicitly about absence of a finite
   canonical boundary certificate, not lower latent intensity.
6. Correction in r3: the bundled core PDF had changed while retaining the old
   cover label. All current companions now carry DR0149-r3; old online records
   remain unchanged. Version history distinguishes substantive and editorial changes.
7. Visual/text review caught the legacy BibTeX parsing of Belnap's suffix as
   a first name (rendered “Jr. Belnap, Nuel D.”). The new report uses a separate
   bibliography (now eight entries) with `Belnap, Jr., Nuel D.`, protected Lean/Boolean
   capitalization, and clickable DOI notes. Visual review of the companion PDF
   found the same suffix issue in the shared bibliography; r3 fixes that entry
   there as well. The historical online files are unchanged.

## Citations used by the new report

The original five entries below retain their previous metadata checks; the shared legacy bibliography is not claimed to
have been entirely re-audited in this pass. No copied abstract or long quotation
is used. The manuscript makes no priority claim based on this short list.

| Entry | Verification source | Result / limitation |
|---|---|---|
| Belnap 1977, *A Useful Four-Valued Logic* | Springer DOI `10.1007/978-94-010-1161-7_2`, publisher preview | Author, title, collection, 1977 and pp. 5–37 match; preview supports the four independent information states. |
| Dunn 1976, *Intuitive Semantics for First-Degree Entailments and “Coupled Trees”* | Springer DOI `10.1007/BF00373152` | Author/title, Philosophical Studies 29, 149–168 (1976) match. |
| Fitting 1991, *Bilattices and the Semantics of Logic Programming* | Crossref publisher-deposited metadata, `https://api.crossref.org/works/10.1016%2F0743-1066(91)90014-G` | Author/title, journal, volume 11(2), 91–116, 1991 match. Publisher full page was blocked by a challenge; no claim of rereading its full text. |
| Bryant 1986, *Graph-Based Algorithms for Boolean Function Manipulation* | Author-hosted corrected version, `https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf` | Author/title and original IEEE C-35(8), 677–691, August 1986 verified from title-page publication note; supports established ordered/reduced Boolean representations. |
| de Moura and Ullrich 2021, *The Lean 4 Theorem Prover and Programming Language* | Springer DOI `10.1007/978-3-030-79876-5_37` | Authors/title, CADE 28, LNCS 12699, 625–635, 2021 match. |

## Added comparison in r3

- Halpern and Moses (1990), Journal of the ACM 37(3), 549–587:
  author-deposited https://arxiv.org/abs/cs/0006009 and its full HTML, especially
  the local-information interpretation and factivity. Used only to position the
  single-observer compatible-state reading, not to claim a new epistemic paradigm.
- Jaulin and Walter (1993), Automatica 29(4), 1053–1064,
  DOI 10.1016/0005-1098(93)90106-4: author-hosted
  https://www.ensta-bretagne.fr/jaulin/paper_automatica93.pdf, title and introductory
  sections. Supports the bounded-error feasible-set comparison; our coordinatewise
  exact boxes are not a general nonlinear SIVIA algorithm.
- Cousot and Cousot (1977), POPL, 238–252, DOI 10.1145/512950.512973:
  publisher metadata and author-hosted paper
  https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf.
  Cited for the established sound-abstraction methodology, not as a claimed formal
  reduction of this project to their full framework.

The overview now cites eight sources; the companions retain their broader shared
bibliography. This is targeted positioning, not an exhaustive novelty search.
No dated search is promoted to a current first-in-the-literature assertion.

## r3 translation checks

The added introduction separates consequence, state recovery, and finite stopping;
it does not add a theorem about physical cognition. The four new numerical boxes
illustrate `ExactHistoryVerdict`: zero intensity with nonneutral structure,
strictly positive intensity, a box admitting both, and an empty intersection.
They are explanatory arithmetic cases, not a new empirical dataset. The counted
import proof sketch was compared with `RecognitionTrustedImport.lean`: its exact
cost is `(8*c.next, 1)`, including rejection. The bounded-period exposition was
compared with `RecognitionBoundedPeriodObservation.lean`: all-index periodicity is
a supplied proposition, positive-hit correctness does not require it, and a
negative finite search requires it before becoming a permanent negative.

The 149 companion references include definitions as well as theorems; they are
not 149 new results. Both the companion and overview audits print dependency
closures. They supplement, and do not replace, the prose/hypothesis review above.

## Reproduction record

See the packaged `verification/` logs, `audit-inventory.json`, and
`verification-receipt.json` for actual command outcomes and hashes. A cached
dependency build is explicitly distinguished from rebuilding project sources
in an extracted archive. This audit adds documentation/checking scripts only;
the original logic definitions and proofs are unchanged.
