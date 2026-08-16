# Canonical definition–Lean matrix

Date: 2026-08-16

Scope: every numbered definition in the logical core (chapters 1–4). The canonical
wording and epistemic status remain in the owning chapter. This matrix records the exact
Lean representation and any required encoding theorem; it does not independently grant
`[VERIFIED]`.

Evidence classes:

- **literal:** the documented object is the named Lean declaration;
- **equivalent:** Lean uses an intentionally different representation and a named
  theorem proves equivalence;
- **partial/paper:** some documented content has no exact Lean object and therefore
  remains `[PROVEN]`.

## Syntax and semantics

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 1.1 Alphabet | atoms are `Nat`; `Syntax.Formula.atom` | literal |
| 1.2 Formulas | `Syntax.Formula` | literal |
| 1.3 Material conditional | `Syntax.Formula.impl` | literal abbreviation |
| 2.1 Truth-object | `Continuous.SquareTruthObj`; raw `TruthObj` + `InSquare` | equivalent: Thm 2.29; `exists_truthObj_not_inSquare` records strictness |
| 2.2 Model | `Continuous.Model` | literal bundled model; conversions and extensionality in Thm 2.29 |
| 2.3 Valuation | `Continuous.evalSquare`, `Continuous.Model.eval`; raw `evalC` | equivalent: `evalSquare_val`, `Model.eval_val` |
| 2.4 Meta-signs | `Semantics.Sign`, `Sign.opp`, `V4.sat`, `Continuous.SatC`, `Continuous.Model.satSigned` | literal; bundled/raw equality `Model.satSigned_eq_unbundled` |
| 2.5 Unsigned satisfaction; states | `V4.T`, `V4.F`, `V4.B`, `V4.N`, `V4.designated`; `SatC` at `Tpos` | literal |
| 2.6 Consequence | arbitrary sets: `Metatheory.Consequence4Set`, `ConsequenceCSetModel`; finite lists: `Consequence4`, `ConsequenceCModel`; fixed threshold: `ConsequenceCAt` | equivalent raw APIs: `consequenceCModel_iff_consequenceC`, `consequenceCSetModel_iff_consequenceCSet` |
| 2.7 FOUR | `Semantics.V4`, `V4.neg`, `V4.conj`, `V4.disj`, `V4.oplus` | literal |
| 2.8 Threshold projection | `Continuous.proj` | literal |
| 2.19 Finite quantified syntax | `FiniteFO.QFormula` | literal raw syntax |
| 2.20 Finite FOUR model | `FiniteFO.QModel`, `Assignment`, `update` | literal raw model |
| 2.21 Quantified evaluation and satisfaction | `FiniteFO.forallV4`, `existsV4`, `qeval`, `qsat` | literal raw semantics |
| 2.25 Fixed signature and well-formedness | `FiniteFO.QSignature`, `QFormula.WellFormed`, `QSigned.WellFormed`, `QBranch.WellFormed` | literal |
| 2.27 Signature-indexed model and consequence | `FiniteFO.QSigModel`, `QSigModel.eval`, `QSigModel.satSigned`, `QSigModel.satBranch`, `QConsequence4Sig` | literal; raw/signature bridge Thm 2.28 |

## Proof theory

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 3.1 Signed formula | `ProofTheory.SignedFormula`, `sat4` | literal |
| 3.2 Branch; closure | `ProofTheory.Branch`, `satBranch`, `BranchClosed`, `BranchClosed.closes` | literal |
| 3.3 Decomposition rules | sixteen constructors of `ProofTheory.Closes` | literal inductive encoding |
| 3.4 Saturation | none for the full documented Hintikka predicate | partial/paper; `[PROVEN]` |
| 3.5 Tableau; derivability | `ProofTheory.TableauCloses`, `Closes`, `Derives`, `tableauCloses_iff_closes` | equivalent finite-tree/inductive representations; `[VERIFIED]` |
| 3.11 ND calculus | `ProofTheory.ND` | literal |
| 3.14 ⊕-De-Morgan extension | `ProofTheory.NDO` | literal |
| 3.21 Finite quantified tableau | `FiniteFO.QSigned`, `QBranch`, `qinst`, `qinstAll`, `QCloses`, `QDerives`, `QConsequence4` | literal raw calculus |
| 3.25 Equality-completed tableau | `FiniteFO.QClosesEq`, `QDerivesEq` | literal |
| 3.28 Finite grounding bridge | `FiniteFO.GroundAtom`, `groundAtomCode`, `groundVal`, `foldConj`, `foldDisj`, `ground`, `groundSigned`, `groundBranch` | literal |
| 3.30 Full extensional tableau | `FiniteFO.QClosesExt`, `QDerivesExt` | literal |
| 3.34 Rigid ground constraints | `FiniteFO.rigidGroundEqSigns`, `rigidGroundEqConstraints`, `rigidGroundConstraints`, `modelOfGroundVal` | literal |
| 3.36 Core extensional tableau | `FiniteFO.QClosesExtCore`, `QDerivesExtCore` | literal |
| 3.38 Replay trace | `FiniteFO.ReplayItem`, `ReplayTrace`, `qTailSigned`, `qTailBranch`, `qTailGroundForms` | literal |
| 3.44 Admissible core replay closure | `FiniteFO.ReplayClosesCore` | literal |
| 3.47 Admissible replay invariant | `FiniteFO.ReplayItem.Admissible`, `ReplayTrace.Admissible` | literal |
| 3.51 Replay ground source | `FiniteFO.ReplayGroundSource` | literal |
| 3.53 Replay close-pair sources | `FiniteFO.ReplayCloseTPair`, `ReplayCloseFPair` | literal |
| 3.62 Generated q-fold alignment | `FiniteFO.qinstItems`, `ReplayTrace.HasQInstBlock`, `GeneratedQFoldConj`, `GeneratedQFoldDisj` | literal |
| 3.64 Generated replay ground source | `FiniteFO.ReplayGeneratedGroundSource` | literal |
| 3.66 Generated close-pair source | `FiniteFO.ReplayGeneratedCloseTPair`, `ReplayGeneratedCloseFPair` | literal |
| 3.78 Reference search branch and head transition | `Operational.SearchBranch`, `SearchBranch.constraints`, `SearchBranch.Terminal`, `children`, `RefStep`, `SearchBranch.weight` | literal; decrease and well-foundedness in Thm 4.8 |
| 3.79 Reference execution and success | `Operational.run`, `AtomicBranch`, `branchClosedB`, `referenceCloses` | literal; exactness and countermodel bridge in Thm 4.34 |
| 3.80 Progressing forest search and scheduler | `Operational.SearchForest`, `ForestTerminal`, `ForestAtomicAcc`, `ForestClosed`, `ForestSat`, `ForestStep`, `ForestReach`, `ProgressScheduler`, `treeCost`, `forestCost` | literal; well-foundedness, trace invariants, terminal correctness, and schedule independence in Thm 4.33 |
| 3.81 Membership-selecting core replay certificate | `FiniteFO.ReplayClosesCoreMem`, `FiniteFO.ReplayClosesCore.toMem` | literal conservative extension; soundness in Prop 3.82 and regression boundaries in Prop 3.83 |
| 3.84 Universal membership replay bridge | `FiniteFO.admissible_ground_replay_bridge_mem_verified` | exact theorem statement; proved by the conditional reduction of Prop 3.89 instantiated with the full compiler of Prop 3.90 |
| 3.85 Flat replay normal form | `FiniteFO.foldIdentityConstraints`, `FiniteFO.ReplayTrace.rigidProjection`, `flatFor`, `flatBranch` | literal derived projection; contains only four fold identities and rigid items actually present in the trace |
| 3.86 Fold-first membership saturation | `FiniteFO.ReplayTrace.membership_saturation_elim` | continuation form; private finite reach relation mirrors exactly the eight membership constructors |
| 3.87 Flat semantic reduction | `FiniteFO.ReplayTrace.flatBranch_unsat_of_ground_closes`, `flatBranch_closes_of_ground_closes` | literal implication through arbitrary FOUR valuations plus propositional completeness |
| 3.88 Literal flat compiler | `FiniteFO.ReplayTrace.flat_qLits_closes_to_replay` | exact reification of atomic flat close pairs into the old replay certificate |
| 3.89 Flat-compiler reduction | `FiniteFO.ReplayTrace.membership_bridge_of_flat_compiler` | exact conditional reduction of Conj 3.84 |
| 3.90 Full flat replay compiler | `FiniteFO.ReplayTrace.flat_closes_to_replay` | exact compiler premise from Prop 3.89; private `replayFlat_todo` verifies all formula constructors and signs by domain-weighted induction |

## Metatheory

| Definition | Exact Lean representation | Class / bridge |
|---|---|---|
| 4.9 Canonical valuation | `Metatheory.canonicalVal` | literal |

## Audit conclusion

Every `[VERIFIED]` core definition above has an exact declaration or a named
representation-equivalence theorem. Definition 3.4 is the only paper-level core
definition row and remains `[PROVEN]`; no verified theorem depends on an encoded
saturation predicate. M2/WP3 is closed for the deterministic reference scheduler by
Definitions 3.78–3.79 and Theorems 4.8/4.34, and for arbitrary active-branch selection
order by Definition 3.80 and Theorem 4.33. The theorem excludes idle steps; no undefined
fairness notion is represented as verified.

The matrix records representational synchronization, not completeness of every defined
proof object. DR-0019 and the Lean theorem
`FiniteFO.admissible_ground_replay_bridge_refuted` show that the literal
`ReplayClosesCore` mirror is sound but incomplete for admissible ground-closed traces;
the verified semantic bridge of Theorem 3.77 is unaffected. DR-0020 adds the separate
`ReplayClosesCoreMem` mirror, whose soundness and cascade repair are verified. Its
fold-first normalization, flat semantic reduction, literal compiler base, and full
domain-weighted compiler are verified (Propositions 3.86–3.90). Consequently the
universal membership replay bridge is verified as Conjecture 3.84. This does not alter
the refutations of the older, strictly smaller `ReplayClosesCore` certificate claims.
