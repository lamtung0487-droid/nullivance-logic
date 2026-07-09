# DR-0013 -- Core extensional tableau and replay trace

Date: 2026-07-07

Status: accepted as the next publication-strengthening layer.

## Intent

Make the finite-domain completeness proof suitable for publication by separating the
macro-rule calculus from a core calculus and by preparing a proof state capable of
replaying propositional tableau constructors through grounded finite quantifiers.

## Change

Add `QClosesExtCore`, the extensional finite-domain tableau without the two macro
constructors:

- no `propSim`;
- no `rigidPropSim`.

The core keeps the equality-completed base closure, ground-extensional closure, all
propositional decomposition rules, and all finite-quantifier rules.

Add `ReplayItem` and `ReplayTrace`. A trace item may be:

- a quantified signed formula;
- a rigid propositional signed formula;
- a residual `foldConj` tail;
- a residual `foldDisj` tail.
- a structured residual `foldConj` tail carrying assignment/formula pairs;
- a structured residual `foldDisj` tail carrying assignment/formula pairs.

The residual fold-tail cases are needed because propositional decomposition of grounded
finite quantifiers creates intermediate formulas that are not groundings of single
quantified formulas. The structured residual cases retain enough finite-domain data to
project a residual fold back to the corresponding quantified instance branch.

## Candidates considered

1. **Replay theorem targeting `QClosesExt`.** Rejected for publication value. The theorem
   is discharged by the existing macro constructor `rigidPropSim`, so it does not show
   constructor replay.

2. **Replay theorem targeting only `QBranch`.** Rejected as too small. It cannot record
   partially decomposed finite conjunction/disjunction folds produced by grounded
   quantifiers.

3. **Core calculus plus replay trace.** Accepted. It blocks the macro-rule shortcut and
   adds explicit state for residual fold tails.

4. **Core calculus plus fold-block lemmas only.** Still viable as an alternative final
   proof style. It may be shorter on paper, but the trace layer is the more literal
   constructor-by-constructor target.

## Stress tests

- **Equality reflexivity:** still closes in `QClosesExtCore` through the
  equality-completed base.
- **Quantified equality reflexivity:** still closes in `QClosesExtCore` through the
  equality-completed base.
- **Predicate extensionality:** closes in `QClosesExtCore` through the ground-extensional
  closure clause, without macro rules.
- **Macro shortcut:** unavailable in `QClosesExtCore` by construction.
- **Residual fold tails:** representable by `ReplayItem.foldConjTail` and
  `ReplayItem.foldDisjTail`; structured finite-domain tails are represented by
  `ReplayItem.qFoldConjTail` and `ReplayItem.qFoldDisjTail`.
- **Rigid-only closure:** impossible for well-formed rigid constraints; Lean proves
  `rigidGroundConstraints_no_closeT` and `rigidGroundConstraints_no_closeF`.
- **Rigid equality replay:** verified for all four equality signs against matching
  rigid equality atoms.
- **Branch extension:** verified for `QCloses`, `QClosesEq`, and `QClosesExtCore`.
  Adding formulas to a closed branch preserves closure.
- **Structured fold-tail replay:** verified for the sign-split head/tail cases needed
  for constructor replay. A uniform empty-tail theorem is rejected because false signed
  ground constants can close propositionally against rigid constraints while projecting
  to no quantified item.
- **Admissible replay closure:** verified that every `ReplayClosesCore` certificate
  projects to `QClosesExtCore`. This isolates the remaining bridge from arbitrary
  propositional closure to admissible replay certificates.
- **Arbitrary ground-to-replay bridge:** refuted. A well-formed trace with an empty
  `T-` conjunction tail plus rigid constraints propositionally closes, but cannot have
  a `ReplayClosesCore` certificate because its quantified projection is empty.
- **Admissible replay invariant:** added to exclude unstructured fold tails and the bad
  empty structured tails while preserving rigid well-formedness. The Prop 3.46
  counterexample is not admissible.
- **Fold-tail membership projection:** verified that a structured q-fold tail occurring
  anywhere in a trace contributes its projected quantified tail branch to the full
  `qBranch` of the trace.
- **Membership-based fold-tail replay:** verified the eight structured fold-tail replay
  cases without requiring the fold-tail item to be the head of the trace.
- **Matching fold-tail close replay:** verified the four close-pair cases where both
  sources are structured q-fold tails of the same fold connective and opposite close
  signs.
- **Quantifier-to-fold all-child close replay:** verified the four mixed q-vs-fold close
  cases where the quantified side uses an all-child finite-domain rule.
- **Generated q-fold alignment invariant:** added `HasQInstBlock`, recording that the
  trace projection already contains every finite instance of a quantified formula.
- **Generated quantifier-to-fold branching replay:** verified the four mixed q-vs-fold
  close cases where the quantified side uses a branching finite-domain rule, under the
  generated q-fold alignment invariant.
- **Generated source inversion:** added a generated source classifier whose structured
  q-fold constructors recover the correct generated q-fold certificate for any matching
  quantified grounding.
- **Generated close-pair inversion:** verified that under admissibility and
  `GeneratedForGround`, any grounded T-close or F-close pair has a generated
  close-pair source classification. This packages Prop 3.65 at the pair level for the
  bridge theorem.
- **Rigid-versus-fold exclusion:** verified that every rigid-source versus structured
  q-fold source close-pair combination is impossible under admissibility. Empty
  fold-tail identities were checked separately against the rigid top/bottom signs.
- **Cross-fold exclusion:** verified that conjunction-fold and disjunction-fold sources
  cannot form a T-close or F-close pair. Empty fold identities reduce to distinct
  top/bottom atoms.
- **Nonmatching q-versus-fold shortcut refuted:** Lean exhibits q-formulas whose outer
  constructor is not the matching quantifier but whose grounding is still a fold. The
  dispatcher must therefore use recursive q-versus-fold replay, not only impossible
  source cases.
- **Recursive q-versus-fold replay steps:** verified the first head/tail replay layer
  for nonmatching conjunction/disjunction q-sources. Non-branching signs close against
  the fold head immediately; branching signs close the left child and expose the
  right-child tail obligation.

## Impact analysis

New items:

- Def 3.36 core extensional finite-domain tableau `[DRAFT]`;
- Prop 3.37 core embeds in the macro calculus `[VERIFIED]`;
- Def 3.38 replay trace with residual fold tails `[DRAFT]`;
- Conj 3.39 constructor replay into the core calculus `[CONJECTURE]`;
- Prop 3.40 local replay rules for quantified trace items `[VERIFIED]`;
- Prop 3.41 rigid equality replay facts `[VERIFIED]`;
- Prop 3.42 monotonicity of quantified core closure `[VERIFIED]`;
- Prop 3.43 structured fold-tail replay facts `[VERIFIED]`;
- Def 3.44 admissible core replay closure `[DRAFT]`;
- Prop 3.45 soundness of admissible core replay closure `[VERIFIED]`;
- Prop 3.46 arbitrary ground-to-replay bridge fails `[REFUTED]`;
- Def 3.47 admissible replay trace invariant `[DRAFT]`;
- Prop 3.48 admissibility sanity facts `[VERIFIED]`;
- Prop 3.49 neutral empty-tail replay constructors `[VERIFIED]`;
- Conj 3.50 admissible ground-to-replay bridge `[CONJECTURE]`;
- Def 3.51 replay ground source `[DRAFT]`;
- Prop 3.52 ground-branch membership inversion `[VERIFIED]`;
- Def 3.53 replay close-pair sources `[DRAFT]`;
- Prop 3.54 close-pair membership inversion `[VERIFIED]`;
- Prop 3.55 immediate close-pair replay cases `[VERIFIED]`;
- Prop 3.56 quantified equality versus rigid equality close cases `[VERIFIED]`;
- Prop 3.57 branching fold-tail nonemptiness `[VERIFIED]`;
- Prop 3.58 fold-tail membership projection `[VERIFIED]`;
- Prop 3.59 membership-based structured fold-tail replay `[VERIFIED]`;
- Prop 3.60 structured fold-tail close replay for matching fold cases `[VERIFIED]`;
- Prop 3.61 quantifier-to-fold close replay for all-child signs `[VERIFIED]`;
- Def 3.62 generated q-fold alignment invariant `[DRAFT]`;
- Prop 3.63 generated quantifier-to-fold close replay for branching signs `[VERIFIED]`;
- Def 3.64 generated replay ground source `[DRAFT]`;
- Prop 3.65 generated source inversion `[VERIFIED]`;
- Def 3.66 generated replay close-pair sources `[DRAFT]`;
- Prop 3.67 generated close-pair inversion `[VERIFIED]`;
- Prop 3.68 rigid-versus-fold close-pair exclusion `[VERIFIED]`;
- Prop 3.69 cross-fold close-pair exclusion `[VERIFIED]`;
- Prop 3.70 nonmatching q-versus-fold exclusion fails `[REFUTED]`;
- Prop 3.71 recursive q-versus-fold replay steps `[VERIFIED]`;
- Prop 3.72 suffix-aligned tail consumer `[VERIFIED]` (2026-07-08): the four branching
  sign pairs now close outright for every q-formula aligned with any suffix of a
  structured fold tail — the recursive fold-tail replay theorem the previous
  follow-up asked for. No admissibility hypothesis; helpers `foldConj_inj`,
  `foldDisj_inj`, `ground_all/ex_mem_qTailGround_of_eq`;
- Prop 3.73 close-pair dispatcher `[VERIFIED]` (2026-07-09): all sixteen source
  combinations per close sign dispatch from a **plain** admissible close pair to
  `QClosesExtCore`. Design consequence: the generated certificate layer
  (Def 3.62/3.64/3.66, Props 3.63/3.65/3.67) is no longer on the critical path —
  Prop 3.72's fold-chain alignment replaced the instance-block invariant. The
  closure cases of Conj 3.50/3.39 are done.

Updated items:

- DR-0012's publication follow-up is refined: the replay theorem must target the core
  calculus or an audited proof that excludes macro constructors.

Open follow-up:

- Dispatch the generated close-pair source combinations. The already verified ordinary
  q/q, quantified equality vs rigid equality, matching fold/fold, q-vs-fold all-child,
  and q-vs-fold branching lemmas should be reused through the generated-to-ordinary
  forgetful maps and generated q-fold certificates.
- Complete or prove impossible the remaining close-pair replay cases involving
- ~~Lift the verified q-versus-fold replay steps into a recursive fold-tail replay
  theorem that consumes the tail obligation~~ — **done 2026-07-08, Prop 3.72**
  (`*_tailConsume_core`, with `suffix = full` dispatcher entry points
  `*_tailConsume_full_core`). Remaining: plug the entry points into the generated
  close-pair dispatcher. Rigid-vs-fold and conjunction-vs-disjunction cross-fold source
  pairs are now excluded.
- ~~Dispatch the generated close-pair source combinations~~ — **done 2026-07-09,
  Prop 3.73**, and with a simplification: plain sources suffice, no generated
  invariant is consumed.
- ~~Define any remaining generated-trace invariant needed by those fold-tail source
  cases~~ — **obsolete**: Prop 3.72/3.73 eliminated the need for generated-trace
  invariants in the dispatcher.
- Prove Conj 3.39 without invoking `propSim` or `rigidPropSim`. **Route revision
  (2026-07-09):** the derivation-by-derivation simulation hits a real obstruction at
  branching-sign quantifier groundings (binary propositional cascade versus the
  core's `(n+1)`-ary quantifier rules; see the Conj 3.50 progress note). Recommended
  route: prove semantic completeness of the core calculus directly —
  `unsatisfiable-in-finite-models ⟹ QClosesExtCore` — by mirroring
  `Metatheory.closes_todo` at the quantified level with the domain-weighted measure
  `qweight(∀xφ) = 1 + (n+1)·qweight(φ)`; every core rule strictly decreases todo
  weight, fold tails never arise, and the closure/literal stage uses the ground
  canonical model plus the equality and extensional closure clauses. Conj 3.39's
  final statement then follows via Thm 4.13's semantic transfer.
- Revisit Thm 3.35 after the core completeness lands: finite-domain completeness can
  be restated with `QClosesExtCore` as the proof-theoretic target.

## Verification

Lean module build:

- `lake build Nullivance.FiniteFO`
- date: 2026-07-08 (Prop 3.72 pass; previous pass 2026-07-07)
- result: success, 912 jobs; full `lake build` success, 2001 jobs; axiom audit of the
  Prop 3.72 declarations: only `propext`, `Classical.choice`, `Quot.sound`

Key Lean names:

- `FiniteFO.QClosesExtCore`
- `FiniteFO.QDerivesExtCore`
- `FiniteFO.QClosesExtCore.toExt`
- `FiniteFO.QDerivesExtCore.toExt`
- `FiniteFO.QClosesExtCore.unsat`
- `FiniteFO.qeqRefl0_derivable_core`
- `FiniteFO.qforallEqRefl0_derivable_core`
- `FiniteFO.qpred_extensionality_derivable_core`
- `FiniteFO.ReplayItem`
- `FiniteFO.ReplayTrace`
- `FiniteFO.ReplayTrace.groundBranch_ofQBranch`
- `FiniteFO.ReplayTrace.qBranch_ofQBranch`
- `FiniteFO.ReplayTrace.mem_qBranch_of_mem_q`
- `FiniteFO.ReplayTrace.replay_negTpos_core`
- `FiniteFO.ReplayTrace.replay_conjTpos_core`
- `FiniteFO.ReplayTrace.replay_disjTpos_core`
- `FiniteFO.ReplayTrace.replay_oplusTpos_core`
- `FiniteFO.ReplayTrace.replay_allTpos_core`
- `FiniteFO.ReplayTrace.replay_exTpos_core`
- `FiniteFO.ReplayTrace.WF_ofRigidConstraints`
- `FiniteFO.rigidGroundConstraints_no_closeT`
- `FiniteFO.rigidGroundConstraints_no_closeF`
- `FiniteFO.ReplayTrace.replay_eqTneg_rigidTpos_core`
- `FiniteFO.ReplayTrace.replay_eqFneg_rigidFpos_core`
- `FiniteFO.QCloses.mono`
- `FiniteFO.QClosesEq.mono`
- `FiniteFO.QClosesExtCore.mono`
- `FiniteFO.ReplayTrace.replay_qFoldConjTpos_cons_core`
- `FiniteFO.ReplayTrace.replay_qFoldConjFneg_cons_core`
- `FiniteFO.ReplayTrace.replay_qFoldDisjTneg_cons_core`
- `FiniteFO.ReplayTrace.replay_qFoldDisjFpos_cons_core`
- `FiniteFO.ReplayTrace.replay_qFoldConjTneg_head_core`
- `FiniteFO.ReplayTrace.replay_qFoldConjFpos_head_core`
- `FiniteFO.ReplayTrace.replay_qFoldDisjTpos_head_core`
- `FiniteFO.ReplayTrace.replay_qFoldDisjFneg_head_core`
- `FiniteFO.ReplayTrace.prependQBranch`
- `FiniteFO.ReplayTrace.qBranch_append`
- `FiniteFO.ReplayTrace.qBranch_prependQBranch`
- `FiniteFO.ReplayClosesCore`
- `FiniteFO.ReplayClosesCore.toCore`
- `FiniteFO.replayEmptyBadTailTrace`
- `FiniteFO.replayEmptyBadTailTrace_ground_closes`
- `FiniteFO.replayEmptyBadTailTrace_not_replayClosesCore`
- `FiniteFO.arbitrary_ground_replay_bridge_refuted`
- `FiniteFO.ReplayItem.Admissible`
- `FiniteFO.ReplayTrace.Admissible`
- `FiniteFO.ReplayItem.admissible_wf`
- `FiniteFO.ReplayTrace.Admissible.wf`
- `FiniteFO.replayEmptyBadTailTrace_not_admissible`
- `FiniteFO.ReplayClosesCore.qFoldConjTposNil`
- `FiniteFO.ReplayClosesCore.qFoldConjFnegNil`
- `FiniteFO.ReplayClosesCore.qFoldDisjTnegNil`
- `FiniteFO.ReplayClosesCore.qFoldDisjFposNil`
- `FiniteFO.ReplayGroundSource`
- `FiniteFO.ReplayGroundSource.mem_groundBranch`
- `FiniteFO.ReplayTrace.groundBranch_mem_source`
- `FiniteFO.ReplayTrace.groundBranch_mem_source_iff`
- `FiniteFO.ReplayCloseTPair`
- `FiniteFO.ReplayCloseFPair`
- `FiniteFO.ReplayTrace.closeT_pair_inversion`
- `FiniteFO.ReplayTrace.closeF_pair_inversion`
- `FiniteFO.ReplayTrace.closeT_q_q_core`
- `FiniteFO.ReplayTrace.closeF_q_q_core`
- `FiniteFO.ReplayTrace.closeT_rigid_rigid_false`
- `FiniteFO.ReplayTrace.closeF_rigid_rigid_false`
- `FiniteFO.ReplayTrace.closeT_qEqNeg_rigidTpos_core`
- `FiniteFO.ReplayTrace.closeT_rigidTpos_qEqNeg_core`
- `FiniteFO.ReplayTrace.closeF_qEqPos_rigidFneg_core`
- `FiniteFO.ReplayTrace.closeF_rigidFneg_qEqPos_core`
- `FiniteFO.ReplayTrace.closeT_qEqPos_rigidTneg_core`
- `FiniteFO.ReplayTrace.closeT_rigidTneg_qEqPos_core`
- `FiniteFO.ReplayTrace.closeF_qEqNeg_rigidFpos_core`
- `FiniteFO.ReplayTrace.closeF_rigidFpos_qEqNeg_core`
- `FiniteFO.ReplayItem.admissible_qFoldConjTneg_nonempty`
- `FiniteFO.ReplayItem.admissible_qFoldConjFpos_nonempty`
- `FiniteFO.ReplayItem.admissible_qFoldDisjTpos_nonempty`
- `FiniteFO.ReplayItem.admissible_qFoldDisjFneg_nonempty`
- `FiniteFO.ReplayTrace.admissible_mem_qFoldConjTneg_nonempty`
- `FiniteFO.ReplayTrace.admissible_mem_qFoldConjFpos_nonempty`
- `FiniteFO.ReplayTrace.admissible_mem_qFoldDisjTpos_nonempty`
- `FiniteFO.ReplayTrace.admissible_mem_qFoldDisjFneg_nonempty`
- `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldConj`
- `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj`
- `FiniteFO.ReplayTrace.qFoldConj_cons_branch_subset_of_mem`
- `FiniteFO.ReplayTrace.qFoldDisj_cons_branch_subset_of_mem`
- `FiniteFO.ReplayTrace.qFoldConj_head_branch_subset_of_mem`
- `FiniteFO.ReplayTrace.qFoldDisj_head_branch_subset_of_mem`
- `FiniteFO.ReplayTrace.replay_mem_qFoldConjTpos_cons_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldConjFneg_cons_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldDisjTneg_cons_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldDisjFpos_cons_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldConjTneg_head_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldConjFpos_head_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldDisjTpos_head_core`
- `FiniteFO.ReplayTrace.replay_mem_qFoldDisjFneg_head_core`
- `FiniteFO.foldConj_qTailGround_head_eq_of_eq`
- `FiniteFO.foldDisj_qTailGround_head_eq_of_eq`
- `FiniteFO.ReplayTrace.closeT_qFoldConj_qFoldConj_core`
- `FiniteFO.ReplayTrace.closeF_qFoldConj_qFoldConj_core`
- `FiniteFO.ReplayTrace.closeT_qFoldDisj_qFoldDisj_core`
- `FiniteFO.ReplayTrace.closeF_qFoldDisj_qFoldDisj_core`
- `FiniteFO.ground_all_qTailGround_head_eq_of_eq`
- `FiniteFO.ground_ex_qTailGround_head_eq_of_eq`
- `FiniteFO.ReplayTrace.closeT_qAllTpos_qFoldConjTneg_core`
- `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qAllFneg_core`
- `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qExTneg_core`
- `FiniteFO.ReplayTrace.closeF_qExFpos_qFoldDisjFneg_core`
- `FiniteFO.qinstItems`
- `FiniteFO.qTailBranch_qinstItems`
- `FiniteFO.qinst_mem_qinstAll`
- `FiniteFO.ReplayTrace.HasQInstBlock`
- `FiniteFO.ReplayTrace.GeneratedQFoldConj`
- `FiniteFO.ReplayTrace.GeneratedQFoldDisj`
- `FiniteFO.ReplayTrace.hasQInstBlock_of_mem_qFoldConj_qinstItems`
- `FiniteFO.ReplayTrace.hasQInstBlock_of_mem_qFoldDisj_qinstItems`
- `FiniteFO.ReplayTrace.closeT_qInstBlockTpos_qAllTneg_core`
- `FiniteFO.ReplayTrace.closeF_qAllFpos_qInstBlockFneg_core`
- `FiniteFO.ReplayTrace.closeT_qExTpos_qInstBlockTneg_core`
- `FiniteFO.ReplayTrace.closeF_qInstBlockFpos_qExFneg_core`
- `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generated_core`
- `FiniteFO.ReplayTrace.closeF_qAllFpos_qFoldConjFneg_generated_core`
- `FiniteFO.ReplayTrace.closeT_qExTpos_qFoldDisjTneg_generated_core`
- `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qExFneg_generated_core`
- `FiniteFO.ReplayTrace.closeT_generatedQFoldConjTpos_qAllTneg_core`
- `FiniteFO.ReplayTrace.closeF_qAllFpos_generatedQFoldConjFneg_core`
- `FiniteFO.ReplayTrace.closeT_qExTpos_generatedQFoldDisjTneg_core`
- `FiniteFO.ReplayTrace.closeF_generatedQFoldDisjFpos_qExFneg_core`
- `FiniteFO.ReplayTrace.GeneratedForGround`
- `FiniteFO.ReplayTrace.generatedQFoldConj_of_ground_all`
- `FiniteFO.ReplayTrace.generatedQFoldDisj_of_ground_ex`
- `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generatedForGround_core`
- `FiniteFO.ReplayTrace.closeF_qAllFpos_qFoldConjFneg_generatedForGround_core`
- `FiniteFO.ReplayTrace.closeT_qExTpos_qFoldDisjTneg_generatedForGround_core`
- `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qExFneg_generatedForGround_core`
- `FiniteFO.ReplayGeneratedGroundSource`
- `FiniteFO.ReplayGeneratedGroundSource.mem_groundBranch`
- `FiniteFO.ReplayTrace.groundBranch_mem_generated_source`
- `FiniteFO.ReplayTrace.groundBranch_mem_generated_source_iff`
- `FiniteFO.ReplayGeneratedGroundSource.toSource`
- `FiniteFO.ReplayGeneratedCloseTPair`
- `FiniteFO.ReplayGeneratedCloseFPair`
- `FiniteFO.ReplayGeneratedCloseTPair.toCloseTPair`
- `FiniteFO.ReplayGeneratedCloseFPair.toCloseFPair`
- `FiniteFO.ReplayTrace.generated_closeT_pair_inversion`
- `FiniteFO.ReplayTrace.generated_closeF_pair_inversion`
- `FiniteFO.rigidGroundConstraints_formula_atom`
- `FiniteFO.rigidGroundConstraints_no_Tneg_top`
- `FiniteFO.rigidGroundConstraints_no_Fpos_top`
- `FiniteFO.rigidGroundConstraints_no_Tpos_bot`
- `FiniteFO.rigidGroundConstraints_no_Fneg_bot`
- `FiniteFO.foldConj_cons_ne_atom`
- `FiniteFO.foldDisj_cons_ne_atom`
- `FiniteFO.ReplayTrace.closeT_rigidTpos_qFoldConjTneg_false`
- `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_rigidTneg_false`
- `FiniteFO.ReplayTrace.closeT_rigidTpos_qFoldDisjTneg_false`
- `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_rigidTneg_false`
- `FiniteFO.ReplayTrace.closeF_rigidFpos_qFoldConjFneg_false`
- `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_rigidFneg_false`
- `FiniteFO.ReplayTrace.closeF_rigidFpos_qFoldDisjFneg_false`
- `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_rigidFneg_false`
- `FiniteFO.groundTop_atom_ne_groundBot_atom`
- `FiniteFO.foldConj_ne_foldDisj_of_nonempty_left`
- `FiniteFO.foldDisj_ne_foldConj_of_nonempty_left`
- `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qFoldDisjTneg_false`
- `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qFoldConjTneg_false`
- `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qFoldDisjFneg_false`
- `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qFoldConjFneg_false`
- `FiniteFO.qVsFoldShapeCounterAssignment`
- `FiniteFO.qVsFoldShapeCounterItems`
- `FiniteFO.q_vs_fold_conj_nonmatching_shape_counterexample`
- `FiniteFO.q_vs_fold_disj_nonmatching_shape_counterexample`
- `FiniteFO.ReplayTrace.closeT_qConjTpos_qFoldConjTneg_core`
- `FiniteFO.ReplayTrace.closeF_qFoldConjFpos_qConjFneg_core`
- `FiniteFO.ReplayTrace.closeT_qFoldDisjTpos_qDisjTneg_core`
- `FiniteFO.ReplayTrace.closeF_qDisjFpos_qFoldDisjFneg_core`
- `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qConjTneg_step_core`
- `FiniteFO.ReplayTrace.closeF_qConjFpos_qFoldConjFneg_step_core`
- `FiniteFO.ReplayTrace.closeT_qDisjTpos_qFoldDisjTneg_step_core`
- `FiniteFO.ReplayTrace.closeF_qFoldDisjFpos_qDisjFneg_step_core`
