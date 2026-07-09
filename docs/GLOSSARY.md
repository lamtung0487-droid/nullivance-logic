# Glossary

Single source of truth for nullivance terminology (rule R2). Every technical term used in
`docs/` or `papers/` must have a row here. Keep alphabetical by term.

| Term | Symbol | Defined in | Lean name | One-line meaning |
|---|---|---|---|---|
| Atom (mệnh đề nguyên tử) | p, q, r | Def 1.1 | `Formula.atom : Nat → Formula` | Propositional variable; countably many |
| Assignment, finite-FO | ρ | Def 2.20 | `FiniteFO.Assignment`, `FiniteFO.update` | Maps variables to elements of a finite nonempty domain |
| Admissible core replay closure | — | Def 3.44; Prop 3.45 | `FiniteFO.ReplayClosesCore`, `FiniteFO.ReplayClosesCore.toCore` | Trace-level closure certificate whose every step is verified to project into the macro-free core tableau |
| Admissible replay trace | — | Def 3.47 | `FiniteFO.ReplayTrace.Admissible` | Stronger replay-trace invariant excluding unstructured fold tails and bad empty structured fold tails |
| Arbitrary ground-to-replay bridge | — | Prop 3.46 | `FiniteFO.arbitrary_ground_replay_bridge_refuted` | Refuted bridge claiming every well-formed propositionally closed replay trace has an admissible replay certificate |
| Bare finite-grounding completeness bridge | — | Thm 3.33 | `FiniteFO.qeqRefl0_ground_not_consequence4`, `FiniteFO.qeqRefl0_ground_branch_not_closes` | Refuted proof route from finite-domain semantic consequence directly to ordinary propositional consequence of the grounded formula |
| Branch (nhánh) | B | Def 3.2 | `ProofTheory.Branch` | Finite set (list) of signed formulas in a tableau |
| Canonical valuation (định giá chuẩn tắc) | v_B | Def 4.9 | inside `Metatheory.closes_lits` | Reads positive literals off an open saturated branch |
| Classical corner | T,F | Prop 4.30 | `Metatheory.classicalCorner` | Embedding of Boolean truth values into the FOUR corners `T` and `F` |
| Classical Boolean evaluation | ⊨₂ | Prop 4.30 | `Metatheory.evalBool`, `ConsequenceBool` | Ordinary Boolean evaluation/consequence for the ⊕-free fragment |
| Closure, branch (đóng nhánh) | — | Def 3.2 | `ProofTheory.Closes.closeT/.closeF` | Branch contains a sign and its opposite on the same formula |
| Compactness | — | Thm 4.25; Cor 4.26 | `Metatheory.compactness_satisfiable4_set`, `compactness_consequence4_set`, `compactness_consequenceC_set` | Arbitrary-premise satisfiability/consequence is determined by finite subsets |
| Constrained finite-grounding completeness | — | Thm 3.35 | `FiniteFO.QClosesExt.complete_of_unsat`, `FiniteFO.QDerivesExt.complete` | Finite-domain completeness theorem using rigid ground constraints plus propositional completeness |
| Conjunction (hội) | ∧ | Def 1.2 / 2.3 | `V4.conj`; `Continuous.conj2` | (min, max) on the two channels |
| Core extensional quantified tableau | — | Def 3.36 | `FiniteFO.QClosesExtCore`, `FiniteFO.QDerivesExtCore` | Macro-free finite-domain extensional tableau used as the target for constructor replay |
| Core closure monotonicity | — | Prop 3.42 | `FiniteFO.QCloses.mono`, `FiniteFO.QClosesEq.mono`, `FiniteFO.QClosesExtCore.mono` | Verified fact that quantified branch closure is preserved when the branch is extended |
| Consequence (hệ quả) | ⊨ | Def 2.6 | `Metatheory.Consequence4` (FOUR), `ConsequenceC` (continuous), `ConsequenceCAt` (fixed τ) | Preservation of (signed) satisfaction over all v and all τ; τ-invariant (Prop 4.27) |
| Crisp equality | x=y | Def 2.20 | `FiniteFO.qeval` on `QFormula.eq` | Equality in finite-FO: T when assigned elements match, F otherwise |
| Derivability (dẫn xuất) | ⊢_A | Def 3.5 | `ProofTheory.Derives`, `DerivesU` | Some tableau for Σ plus the opposite-signed conclusion closes |
| Effective intensity (cường độ hiệu dụng) | eff(c) | Def 5.4 | `Generative.Channel.eff` | α·Φ(Θ): intensity modulated by structural stability |
| Existence intensity (cường độ tồn tại) | α | Def 5.4 | `Generative.Channel.α` | Absolute degree of presence, in [0,1]; poles attained |
| Designated states (chỉ định) | {T, B} | Def 2.5 | `V4.designated` | States counting as "holds" in the unsigned reading |
| Disjunction (tuyển) | ∨ | Def 1.2 / 2.3 | `V4.disj`; `Continuous.disj2` | (max, min) on the two channels |
| Fairness (công bằng) | — | Def 3.5 | — (paper-level; see DR-0005) | Every unprocessed signed formula is eventually processed on every extension |
| Finite continuous quantified model | M | Thm 2.24 | `FiniteFO.QCModel` | Finite-domain model interpreting predicates as continuous truth-objects for exact projection |
| Finite FOUR model | M | Def 2.20 | `FiniteFO.QModel` | Function-free finite-domain model interpreting predicates as FOUR values |
| Finite exact projection | π_τ(V_M(φ)) | Thm 2.24 | `FiniteFO.finite_exact_projection` | Projection commutes with finite-domain quantified evaluation for `0 < τ ≤ 1` |
| Finite grounding bridge | ground(rho, phi) | Def 3.28; Lem 3.29 | `FiniteFO.GroundAtom`, `FiniteFO.ground`, `FiniteFO.groundVal`, `FiniteFO.ground_truth` | Translation from finite-domain quantified formulas to propositional formulas, with a Lean-verified truth lemma under the induced valuation |
| Grounding simulation | — | Thm 3.32; Thm 3.35 | `FiniteFO.groundBranch_closes_to_QClosesExt`, `FiniteFO.rigidGroundBranch_closes_to_QClosesExt` | Macro-level syntactic simulation from propositional closure of grounded branches, unconstrained or rigid-constrained, to finite-domain extensional closure |
| Finite quantifier clauses | ∀, ∃ | Def 2.21 | `FiniteFO.forallV4`, `FiniteFO.existsV4` | FOUR-valued finite quantifiers: ∀=(all truth, some falsity), ∃=(some truth, all falsity) |
| Finite-support derivability | ⊢_A over arbitrary Σ | Cor 4.26 | `Metatheory.DerivesSet` | An arbitrary premise set derives a conclusion iff some finite subset derives it |
| Falsity channel (kênh sai) | f | Def 2.1 | `V4.f` (FOUR); `.2` (cont.) | Degree of support for falsity, independent of t |
| Formula (công thức) | φ, ψ, χ | Def 1.2 | `Formula` | Element of the language generated by ¬,∧,∨,⊕ |
| FOUR matrix | FOUR; T,F,B,N | Def 2.7 | `V4`, `V4.T/F/B/N` | {0,1}² with the same connective clauses; target of π_τ |
| Generative frame (khung sinh) | F = (d, Φ) | Def 5.1 | `Generative.GenFrame` | Structure dimension + stability function satisfying S-mem/S-flip/S-neutral |
| Generative state (trạng thái sinh) | s = (c_T, c_F) | Def 5.4 | `Generative.GenState` | Two independent support channels; initializes a truth-object |
| Glut/gap-free fragment | {T,F} inputs | Prop 4.30 | `Metatheory.Consequence4OnClassical` | The restriction of FOUR consequence to valuations whose atoms are classical corners |
| Good-prefix assignment | σ | Thm 4.25 | `Metatheory.PrefixGood` | A finite atom assignment whose every finite premise subset remains satisfiable by some extending valuation |
| Knowledge order (thứ tự tri thức) | ≤_k | Lem 2.18 | `Continuous.le_k` | (t₁,f₁) ≤_k (t₂,f₂) ⟺ both channels ≤; ⊕ is its meet; N bottom, B top on the square |
| Harmonization (hòa hợp) | ⊕ | Def 1.2 / 2.3 | `V4.oplus`; `Continuous.oplus2` | (min, min); consensus connective. ⚠ Literature calls the FOUR restriction "consensus", symbol ⊗ [arieli1996reasoning; fitting1991bilattices]; literature's ⊕ is the gullibility JOIN — clash recorded in DR-0002, confirmed 2026-07-03 (npl-positioning.md §2) |
| Latent collapse (sập-tiềm-ẩn) | — | Lem 2.11 (FOUR); Lem 2.16 (cont.) | `V4.latentCollapse`; `Continuous.latent_collapse` | φ⊕¬φ equalizes the channels; glut-free states land in N |
| Local replay rule | — | Prop 3.40 | `FiniteFO.ReplayTrace.replay_*_core` | Verified lemma replaying one quantified trace-item decomposition into the macro-free core tableau |
| Manifestation threshold (ngưỡng biểu hiện) | τ | Def 2.2 | argument of `Continuous.proj`, `SatC` | Cut-off in (0,1] deciding what counts as manifest |
| Material conditional | ⇒ | Def 1.3 | `Formula.impl` | Abbreviation ¬φ∨ψ; not primitive |
| Meta-sign | T⁺,T⁻,F⁺,F⁻ | Def 2.4 | `Sign`, `V4.sat`; `Continuous.SatC` | Threshold predicate on a single channel of a formula's value |
| Model (mô hình) | M = (v, τ) | Def 2.2 | unbundled: `v` + `InSquare` hypotheses + `τ` | Atom valuation into [0,1]² plus a threshold |
| ND calculus (hệ suy diễn tự nhiên) | ⊢_ND | Def 3.11 | `ProofTheory.ND` | The D1 §14 rule list as a calculus; sound (Prop 3.12) but incomplete (Thm 3.13) |
| ND⊕ calculus | ⊢_ND⊕ | Def 3.14 | `ProofTheory.NDO`; `Metatheory.NDO.complete` | The ND calculus extended with the two ⊕-De Morgan rules; sound and completeness verified |
| Negation (phủ định) | ¬ | Def 1.2 / 2.3 | `V4.neg`; `Continuous.neg2` | Channel swap (t,f) ↦ (f,t); NOT 1−x |
| Negation-normal form for ND⊕ | nnf(φ) | Lem 3.17 | `Metatheory.nnf`, `Metatheory.nnfNeg`, `Metatheory.NDO.nnf_equiv` | Formula equivalent to φ in `⊢_ND⊕` with negation pushed to atoms using the ∧/∨/⊕ De Morgan rules |
| Occurrence (xuất hiện) | Occurs n φ | Lem 4.23 | `Metatheory.Occurs` | Atom n occurs in φ; evaluation depends only on occurring atoms |
| ⊕-free ND⊕ completeness principle | — | Thm 3.20 | `Metatheory.OplusFreeNDOComplete`; `Metatheory.NDO.oplusFree_complete` | Lean-verified completeness of `⊢_ND⊕` restricted to ⊕-free premises and conclusions |
| Polarization coordinate (tọa độ phân cực) | Θ | Def 5.2 / 5.4 | `Generative.Channel.Θ` | Relational structure in [0,1]^d; ½ neutral, 0/1 polar; flip = half-turn; NOT a physical phase |
| Prime NDO theory | P | Thm 3.20 | `Metatheory.NDOTheoryClosed`, `Metatheory.NDOPrimeDisj`, `Metatheory.NDOConsistentFor`, `Metatheory.exists_maximal_NDOConsistentFor` | Deductively closed extension with the disjunction property, used to build the countermodel in the ⊕-free completeness proof |
| Quasivance | — | Def 5.6 (formal); ch. 0 (philosophy) | `Generative.Channel.Quasivant` | α = 0 with Θ ≠ neutral: unmanifest yet structured; Tier-2 avatar is state N (Prop 5.7); invisible at Tier 2 (Prop 5.8) |
| Quantified finite-domain formula | φ | Def 2.19 | `FiniteFO.QFormula` | Function-free first-order NPL formula with predicate atoms, crisp equality, and finite-domain quantifiers |
| Quantified finite-domain branch | Γ | Def 3.21 | `FiniteFO.QBranch`, `FiniteFO.QSigned` | Finite tableau branch of signed quantified formulas, each evaluated at an explicit assignment |
| Quantified finite-domain tableau closure | — | Def 3.21 | `FiniteFO.QCloses`, `FiniteFO.QDerives` | Assignment-indexed signed tableau with finite ∀/∃ instantiation rules |
| Quantifier-to-fold close replay | — | Prop 3.61; Prop 3.63 | `FiniteFO.ReplayTrace.closeT_qAllTpos_qFoldConjTneg_core`, `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qAllTneg_generated_core` | Verified replay of mixed quantified-formula versus structured-fold close pairs |
| Equality-completed quantified tableau closure | — | Def 3.25 | `FiniteFO.QClosesEq`, `FiniteFO.QDerivesEq` | Repaired finite-domain quantified tableau adding four crisp-equality closure clauses |
| Full extensional quantified tableau | — | Def 3.30 | `FiniteFO.QClosesExt`, `FiniteFO.QDerivesExt` | Sound finite-domain tableau whose decomposition rules recurse through extensional closure on equal finite groundings and whose grounding macro-rules include rigid constraints |
| Fold-tail close replay | — | Prop 3.60 | `FiniteFO.ReplayTrace.closeT_qFoldConj_qFoldConj_core`, `FiniteFO.ReplayTrace.closeF_qFoldDisj_qFoldDisj_core` | Verified replay of matching structured q-fold close pairs into the macro-free core tableau |
| Fold-tail membership projection | — | Prop 3.58 | `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldConj`, `FiniteFO.ReplayTrace.qTailBranch_subset_of_mem_qFoldDisj` | Verified fact that a structured q-fold tail occurring anywhere in a replay trace contributes its projected quantified tail branch to the trace's full quantified branch |
| Fold-tail replay | — | Prop 3.43 | `FiniteFO.ReplayTrace.replay_qFoldConj*_core`, `FiniteFO.ReplayTrace.replay_qFoldDisj*_core` | Verified sign-split replay lemmas for structured finite conjunction/disjunction tails in replay traces |
| Generated q-fold tail | — | Def 3.62; Prop 3.63 | `FiniteFO.ReplayTrace.HasQInstBlock`, `FiniteFO.qinstItems`, `FiniteFO.qTailBranch_qinstItems` | Structured q-fold alignment condition recording that the trace projection contains every finite-domain instance of a quantified formula |
| Generated replay close-pair source | — | Def 3.66; Prop 3.67 | `FiniteFO.ReplayGeneratedCloseTPair`, `FiniteFO.ReplayGeneratedCloseFPair` | Pair-level close-source classification for generated traces, retaining generated q-fold certificates on both sides of a grounded T/F close pair |
| Generated replay ground source | — | Def 3.64; Prop 3.65 | `FiniteFO.ReplayGeneratedGroundSource`, `FiniteFO.ReplayTrace.groundBranch_mem_generated_source` | Source classification for generated traces whose q-fold cases recover the generated q-fold certificate matching a quantified grounding |
| Nonmatching q-versus-fold source | — | Prop 3.70 | `FiniteFO.q_vs_fold_conj_nonmatching_shape_counterexample`, `FiniteFO.q_vs_fold_disj_nonmatching_shape_counterexample` | Refuted shortcut: a q-source can ground to a fold without having the matching quantifier as its outer constructor |
| Recursive q-versus-fold replay | — | Prop 3.71 | `FiniteFO.ReplayTrace.closeT_qConjTpos_qFoldConjTneg_core`, `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qConjTneg_step_core`, etc. | Verified head/tail replay steps for q-side propositional constructors closing against structured q-fold sources |
| Replay trace | — | Def 3.38 | `FiniteFO.ReplayItem`, `FiniteFO.ReplayTrace` | Trace state for constructor replay, including quantified formulas, rigid atoms, and residual fold tails |
| Replay ground source | — | Def 3.51; Prop 3.52 | `FiniteFO.ReplayGroundSource` | Classification of how a signed formula in a trace ground branch originates from quantified, rigid, or structured fold-tail data |
| Replay close-pair source | — | Def 3.53; Prop 3.54 | `FiniteFO.ReplayCloseTPair`, `FiniteFO.ReplayCloseFPair` | Pair-level source classification for propositional T/F close pairs in an admissible replay trace |
| Rigid finite-ground constraints | R_n | Def 3.34 | `FiniteFO.rigidGroundConstraints` | Finite signed propositional branch forcing ground truth, falsity, and equality atoms to their finite-domain values |
| Rigid-versus-fold exclusion | — | Prop 3.68 | `FiniteFO.ReplayTrace.closeT_rigidTpos_qFoldConjTneg_false`, etc. | Verified exclusion of all rigid-source versus structured q-fold source close-pair combinations in admissible replay traces |
| Cross-fold exclusion | — | Prop 3.69 | `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qFoldDisjTneg_false`, etc. | Verified exclusion of structured conjunction-fold versus disjunction-fold close-pair combinations |
| Rigid equality replay | — | Prop 3.41 | `FiniteFO.ReplayTrace.replay_eqTneg_rigidTpos_core`, etc. | Verified bridge from a quantified equality item plus matching rigid equality atom to a core equality closure |
| Structured q-fold tail | — | Def 3.38 | `FiniteFO.ReplayItem.qFoldConjTail`, `FiniteFO.ReplayItem.qFoldDisjTail` | Residual fold-tail trace item that keeps assignment/formula pairs so the quantified projection can recover finite-domain instances |
| Suffix-aligned tail consumer | — | Prop 3.72 | `FiniteFO.ReplayTrace.closeT_qFoldConjTpos_qTneg_tailConsume_core` + 3 sign variants, `*_tailConsume_full_core` entry points | Recursive replay theorem closing any q-formula against a structured fold tail whose suffix it grounds to: structural descent, left children close on fold members, matching quantifier closes memberwise; no admissibility needed |
| Fold-chain injectivity | — | Prop 3.72, Step 1 | `FiniteFO.foldConj_inj`, `FiniteFO.foldDisj_inj` | Equal conjunction/disjunction fold chains have equal form lists; exposes memberwise quantifier-fold alignment |
| Close-pair dispatcher | — | Prop 3.73 | `FiniteFO.ReplayTrace.closeT_pair_dispatch_core`, `closeF_pair_dispatch_core`, membership form `closeT/F_members_dispatch_core` | Sixteen-way source dispatch closing the core tableau from any admissible plain propositional close pair; needs no generated certificate |
| Domain-weighted measure | qsize, qweightB | Thm 3.74, Step 1 | `FiniteFO.qsize`, `FiniteFO.qweightB` | Formula size with quantifiers weighted by domain cardinality (`(n+1)·qsize(φ)+1`); every core rule strictly decreases the branch total |
| Quantified completeness engine | — | Thm 3.74, Step 2 | `FiniteFO.qclosesCore_todo`, `FiniteFO.qclosesCore_lits` | Strong induction on the domain-weighted todo weight decomposing to literals, then equality/ground closure or the canonical finite model |
| Core semantic completeness | — | Thm 3.74 | `FiniteFO.QClosesExtCore.complete_of_unsat`, `qclosesExtCore_iff_unsat`, `QDerivesExtCore.complete`, `qDerivesExtCore_iff_qconsequence4` | Finite-domain unsatisfiability is equivalent to macro-free core closure; derivability coincides with finite semantic consequence |
| Satisfaction, unsigned (thỏa mãn) | M ⊨ φ | Def 2.5 | `Continuous.SatC` (T⁺ case) | t_M(φ) ≥ τ; reads the truth channel only (= T⁺) |
| Saturation (bão hòa) | — | Def 3.4 | — (paper-level; see DR-0005) | Hintikka condition: every rule instance on the branch is fulfilled |
| Signed formula (công thức có dấu) | Sφ | Def 3.1 | `ProofTheory.SignedFormula`, sat = `sat4` | Pair of a meta-sign and a formula |
| Stability function (hàm ổn định) | Φ; canonical Φ_c | Def 5.1 / 5.2 | `GenFrame.stab`; `Generative.canonStab` | Converts structure to a multiplier in [0,1]; canonical = geometric mean of 1−2\|x−½\| |
| Support channel (kênh hỗ trợ) | c = (α, Θ) | Def 5.4 | `Generative.Channel` | One side of the evidence: intensity + structure; two per atom (for/against) |
| State (trạng thái) | T, F, B, N | Def 2.5 | `V4.T/F/B/N` | Fiber of π_τ ∘ V_M: manifest true/false, Both, Neither |
| Tableau (bảng phân tích) | — | Def 3.5 | `ProofTheory.Closes` (closability; Rem 3.6) | Finite binary tree of branches grown by the 16 decomposition rules |
| Threshold projection (phép chiếu ngưỡng) | π_τ | Def 2.8 | `Continuous.proj` | (x,y) ↦ (𝟙[x≥τ], 𝟙[y≥τ]); exactness = Thm 2.13 |
| Truth channel (kênh đúng) | t | Def 2.1 | `V4.t` (FOUR); `.1` (cont.) | Degree of support for truth, independent of f |
| Truth core | truthCore(φ) | Lem 3.18 | `Metatheory.truthCore`, `Metatheory.NDO.truthCore_equiv` | ⊕-free formula interderivable with φ in `⊢_ND⊕` for T⁺ natural deduction |
| Truth order (thứ tự chân lý) | ≤_t | Lem 2.18 | `Continuous.le_t` | (t₁,f₁) ≤_t (t₂,f₂) ⟺ t₁≤t₂ ∧ f₂≤f₁; ∧/∨ are its meet/join |
| Truth-object (vật chân lý) | (t, f) | Def 2.1 | `Continuous.TruthObj`; FOUR fragment `V4` | Pair of independent channel values in [0,1]² |
| Well-formed replay trace | — | Prop 3.41 | `FiniteFO.ReplayTrace.WF` | Replay trace whose rigid items are drawn from the finite rigid ground constraints |

## Naming conventions

- English term is canonical; the Vietnamese working term from `drafts/` is recorded in parentheses.
- Symbols: fix a symbol once and never overload it; reserve a Unicode symbol and a LaTeX macro together.
- Lean names: `Nullivance.<Chapter>.<name>` mirroring the doc structure (`Continuous.*` and
  `ProofTheory.*` abbreviate the `Nullivance.` prefix). "paper-level" = notion used only in
  paper proofs, absorbed by the `Closes` encoding (Rem 3.6 / DR-0005).
