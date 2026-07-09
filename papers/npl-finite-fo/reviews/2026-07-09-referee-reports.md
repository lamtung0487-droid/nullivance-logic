# Panel review — "Finite-Domain Quantified Nullivance Logic: A Machine-Checked Completeness Theorem for a Macro-Free Extensional Tableau", draft v0.1 (2026-07-09)

Venue calibration: serious automated-reasoning / non-classical-logic venue
(JAR / Studia Logica tier). Ground truth assumed sound (audit of 2026-07-09
passed); this panel evaluates the manuscript as strangers will read it.

---

# Referee 1 report — Correctness & rigor (2026-07-09)

Recommendation: MAJOR REVISION
Confidence: high

Summary: The paper extends a previously published propositional four-signed
threshold logic by quantifiers over a fixed finite nonempty domain with crisp
equality, refutes the completeness of the naive lifted tableau by
machine-checked countermodels, and proves that a "core extensional" tableau —
adding four equality clauses and two ground-closure clauses — closes a branch
exactly when no finite model satisfies it, by a weighted-measure engine and a
canonical model; a corollary connects propositional closure of the grounded
branch (under rigid constraints) to core closure. All results carry Lean
markers.

## Major comments

1. **§6 (Def. core calculus): the calculus is not reconstructible from this
   paper.** The definition says "all sixteen propositional decomposition rules
   and all eight finite quantifier rules are retained", but the sixteen rules
   appear nowhere in this manuscript (they are in the companion). A referee
   cannot check soundness or the engine's case analysis as printed. Fix: print
   the rule table (it is small), or at minimum the eight quantifier rules plus
   an explicit statement that the propositional rows are those of companion
   Table N, reproduced in an appendix.
2. **Semantic consequence $\Gamma \models_{Q,n} s\varphi$ is used (Prop.
   soundness, Thm. completeness) but never defined.** The macro exists; a
   definition does not. Fix: one displayed definition in §3 (all models over
   the fixed domain satisfying every member of $\Gamma$ satisfy $s\varphi$).
3. **Prop. soundness is stated with no proof content** — the entire
   justification is the [L] marker. Even a two-line sketch (induction on the
   closure derivation; each closure clause is unsatisfiable at its own
   assignment pair; each rule preserves satisfiability downward) is required
   for a journal version.
4. **Statement fidelity (checked, sound):** I compared every numbered
   statement against the named Lean declarations: the completeness theorem's
   domain quantification (`QModel n`), the projection theorem's threshold
   hypotheses ($0<\tau\le1$), duality's nonempty-domain remark, and the
   grounding corollary all match. The engine sketch's three steps correspond
   to `qsize/qweightB`, `qclosesCore_todo`, `qclosesCore_lits`. No statement
   printed stronger than verified. The sets-as-signs identification
   ($\Fp = \{\vB,\vF\}$, $\Fm = \{\vT,\vN\}$) is correct.
5. **Edge cases (checked, sound):** empty branch (hypothesis vacuous, theorem
   holds via the engine's base case), $\tau=1$ included in projection, $n=0$
   (one-element domain) exercised by the reflexivity refutation. The
   fixed-domain design excludes the empty-domain pathologies and the paper
   says so.

## Minor comments

1. §3, Def. evaluation: say explicitly that branch members carry their own
   assignments (it is stated, but only inside a parenthetical; promote it).
2. §7 proof, Step 2: "monotonicity of closure restores the full branch" —
   name the lemma (closure is preserved under branch extension).
3. §5: the block/per-element rule split is described in prose; a two-column
   display would prevent misreading which signs are which.

## Questions to the authors

1. Is the exact characterization (closure iff finite unsatisfiability)
   decidable as stated — i.e., is `QConsequence4` decidable for fixed $n$ —
   and if so, why is decidability not claimed?
2. Does the engine yield a complexity bound (the weight is exponential in
   quantifier nesting)?

---

# Referee 2 report — Novelty & positioning (2026-07-09)

Recommendation: MAJOR REVISION
Confidence: medium-high

Summary: A finite-domain quantified extension of a four-valued threshold
logic, with a machine-checked exact-characterization theorem for a tableau
calculus extended by equality and ground-closure clauses. The novelty is
claimed for the calculus format, the equality/ground clauses, the
domain-weighted completeness engine, and the mechanization — not for
many-valued first-order tableau completeness as such.

## Major comments

1. **The reduction attack is not preempted where the reader mounts it.** A
   knowledgeable referee's first reaction: "finite-domain many-valued logic
   is essentially propositional — ground out the quantifiers and apply the
   companion's completeness theorem; the paper is a corollary." The
   ingredients to rebut this exist in the paper (the refuted bare grounding
   bridge; the rigid constraints; the macro-free requirement; the extensional
   closure example), but they are scattered across §5, §8 and §9. The
   introduction must state the objection and answer it in one place: the
   naive reduction is machine-refuted, the repaired reduction needs rigid
   constraints and previously proved completeness only up to a simulation
   macro, and eliminating that macro is exactly the content of the headline
   theorem.
2. **Engagement with Carnielli/Hähnle is now present and formally specific
   (checked against the positioning note §6.1) — but the paper should also
   delimit against the distribution-quantifier tradition on the semantic
   side:** their calculi cover arbitrary domains; ours fixes the domain in
   the judgment itself. A sentence on why fixed-domain judgments are the
   right primitive for the intended applications (finite data) would blunt
   "your logic is a fragment of theirs".
3. **Significance:** as positioned, the contribution rests substantially on
   the mechanization and the refutation catalogue. That clears the bar at an
   automated-reasoning venue; at a pure non-classical-logic venue it would
   need the infinite-domain story or the complexity story. State the intended
   venue class in the cover letter; for the manuscript, the open-problems
   section already points the right directions.

## Minor comments

1. The search-scoped novelty claim for "first machine-checked completeness of
   a many-valued quantified tableau" is properly hedged and points to the
   recorded literature pass; keep the pointer in the published version (as a
   footnote with date and scope).
2. Cite the universally-free FO BD line (arXiv:2412.19767) alongside
   \cite{behounek2023free} or drop the sentence that gestures at it.

## Questions to the authors

1. Can the core calculus be presented as an instance of Hähnle's sets-as-signs
   framework restricted to finite domains, and if so, does his generic
   completeness argument apply — or does the crisp-equality/ground-closure
   layer genuinely fall outside it? (The paper asserts the latter; a paragraph
   arguing it would preempt the strongest referee attack.)

---

# Referee 3 report — Presentation & scholarship (2026-07-09)

Recommendation: MAJOR REVISION
Confidence: high

Summary: A readable companion paper with a firm results-to-artifact
correspondence policy; presentation gaps concern self-containedness and the
artifact-availability statement.

## Major comments

1. **Artifact availability is not stated.** The appendix gives toolchain,
   build command, coverage policy and axiom audit, but never says where the
   artifact can be obtained (the companion paper has an availability
   sentence; this one lost it). For a paper whose headline is
   "machine-checked", this is disqualifying as printed. Fix: add the
   availability/DOI-at-submission sentence.
2. **Abstract/introduction contract (checked):** all five contribution items
   are delivered with section pointers — (i) §3, (ii) §5, (iii) §6–7,
   (iv) §8, (v) §9. However, the abstract's "(ii) ... two further tempting
   proof routes are refuted" is delivered only if §9's obstruction counts as
   one of the two; §5 itself contains one refutation (naive calculus) plus an
   example. Count and name the refutations consistently (reflexivity; bare
   grounding bridge; nonmatching-shape dispatcher shortcut) or weaken the
   abstract sentence.
3. **Order of presentation:** $\models_{Q,n}$ (used from the contributions
   onward) and "branch" (first used in §3's Def. evaluation parenthetical)
   are never formally introduced — same finding as Referee 1.2; also the
   term "macro"/"simulation macro" is used from the abstract but only
   explained in §8. One sentence at first use.

## Minor comments

1. The `\dom` macro is defined and never used; delete.
2. §4 label `sec:groundingdef` vs §8 `sec:grounding` invites confusion;
   rename one.
3. Bibliography: all cited keys resolve; `behounek2023free` is an arXiv-noted
   entry — acceptable for a draft, upgrade to the IUKM proceedings entry
   (volume/pages) before submission.
4. Consistent use of "core calculus" vs "core extensional tableau" — pick one
   after first definition.

## Questions to the authors

None beyond the above.

---

# Editor meta-review (2026-07-09)

**Decision: MAJOR REVISION.** The panel is unanimous. No critical findings:
no claimed-status dishonesty, no statement printed stronger than its verified
counterpart, and the novelty positioning survives Referee 2's reduction
attack in substance — but not yet in presentation.

## Revision checklist (deduplicated, by severity)

1. Print the calculus: quantifier rule table + propositional rule table (or
   appendix reproduction from the companion). (R1.1, R3 self-containedness)
2. Define $\Gamma \models_{Q,n} s\varphi$ and "signed branch" formally at
   first use. (R1.2, R3.3)
3. Add the reduction-objection paragraph to the introduction: naive reduction
   machine-refuted → rigid repair → macro elimination as the headline
   content. (R2.1)
4. Add the artifact availability sentence to the appendix. (R3.1)
5. Add a soundness proof sketch. (R1.3)
6. Name the three refutations consistently in abstract and §5, aligning the
   count. (R3.2)
7. Add the fixed-domain-vs-distribution-quantifier delimitation sentence and
   the sets-as-signs question (R2.2, R2.Q1) — a short paragraph in §Related
   work.
8. Minor: promote the per-member-assignment sentence; name the monotonicity
   lemma; block/per-element display; delete `\dom`; rename a section label;
   cite or drop arXiv:2412.19767; terminology consistency.

## What the panel did NOT check

Line-by-line correspondence of the engine sketch to the 600-line Lean proof
(delegated to the artifact and the project audit); the IUKM proceedings
metadata for \cite{behounek2023free}; grammar beyond sampled sections; and
whether the intended venue's formatting requirements are met (draft uses a
plain article class).
