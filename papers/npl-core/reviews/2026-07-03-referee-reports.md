# Panel review — "Nullivance Propositional Logic: Threshold-Signed Consequence on the Unit Square with a Machine-Checked Completeness Theorem", draft v0.3 (2026-07-03)

Venue frame: a *Studia Logica / JPL / JoLLI*-tier journal. Three independent referees;
editor meta-review at the end. Manuscript: `papers/npl-core/main.tex` @ commit a50a48a.

---

# Referee 1 report — Correctness & rigor (2026-07-03)

**Recommendation: MAJOR REVISION** · Confidence: high

Summary: the paper presents a propositional logic valued in $[0,1]^2$ with a consensus
connective and a threshold-indexed family of sign predicates, proves that thresholding
commutes with evaluation, and derives soundness/completeness of a four-signed tableau
calculus first over the induced four-valued matrix and then over the continuous
semantics, with most results machine-checked in Lean. The mathematics, where I could
check it against the artifact, is sound; the manuscript as a self-contained document
is not.

## Major comments

1. **[CRITICAL] §6, unnumbered Remark after Theorem 6.4 (lines 332–339): the paper
   contradicts itself about its own results.** The Remark states "Compactness fails to
   be addressed: both theorems are finite-Σ; strong completeness for infinite Σ is
   open" — immediately after Theorem 6.4 *proves* compactness and strong completeness.
   This is a leftover from an earlier draft. A referee who reads only §6 cannot tell
   which claim the authors stand behind. Why it matters: self-contradiction about the
   headline metatheory is grounds for rejection on its own at most venues. Fix: delete
   the stale sentence; keep (and relocate) the still-true bifilter caveat.

2. **§5, Definition 5.1: the calculus — the paper's central object — is never actually
   defined.** The sixteen rules are described by two examples and the phrase "read off
   Definition 3.2". An underivability-sensitive metatheory (soundness AND the later
   incompleteness contrast) cannot rest on an unprinted rule set. Fix: print the full
   4×4 rule table (it exists in the project's development documents).

3. **§7, Proposition 7.8 (ND incompleteness): the ND calculus is defined only by
   allusion** ("assembling the source system's natural-deduction rules"). For an
   *incompleteness* theorem the exact rule list is the entire content — adding one rule
   changes the truth value of the theorem. The proof's reinterpretation argument also
   needs one displayed line: the induction invariant ("every rule constrains only the
   truth channel of ⊕"). Fix: display the sixteen ND rules (or the constructor list)
   and a three-line proof, not a prose gloss.

4. **§6, Theorem 6.4 (compactness): a theorem explicitly NOT covered by the artifact
   is proved in a parenthesis.** "(proof: an explicit finitely-branching tree of 'good'
   partial assignments …)" is a compressed allusion, not a proof. Since this is the one
   result the authors themselves flag as un-verified, it needs the *most* printed
   detail, not the least. The full argument (good assignments, pigeonhole over the four
   values, limit valuation via finite dependence) exists in the development and is
   correct — print it, including the standing assumption that the atom set is countable
   (used essentially in the enumeration; currently implicit in Definition 2.1's
   "countable set of atoms" but never invoked).

5. **§6, Theorem 6.1 uses $\models_{\FOUR}$, which is never defined in the paper.**
   Only the continuous $\models$ is defined (Definition 3.3). The reader must guess the
   FOUR-consequence relation (valuations into $\FOUR$? which designated machinery for
   signed formulas?). Fix: one displayed definition before Theorem 6.1.

6. **Proof content policy is inconsistent with the paper's own convention.** The
   header/footnote convention says results labelled [L] are verified; but
   Theorem 6.3 (decidability) carries an [L] marker that covers only the auxiliary
   lemma (`eval_eq_of_agree`), not the theorem, and Corollary 7.6 attaches
   [L: consistency_witness] to a statement whose first half (FDE conservativity) is
   paper-level. Two results are thereby presented as more verified than they are —
   under the paper's own reading of [L]. Fix: per-result markers with explicit
   "paper-level" tags where Lean does not cover the statement (as Theorem 6.4 already
   does correctly).

7. **Most results have no printed mathematical content at all** (Theorems 6.1, 6.2;
   Corollaries 7.1, 7.2; Propositions 7.3, 7.4): statement + [L] marker only. An expert
   cannot referee a PDF by trusting an artifact. Fix: two-to-five-sentence proof
   sketches for each (the soundness induction, the literal-stage canonical valuation,
   the projection/embedding computations) or a proofs appendix.

## Checked and found sound (certification)

Statement fidelity against the artifact and development documents was checked for every
numbered item: Definitions 2.1, 3.1–3.3, 4.1; Lemma 3.4 (i)–(iv) (the unit law is
correctly restricted to the square); Theorem 4.2 = `exact_projection`/`sat_projection`;
Theorems 6.1–6.2 = `derives_iff_consequence4`/`derives_iff_consequenceC` (finite Σ as
stated); Propositions 7.3–7.5, 7.7, 7.8 and Corollaries 7.1, 7.2, 7.9 match their Lean
declarations, including quantifier structure; Proposition 7.5's generality ("no ⊕-free
formula computes harmonization") is exactly the binary-definability statement proved
(`oplus_not_definable` on two fixed atoms — that *is* definability of a binary
connective). Degenerate cases probed: τ = 1 (signs behave correctly, embedding uses it),
empty Σ (nontriviality corollary handles it), d ≥ 1 stated in Definition 8.1. No
mismatch of strength found beyond items 6 above.

## Minor comments

1. §4: the indicator notation $\mathbb{1}[\cdot]$ is never introduced.
2. §6 Theorem 6.4: "read as 'some finite subset derives'" — display this as a
   definition, not an aside inside a theorem statement.
3. §8 Proposition 8.3(iii) is specific to the canonical frame; the statement says so,
   but the section lead ("for any admissible Φ") invites over-reading. One clarifying
   clause.

## Questions to the authors

Q1. Is the four-signed system equivalent (derivability-preserving both ways) to a
two-signed system over φ/¬φ, as your own related-work section hints? If yes, why prefer
four signs? Say so in §5.
Q2. In Theorem 6.4, is dependent choice eliminable (the tree is finitely branching over
a countable alphabet — König's lemma for such trees is choice-free in many settings)?

---

# Referee 2 report — Novelty & positioning (2026-07-03)

**Recommendation: MAJOR REVISION** · Confidence: high

Summary: the paper assembles Belnap–Dunn/bilattice semantics over the unit square with
the consensus operation as an object-language connective, adds a threshold-indexed
signed consequence, and verifies the resulting metatheory in Lean. The candid
"honest positioning" paragraph is the best thing in the paper; my job is to test
whether anything survives it.

## Major comments

1. **The central novelty claim rests on an admitted unchecked comparison.**
   Contribution 1 ends: negative signs mean the consequence relation "is not an
   instance of designated-value (bifilter) consequence *as far as we have checked*" —
   and §6's remark plus Conclusion (2) admit the Arieli–Avron bifilter collapse theorem
   has not been consulted. This referee HAS read Arieli–Avron (1996): any competent
   referee at this venue will have. Submitting with the load-bearing comparison
   unperformed is not acceptable; the answer is knowable with a library visit. Fix
   before resubmission: perform the comparison; then either (a) prove a precise
   separation statement ("no designated subset D ⊆ FOUR induces the signed relation",
   in a formulation that type-checks), or (b) weaken Contribution 1 accordingly. A
   hedge is not a theorem, and it is currently doing a theorem's job.

2. **The reduction attack on the headline theorem is not fully preempted.** The
   strongest honest version: *FOUR-completeness for the consensus language is
   Arieli–Avron 1996; your Theorem 4.2 is α-cut cutworthiness; Theorem 6.2 is then
   known-result + routine-glue, and what remains is a tableau reformatting and a Lean
   library.* §9 concedes the first two clauses but never confronts the composite
   claim. Fix: one paragraph naming the reduction and stating exactly where it breaks —
   as far as I can see, at (i) the negative signs (pending comment 1) and (ii) the
   all-τ quantification being *internal* to your consequence rather than a
   metatheoretic afterthought. Make that argument explicitly or the contribution
   paragraph overstates.

3. **Fitting 1991 is under-engaged.** That paper interprets logic programs over
   continuous bilattices (confidence factors) with the knowledge operations available
   in rule bodies — i.e., consensus over a continuous bilattice *in an object language*
   predates this paper in the logic-programming setting. The difference (fixed-point
   program semantics vs. consequence + completeness) is real but must be stated by the
   authors, not left for referees to reconstruct. Currently Fitting is cited only for
   "the square". Fix: two sentences in §9.

4. **§8 (generative tier): the mathematics is slight and the framing does heavy
   lifting.** The interface theorem is a product-of-unit-interval bound; forgetfulness
   is a two-line witness; polar annihilation is arithmetic of a chosen f. As a
   *limitative* result (quasivance is invisible to the logic) it is honest and I
   commend it, but a hostile reading is "a philosophical appendix upgraded to a
   section". Fix: either compress §8 to a two-page remark-style section, or argue for
   its inclusion (e.g. the Φ-independence-as-import-graph point, which IS novel as an
   artifact practice, deserves the emphasis instead).

5. **The name.** "Nullivance" and "quasivance" are introduced as if standard; no
   etymology, no motivation for coining two neologisms in a paper whose semantic
   objects all have literature names. A referee will ask why the paper does not simply
   say "thresholded product-bilattice logic". The philosophical answer presumably
   exists (the Zero-Postulate provenance); one footnote-length version of it must
   appear, or the terminology will read as branding.

## Minor comments

1. §9 "we inherit its literature rather than compete with it" — good sentence; move it
   to the introduction.
2. The Omori–Wansing survey is cited but not used; either engage (their taxonomy of
   FDE extensions locates yours) or drop.
3. Post-2022 twist-product literature: the paper's search-scope disclosure is
   commendable, but a resubmission should close that sweep, not disclose it.

## Questions to the authors

Q1. Precisely which object of Arieli–Avron 1996 does your $\dershort$ correspond to
under the ¬-translation of F-signs to T-signs, if any?
Q2. Is there a formula valid in your all-τ consequence that fails for some *fixed* τ
consequence (i.e., does quantifying over τ actually change the relation, or does
τ-invariance collapse it to any single τ)? If it collapses, say so — it affects how
"threshold-quantified" can be sold. If it does not, exhibit the separating instance.

---

# Referee 3 report — Presentation & scholarship (2026-07-03)

**Recommendation: MAJOR REVISION** · Confidence: high

Summary: a densely written systems paper with an unusually honest positioning section
and a verification artifact, marred by draft residue, missing self-containedness, and
an absent artifact-availability statement.

## Major comments

1. **No artifact statement.** The paper's selling point is machine-checking, yet
   Appendix A gives no repository URL/DOI, no Lean toolchain version, no mathlib
   pin, no build instructions, and no statement of the verification/correspondence
   policy beyond prose. Venues with artifact badges will desk-reject the artifact
   claim as unverifiable. Fix: a standard artifact paragraph (location, versions,
   `lake build` instructions, sorry-policy, which theorems are paper-only).

2. **Draft residue visible in the PDF.** (a) Title footnote says "Draft v0.1" while
   the file is v0.3; (b) the author footnote literally reads "Author name is a
   placeholder --- fix before submission"; (c) the stale compactness Remark in §6
   (also flagged as mathematics — it is equally a proofreading catastrophe). Any of
   these alone signals an unfinished manuscript to an editor.

3. **The bibliography does not build as configured.** `\bibliographystyle{plainurl}`
   references a style that ships with neither TeX Live's core nor the paper; the
   already-noted TODO in the project README confirms it. Also
   `$\mathbb{1}[\cdot]$` (§4): `\mathbb` is only defined on uppercase letters in
   `amssymb`; on digits it produces a wrong glyph or an error depending on the font
   setup. Fix: `plain`/`alphaurl`-with-file or biblatex; `\mathbbm{1}` (package
   `bbm`) or plain indicator notation.

4. **Section 7 is titled "Corollaries" but contains the paper's third-most-important
   theorem** (ND incompleteness, Proposition 7.8 — a genuine limitative result with
   its own proof method) and two propositions that are not corollaries of anything.
   Fix: retitle ("The behavioural profile of NPL") — the current title buries a
   result the abstract advertises.

## Abstract/introduction contract check (certification)

Promises (i)–(v) of the abstract were each traced: (i) → §4 ✓; (ii) → §6 ✓;
(iii) → §7 (Cor 7.2, Prop 7.3, Cor 7.9) ✓; (iv) → §7 (Props 7.5, 7.7) ✓;
(v) → §8 ✓. Contribution list items 1–5 all resolve to sections ✓. Terms used in the
abstract before definition: "quasivance" and "latent" are both glossed inline —
acceptable. No undelivered promise found. All 14 bibliography entries are cited in the
text; no dangling citations; no cited-but-missing keys.

## Minor comments

1. §1 "the specifically nullivance idea" — noun-as-adjective; rephrase.
2. §6 Remark: "Compactness fails to be addressed" is also ungrammatical English.
3. Notation: $\Form$ is defined in the macro block but used once; $\dershort$ carries
   a subscript A that is never explained (presumably "analytic") — say so.
4. The [L] markers cite bare declaration names without module paths in later sections
   but full paths in early sections; unify.
5. Consider a notation table; the sign/state/corner triple (T⁺ vs $\vT$ vs t) invites
   confusion and is only disambiguated by usage.

## Questions to the authors

Q1. Under what license and where will the artifact be archived (Zenodo DOI at
submission time is the norm)?
Q2. Is the intended venue a logic journal or a certified-mathematics venue (ITP/CPP)?
The current balance of printed-proof vs artifact-pointer fits the latter better; for
the former, §6–7 need real proof text.

---

# Editor meta-review (2026-07-03)

**Decision: MAJOR REVISION.** All three referees independently converge on major
revision; none recommends rejection — the underlying mathematics survived Referee 1's
fidelity check against the artifact, and the positioning honesty is above community
norms. But the manuscript is visibly unfinished (draft residue, self-contradicting
remark), not self-contained on its two central calculi, and its single most-exposed
novelty claim depends on a comparison the authors admit not having performed.

## Revision checklist (deduplicated, by severity)

1. **[Blocking]** Delete the stale compactness Remark in §6; keep the bifilter caveat
   only where it is still true. (R1.1, R3.2c)
2. **[Blocking]** Perform the Arieli–Avron bifilter comparison and rewrite
   Contribution 1 as either a precise separation statement or a weakened claim.
   (R2.1; also answers R2.Q1)
3. **[Blocking]** Print the sixteen tableau rules (table) and the sixteen ND rules
   (list); currently neither calculus is defined in the paper. (R1.2, R1.3)
4. Print the full compactness proof (the one non-Lean theorem) incl. the countability
   assumption; add proof sketches for all [L]-only results or a proofs appendix.
   (R1.4, R1.7, R3.Q2)
5. Define $\models_{\FOUR}$ before Theorem 6.1; define the indicator notation; fix
   `\mathbb{1}`. (R1.5, R3.3)
6. Artifact statement: repository/DOI, Lean & mathlib versions, build command,
   verification-coverage policy; make [L] markers coverage-accurate (decidability,
   FDE-conservativity). (R3.1, R1.6)
7. Remove draft residue: version footnote, author placeholder. (R3.2)
8. Bibliography style that exists; retitle §7; Fitting 1991 engagement (two
   sentences); neologism footnote; answer R2.Q2 (τ-collapse question) in the text —
   it is a genuinely good question whose answer belongs in §3.
9. Optional but recommended: compress §8 or re-center its emphasis on the
   import-graph independence check; move "we inherit its literature" to §1;
   close the post-2022 literature sweep.

## What the panel did NOT check

The PDF was not actually compiled (no TeX toolchain in the review environment); the
Lean artifact was consulted for statement fidelity but not independently rebuilt by
Referees 2–3; the post-2022 literature sweep remains open on the project's own
disclosure; and Referee 2's Q2 (τ-collapse) was posed, not answered — the panel does
not know the answer and considers it a substantive question.
