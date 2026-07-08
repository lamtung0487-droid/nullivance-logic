---
name: related-work
description: Position nullivance against existing logic literature - find similar systems, build comparison tables, vet novelty claims, maintain the bibliography. Use when the user asks how nullivance relates to existing logics, before making any novelty claim, or when writing the related-work section of a paper.
---

# Related work: literature positioning

Novelty claims are the easiest way for a logic paper to be desk-rejected. Every claim of
the form "no existing system does X" must survive this skill first.

## Procedure

### 1. Decompose the feature
Take the nullivance feature/claim under investigation and decompose it into searchable
properties (e.g., "third truth value absorbed by conjunction", "negation not involutive",
"empty-domain quantification"). Abstract away our terminology — the literature will not
use the word "nullivance".

### 2. Search systematically
Use WebSearch/WebFetch. For each property, check at minimum:
- **Stanford Encyclopedia of Philosophy** (plato.stanford.edu) — the canonical survey source,
- standard families: many-valued logic (Łukasiewicz, Kleene, Bochvar, Priest LP), partial logic, free logic, paraconsistent and relevance logics, intuitionistic and minimal logic, substructural logics, logics of nonsense (Bochvar, Halldén), quantum logic,
- recent work: search Google Scholar / arXiv (math.LO, cs.LO) with the decomposed property phrases.

Record every consulted source, including negative results ("checked Bochvar's B3 — differs because …").

### 3. Compare precisely
For each genuinely close system, build a comparison at the level of formal detail:
truth tables side by side, axiom lists side by side, or a translation attempt in both
directions. "Similar in spirit" is not a finding; "agrees with weak Kleene on {∧,∨} but
differs on negation: table…" is.

### 4. Verdict
One of:
- **Subsumed** — nullivance's feature already exists; cite it. This is valuable: we inherit their theorems (via translation) and must reposition our contribution.
- **Overlapping** — partial coincidence; state exactly where it diverges.
- **Novel (as far as checked)** — record the search scope honestly; novelty claims in `docs/`/`papers/` must be phrased "to our knowledge" and link to this check.

### 5. Install results
- Add BibTeX entries to `references/bibliography.bib` (verify metadata against the publisher/arXiv page, do not invent entries).
- Write/update a note in `references/` (`<topic>-comparison.md`) with the comparison tables and verdict.
- Update any novelty wording in `docs/` accordingly.

## Prohibitions
- Never fabricate or guess citations; every BibTeX entry must come from a fetched source.
- Never soften a "Subsumed" verdict to protect the project's novelty narrative (R9).
