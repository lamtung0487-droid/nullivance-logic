# 5. The generative tier (Tier 1)

Philosophical motivation stays in chapter 0; this chapter contains only the formal
generative interface.

**Architectural contract (D1 §6, load-bearing):** every metatheorem of chapters 2–4
depends only on the Tier-2 truth-object (t,f) and the connective table — never on the
shape of Φ or on how Tier 1 produces (t,f). Tier 1 is an *initialization theory*: it
explains where truth-objects come from and where the α/Θ philosophy lives. Replacing Φ
by any other frame-admissible function (Def 5.1) changes no theorem of chapters 2–4.
This chapter maintains that contract: nothing below is cited by chapters 1–4.

---

**Definition 5.1 (Generative frame).** `[VERIFIED]`
A *generative frame* is a triple `F = (d, Φ)` where `d ≥ 1` is the *structure dimension*
and `Φ : [0,1]^d → [0,1]` is a *stability function* satisfying:

- (S-mem) `Φ(Θ) ∈ [0,1]` for all `Θ ∈ [0,1]^d`;
- (S-flip) `Φ(1 − Θ) = Φ(Θ)` (componentwise flip `x ↦ 1−x`, the "half-turn");
- (S-neutral) `Φ(½, …, ½) = 1` (neutral structure passes intensity through unchanged).

> ⚠ Deviation from draft, flagged: D1 §7 defines one concrete Φ; the frame *axioms* are
> extracted from D1 §6's explicit requirement that Φ be replaceable without touching the
> logic. Both are installed (Def 5.2 gives the canonical instance). `d ≥ 1` is forced:
> the geometric mean is undefined at d = 0 (DR-0006).
> *Lean:* `Nullivance.Generative.GenFrame` · *DR:* DR-0006 · *Depends on:* —

**Definition 5.2 (Canonical stability function).** `[VERIFIED]`
Componentwise stability `f : [0,1] → [0,1]`, `f(x) = 1 − 2·|x − ½|` — maximal (= 1) at
the neutral point ½, zero at the poles 0 and 1. Canonical global stability of
`Θ ∈ [0,1]^d`: the geometric mean

`Φ_c(Θ) = (∏_{k<d} f(Θ_k))^{1/d}`.

Θ here is a *bounded polarization coordinate*, **not** a physical phase on a circle: the
flip `x ↦ 1−x` around ½ plays the role of "180° reversal" (disclaimer carried verbatim
from D1 §7). D1's "log form" is a numerical-stability implementation note, not
mathematical content; dropped (DR-0006).

> *Lean:* `Nullivance.Generative.fstab`, `canonStab` · *DR:* DR-0006 · *Depends on:* Def 5.1

**Lemma 5.3 (The canonical stability function is frame-admissible).** `[VERIFIED]`
For every `d ≥ 1`, `(d, Φ_c)` is a generative frame: Φ_c maps `[0,1]^d` into `[0,1]`,
is flip-invariant, and sends neutral structure to 1.

*Proof.* (S-mem) Each `f(Θ_k) ∈ [0,1]` since `|Θ_k − ½| ≤ ½` exactly when `Θ_k ∈ [0,1]`;
a finite product of `[0,1]`-values lies in `[0,1]`; and `x ↦ x^{1/d}` preserves `[0,1]`
for `x ≥ 0` (standard real-power facts). (S-flip) `f(1−x) = 1 − 2|½ − x| = f(x)` since
`|·|` is symmetric; the product is invariant term-by-term. (S-neutral) `f(½) = 1`, the
product of ones is 1, and `1^{1/d} = 1`. ∎

> *Lean:* `Nullivance.Generative.canonFrame` (fields `stab_mem`, `stab_flip`, `stab_neutral` via `fstab_mem`, `fstab_flip`, `fstab_neutral`) — sorry-free, `lake build` 2026-07-03. · *Depends on:* Def 5.1, 5.2

**Definition 5.4 (Support channels; generative state; initialization).** `[VERIFIED]`
Fix a frame F. A *support channel* is a pair `c = (α, Θ)` with `α ∈ [0,1]` (*existence
intensity* — absolute) and `Θ ∈ [0,1]^d` (*structure* — relational). Its *effective
intensity* is `eff(c) = α · Φ(Θ)`. A *generative state* of an atom is a pair of
independent channels `s = (c_T, c_F)` (support-for-truth, support-for-falsity); its
*initialization* is the truth-object

`init(s) = (eff(c_T), eff(c_F)) ∈ [0,1]²`  (Def 2.1).

This is where paraconsistency begins: evidence-for and evidence-against are separate
entities that can be simultaneously strong (glut) or simultaneously weak (gap); a
one-channel system can do neither (D1 §7).

> *Lean:* `Nullivance.Generative.Channel`, `GenState`, `Channel.eff`, `GenState.init` · *DR:* DR-0006 · *Depends on:* Def 2.1, 5.1

**Theorem 5.5 (Interface theorem).** `[VERIFIED]`
For every frame F and every generative state s: `init(s) ∈ [0,1]²`. Hence Tier 1 feeds
Tier 2 exactly the objects Definition 2.2 quantifies over, and every result of chapters
2–4 applies verbatim to models initialized by any frame. Conversely, chapters 2–4 never
mention F — the metatheory is Φ-independent by construction (the architectural
contract above).

*Proof.* `α ∈ [0,1]` (Def 5.4) and `Φ(Θ) ∈ [0,1]` (S-mem), and `[0,1]` is closed under
multiplication (`0 ≤ αΦ` from nonnegativity of both; `αΦ ≤ 1·1 = 1` from monotonicity of
multiplication on nonnegatives). Apply to both channels. The independence half is
architectural: it is witnessed by the absence of any reference to this chapter in
chapters 2–4 (checked by the audit skill, not by a formula). ∎

> *Lean:* `Nullivance.Generative.Channel.eff_mem`, `GenState.init_mem` — sorry-free. · *Depends on:* Def 2.1, 5.1, 5.4

**Definition 5.6 (Quasivance).** `[VERIFIED]`
Write `Θ_neutral = (½, …, ½)`. A channel `c = (α, Θ)` is *quasivant* iff `α = 0` and
`Θ ≠ Θ_neutral`: fully unmanifest, yet genuinely structured. A generative state is
quasivant iff both its channels are.

> ⚠ Deviation from draft, flagged: D1 Def 4 writes "α ≈ 0"; normalized to `α = 0` exactly,
> justified by D1 §3(3) itself — "Quasivance sống *tại đúng điểm* α = 0", the attainable
> absence horizon is the stated reason for the closed interval (DR-0006).
> *Lean:* `Nullivance.Generative.Channel.Quasivant`, `GenState.Quasivant` · *Depends on:* Def 5.4

**Proposition 5.7 (Quasivance is effectively silent; projects to N).** `[VERIFIED]`
A quasivant channel has `eff(c) = 0`. Hence a quasivant generative state initializes to
`(0,0)`, and for **every** threshold `τ ∈ (0,1]`, `π_τ(init(s)) = N`: the Tier-2 avatar
of quasivance is exactly the unmanifest state N of Definition 2.5.

*Proof.* `eff(c) = 0 · Φ(Θ) = 0`. Then `π_τ(0,0) = (𝟙[0 ≥ τ], 𝟙[0 ≥ τ]) = (0,0) = N`
since `τ > 0`. ∎

> *Lean:* `Nullivance.Generative.Channel.eff_of_quasivant`, `quasivant_projects_N` — sorry-free. · *Depends on:* Def 2.7, 2.8, 5.4, 5.6

**Proposition 5.8 (Tier-2 forgetfulness).** `[VERIFIED]`
Initialization is not injective: there exist generative states s₁ (quasivant) and s₂
(not quasivant) with `init(s₁) = init(s₂)`. Consequently quasivance is **not recoverable
from the truth-object**: it is a Tier-1 notion whose Tier-2 shadow is N, and nothing in
chapters 2–4 can (or should) distinguish structured from structureless absence.

*Proof.* Witness at d = 1: `c₁ = (0, Θ=0)` (quasivant — polar structure, zero intensity)
and `c₂ = (0, Θ=½)` (not quasivant — neutral structure); both have effective intensity 0,
so the states `s₁ = (c₁, c₁)` and `s₂ = (c₂, c₂)` both initialize to `(0,0)`.
Both channels of s₁ are quasivant, whereas neither channel of s₂ is quasivant. ∎

*R5 record (2026-07-27).* The former witness `s₁ = (c₁,c₂)` was refuted by
Definition 5.6 itself: because c₂ is not quasivant, that mixed state is not quasivant.
Replacing its second channel by c₁ repairs the witness without changing either
initialization.

*Consequence, stated honestly:* the philosophical content of quasivance ("nothingness
with shape") lives strictly at Tier 1. Claims about N in chapters 2–4 are claims about
*unmanifestness*, not about hidden structure.

> *Lean:* `Nullivance.Generative.init_not_injective` — sorry-free. · *Depends on:* Def 5.4, 5.6

**Proposition 5.9 (Polarization annihilates intensity).** `[VERIFIED]`
In the canonical frame: if any component `Θ_k ∈ {0, 1}` (fully polarized), then
`Φ_c(Θ) = 0`, hence `eff(α, Θ) = 0` **for every α, including α = 1**.

*Proof.* `f(0) = f(1) = 0`, a product with a zero factor is 0, and `0^{1/d} = 0` for
`d ≥ 1`. ∎

*This is a real semantic commitment* (surfaced by the R5 stress test):
full presence with fully polarized structure does not manifest. It is faithful to D1 §7
("bằng 0 tại hai cực") but was nowhere stated as a consequence; recorded here so it can
be revisited deliberately (an R4 event if the pole behavior of f is ever changed).

> *Lean:* `Nullivance.Generative.canonStab_pole`, `polar_kills_intensity` — sorry-free. · *Depends on:* Def 5.2, 5.4

**Proposition 5.10 (Flip covariance — was G1).** `[VERIFIED]`
Flipping the structure of both channels (`Θ ↦ 1 − Θ`, the "half-turn" of Def 5.2)
leaves the initialized truth-object unchanged.

*Proof.* Effective intensity is invariant per channel: `eff(α, 1−Θ) = α·Φ(1−Θ) =
α·Φ(Θ)` by (S-flip); apply to both channels. (Membership: `x ∈ [0,1] ⟹ 1−x ∈ [0,1]`.) ∎

> *Lean:* `Generative.Channel.flip`, `Channel.eff_flip`, `init_flip` — sorry-free. · *Depends on:* Def 5.1, 5.4.

**Proposition 5.11 (Initialization is surjective — was G2).** `[VERIFIED]`
For every frame F and every truth-object `p ∈ [0,1]²` there is a generative state
initializing to p.

*Proof.* Give both channels neutral structure and let intensity carry the coordinate:
`eff(p₁, Θ_neutral) = p₁·Φ(neutral) = p₁·1 = p₁` by (S-neutral); likewise the second
channel. ∎ (So Tier 1 loses no expressive range: every Tier-2 model arises from some
initialization — the converse companion to Thm 5.5.)

> *Lean:* `Generative.init_surjective` — sorry-free. · *Depends on:* Def 5.1, 5.4, Thm 5.5.

---

## Open items (chapter 5)

- ~~G1, G2~~ **resolved 2026-07-03** as Prop 5.10, 5.11.
- The "matching degree" sketch of D1 §3(2) (tích các α và phần tương quan Θ) is **not**
  formalized — it belongs to the future emergence/field layer, out of the logic's scope
  (D1 §18 declares it open; see also chapter 0).
