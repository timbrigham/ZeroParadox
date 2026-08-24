# Naming conventions, readable names, and the public-issue policy

**Body for `CLAUDE.md` §§ `R-NAMING` and `R-ISSUES`.** The rules are there; the CC-2 and
MC-1 rollout histories, the keystone "diagonal fixed point" naming decision, the retired
MC-1 identity, and the issue framing standard are here.

---

## Theorem/Proposition/Lemma Naming Convention

All formal ZP documents use the following hierarchy for naming results. Apply this consistently when drafting or editing any formal layer:

- **Theorem**: The primary result of a section — of major significance for the framework. Reserve for results that drive the dependency chain or that are the central claim of a layer (e.g., T3 Monotonicity, T-SNAP).
- **Proposition**: A derived result that is rigorously proved but subsidiary to the main theorems — true and important, but not the headline claim (e.g., T1 partial order, T2 clopen balls).
- **Lemma**: A technical helper result used as a stepping stone toward proving another result (e.g., L-RUN, T2 global minimum).
- **Corollary**: A result that follows immediately from a theorem, proposition, or lemma with no substantial additional work (e.g., C1, C2, C3, T1b). Mark with "Corollary" label.
- **Conditional Claim (CC)**: A result that holds only given an explicit modelling commitment not derivable from the axioms (e.g., CC-1: S₀ = ⊥).
- **Design Principle (DP)**: A design commitment — well-motivated and explicit — that is chosen rather than derived (e.g., DP-1: orthogonality).
- **Remark (R)**: An observation providing context or clarification; does not require proof.

When assigning a label, ask: "Is this result the central claim of its section, or is it infrastructure for something else?" Central claims are Theorems; infrastructure is Propositions or Lemmas.

### Readable Name Convention — CC-2 is "the Quine atom" (framework-wide, additive)

**Standing rule (Tim, 2026-06-09).** CC-2 (⊥ = {⊥}, the self-containing bottom) is the conceptual keystone of the framework — it is what forces ZF+AFA, makes ⊥ immune to external description, and is the single contact point between ZFC+Foundation and ZF+AFA. The bare label "CC-2" undersells it on two counts: it reads as a minor sequence code, and the "CC = Conditional Claim" prefix is now **stale** — CC-2 was upgraded to a Forced Metatheoretic Commitment (closed via ZP-J T-EXEC), so it is no longer a conditional claim. This is the same situation AX-1 was in before it became T-SNAP.

**The convention — ADDITIVE, never eliminative:**
- Present CC-2 with the readable name **"the Quine atom."** This is a recognized set-theory term (Quine, Aczel) — it carries real gravity and a literature anchor, and it is NOT ZP-invented jargon (avoid inventing a ZP-branded name — that would undo the de-jargoning work).
- **Keep "CC-2" as the formal handle and note it alongside** — e.g., "the Quine atom (CC-2)" on first/significant mention. Do NOT remove or rename the CC-2 identifier anywhere; every existing cross-reference stays valid.
- Gloss once per document as "the self-containing bottom, ⊥ = {⊥}."
- **⚠ SCOPE THE GLOSS — BANKED 2026-08-01 (Tim), NOT YET ROLLED OUT.** `⊥ = {⊥}` is well-formed and
  true **in the ZF+AFA metatheory** — that is anti-foundation's actual content and Aczel's Quine atom
  is a real object, so **do NOT retire it** (a flat retirement would deny a true theorem of a real set
  theory: the `snap_is_frameflip` over-correction pattern). But asserted of the **Lean carrier** it is
  a **cross-type `=`** — `bot : L` against `{bot} : Set L` — which is on this file's bedrock-violation
  list. **Carrier-level statements take the INSTANCE-OF-FAMILY form**, which the corpus already
  proves: `IsQuineAtom q := selfMem q ∧ ∀ x, selfMem x → x = q` (the family predicate),
  `da1_closed_concrete : IsQuineAtom (bot : MachinePhase)` (⊥ as an instance), and
  `selfMem_eq_singleton_bot : {x | selfMemDerived x} = {bot}` (a `Set L` equality, `[propext,
  Quot.sound]`). This is the **QuineHost pattern** — never "⊥ *is* {⊥}", always "here are the
  requirements, and ⊥ is a witness meeting them."
  - **Why it was missed, and it is a measurement error worth copying the lesson from.** The rollout
    note below says *"Lean is clean (CC-2 is never a Lean identifier — 0 occurrences)"*. True of the
    **label** and false of the **claim**: `ZeroParadox/Algebra/Wheel.lean` asserts the bare equation
    many times. **Grep the CLAIM, not the name** — the same rule this file states for
    kill-propagation, missed here at the measurement step. **No count and no line numbers are
    recorded here on purpose**: the figure once said "ten times" with ten line numbers, and both went
    stale as the file was edited. Measure it.
  - **⚠ AND THE ROLLOUT IS NOT A SWEEP — most occurrences are CORRECT.** All were re-read
    individually 2026-08-03: the governing scope note, the correction record, and every site that is
    explicitly ZF+AFA-scoped or hedged as a conjectured counterpart is **right as written**, because
    `⊥ = {⊥}` is a true theorem of a real set theory. Only a **carrier-level consequence** claim is a
    defect. Two have been found and fixed, both the same modality (`forced`, then `structurally
    requires`), and the second was left standing by the pass that fixed the first — which had
    recorded itself as fixing "the one" occurrence.
  - **Provenance, because it is easy to misremember (it was, this session):** the 2026-07-14 ratification
    retired **MC-1**'s identity and cites CC-2 only as the precedent for *keeping a label*. **CC-2's own
    identity was never reviewed.** And the two defects are NOT the same: MC-1's was **ill-typed**
    (cross-category, never a proposition); CC-2's is **well-typed in the metatheory and cross-type in
    the carrier**. Scope it; do not retire it.
- **Do not overclaim status.** It remains a Forced Metatheoretic Commitment, not a Lean theorem. The structural self-application fixed point is Lean-proved (ZP-J T-EXEC); the literal set-membership ⊥ ∈ ⊥ is metatheoretic (lives in the ZF+AFA framing, not the Lean kernel). The readable name conveys significance, not proof-status.

**Rollout (phased, not a 12-PDF marathon):**
- Reader-facing surfaces first: README.md, GUIDE.md, register.md.
- Then apply to each formal document/companion **as it is next revised** (the readable name leads CC-2's introduction). Footprint as of 2026-06-09: 12 build scripts carry CC-2 (build_zpe.py 27, build_zpa.py 13, build_zpc.py 8, etc.); Lean is clean (CC-2 is never a Lean identifier — 0 occurrences).
- **Do not touch** RELEASES.md (release record - never rewrite history).

### The keystone concept — "the diagonal fixed point" (confirmed name)

**Standing rule (Tim, 2026-06-10).** The Quine atom (CC-2) is only the *set-theoretic face* of the
framework's actual keystone: **⊥ is the same self-referential fixed point in every framework, and the
floor of each structure is its point of self-reference** (the Gödel inversion — self-reference located
at the floor, not the ceiling). The confirmed readable name for this keystone is **"the diagonal fixed
point."** This language has recurred across many sessions; it is the real central concept.

- The faces of the one diagonal fixed point: the Quine atom (set theory, CC-2), the Kleene quine
  (computability, ZP-K), v₂(0)=∞ (valuation, ZP-B), the unique fixed point of `selfApp`
  (ZP-J `AbstractSelfApp`), unbounded surprisal / no external description (ZP-C), the categorical
  initial object (ZP-G). MC-1 (the bottom family) is what identifies them as kin.
- **Name it to evoke the recognized phenomenon, do NOT claim the unification as proved.** "Diagonal"
  anchors it to the diagonal argument and Lawvere's fixed-point theorem (the recognized home for
  self-referential fixed points across Russell / Quine / Kleene / Gödel / Tarski / Cantor). What ZP has
  *formalized*: `AbstractSelfApp` + instances, T-COMP (Quine atom = Kleene fixed point = ⊥), ZP-M
  (Kleene quine ∧ ε₀ co-witnessed). That ZP's keystone *is* a manifestation of Lawvere's theorem is a
  CONNECTION / conjecture, not a ZP result — keep that fence.
- Full articulation, faces, and the formal-vs-conjectural split:
  `.claude-local/notes/keystone_self_referential_fixed_point_2026-06-10.md`.

### MC-1 status convention — RETIRED as a commitment; MC-1 = the bottom family (rolled out 2026-07-15)

**Standing rule (Tim, ratified 2026-07-14, rolled out 2026-07-15).** MC-1 no longer names a "modeling
commitment" to one object; it names the **bottom family**. The "MC = Modeling Commitment" prefix is stale
(the same arc as AX-1→T-SNAP and CC-2→FMC). The earlier "correspondence derived / identity a commitment"
split is superseded:

- **Correspondence half — now formally realized.** Each domain bottom is the categorical bottom
  (limit or initial object) of its own *real* Mathlib category: F_B `fB_functor : ℕᵒᵖ ⥤ TopCat`
  (⊥ = inverse limit `⋂ B(0,2⁻ⁿ) = {0}`), F_D `fD_functor : ℕ ⥤ ModuleCat ℂ` (⊥ = initial object
  `StateSpace 0`), F_C `fC_functor : ℕ ⥤ KleisliCat PMF` (⊥ = initial object `Fin 0`, with
  `fC_no_return` = AX-G2 as a theorem). Bundled witness: `mc1_correspondence` (`MC1Bridge.lean`).
  So the bare label "MC = Modeling Commitment" now **undersells** this half.
- **The family — membership proved.** Each domain's bottom satisfies a shared list of criteria (the slots
  in BOTTOMELEMENT); per-domain membership is proved, the choice of criteria a design principle.
- **Identity half — RETIRED as ill-typed.** That the four bottoms are *numerically one object* across
  distinct categories is NOT a commitment the framework holds — `x = y` across distinct categories is not a
  well-formed proposition, so it was never a claim. The members are provably distinct (the walls); the only
  oneness is the shared *shape* (the diagonal fixed point), apophatic, never a formal identity.

**The convention (ADDITIVE, never eliminative):**
- Keep **"MC-1"** as the formal handle everywhere; it now points at the **bottom family** (CC-2 precedent:
  keep the label, retire the framing). Do not rename it; `mc1_correspondence` is unchanged. **Never call the
  cross-category identity a "modeling commitment," "offered," or "one object we commit to"** — it is retired
  as ill-typed. Present the split: membership PROVED, criteria a design principle, identity RETIRED, members
  provably distinct.
- **No new readable name for MC-1.** Unlike CC-2 (which *is* an object = the Quine atom), MC-1 is the
  *identification*; its underlying object already has the confirmed readable name
  [[project_diagonal_fixed_point]] ("the diagonal fixed point"). Coining an MC-branded name would be
  the ZP-invented jargon the CC-2 convention warns against — do not.
- **Do not overclaim.** The real categories are not `ZPCategory` instances (they have terminal
  objects), so ⊥ is the *limit* in `TopCat` and the *initial object* in the other two; state that
  distinction honestly. The cross-category identity is never claimed as proved.
- Canonical definition lives in **BOTTOMELEMENT's opening** ("The family - MC-1"); everything references
  there (draft MC1.md folded in + archived to `.claude-local/notes/` 2026-07-15).
- **Rollout DONE (2026-07-15):** README, CLAIMS, SNAP + BOTTOMELEMENT via their generators. Do not touch RELEASES.md.

## GitHub Issues — Transparency and Engagement Policy

The Zero Paradox project treats GitHub Issues as a public transparency mechanism, consistent with the project's core transparency commitment. Issues are not just a bug tracker — they are the public record of what is open, contested, or unresolved in the framework.

### When to check

- At the start of any session where a PR is being created or merged
- At the start of any session where outreach responses are being processed
- Any time Tim asks about external engagement or project status

### When to file a public issue

- Framework open questions that are genuinely unresolved and would benefit from external input (e.g. OQ-E2 cardinality question, AFA/CH tractability)
- Substantive technical questions that arose in review and were not closed within the session
- Questions where the framework explicitly flags something as open and outside the authors' expertise

### When NOT to file

- Anything sourced from private correspondence (reviewer feedback, outreach responses, academic group correspondence)
- Reviewer identity or feedback details
- Outreach strategy, sending schedules, or draft emails
- Editorial or prose decisions
- Anything that belongs in `.claude-local/`

### Issue framing standard

Public issues should read as genuine open questions to the mathematical community — not as requests for validation. Frame them as specific, honest about uncertainty, and standalone without requiring knowledge of the full framework.

### Identifier tracking — standing requirement

Every outreach item must have its external identifier recorded in `.claude-local/outreach/tracker.md` at the time it is created or sent. No exceptions.

**What counts as an identifier:**
- GitHub Discussion: `#N` (e.g. `#77`)
- GitHub Issue: `#N`
- MathOverflow question: full URL
- Email thread: date sent + recipient (email threads have no stable ID — date + recipient is the key)
- Zulip post: stream + topic slug
- arXiv submission: arXiv ID

**When to record it:** At the moment the item is created or sent — not after the fact. If an identifier is missing from the tracker, add it before doing any other work in that outreach session.

---
