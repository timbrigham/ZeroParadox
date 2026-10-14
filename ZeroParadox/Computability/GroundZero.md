# GroundZero — ride-along documentation

Moved from `ZeroParadox/Computability/GroundZero.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

In the sections below, "this file", "here" and every bare § number refer to
`ZeroParadox/Computability/GroundZero.lean`.

## Formal Overview (AI-assisted)

This file connects two developments the project already had and had never wired together:
the operational model of § I-V of `Occurrence.lean` (`f : σ → Option σ`), and the coalgebra
for the functor `X ↦ 1 + X` in `NatListRegime.lean` (`natPF_NatListRegime`, `natInfinity`),
which is cited there to Jacobs & Rutten (EATCS Bulletin 62, 1997).

**What it establishes.** Reading a step function as a coalgebra, every configuration is a leaf
(halted) or a successor (stepping) — the head is `Bool`, so "exists but has not begun" is not
merely unproved, it is *not expressible* (§ I, axiom-free). And the behaviour that never reaches
a leaf is **unique**: it is `natInfinity` (§ II, `notEL_unique`). So the non-terminating bottom
is pinned by a purely negative description — by what it never does — with no element-hood in any
machine carrier assumed. A self-looping configuration unfolds to exactly that point (§ III).

**Why this shape matters.** The framework's other apophatic characterization with uniqueness is
set-theoretic (`quine_unique`). This is its computational counterpart, and unlike the ZP-K
identification it is a Lean `=` inside a single type, not a cross-type reading.

**Prior art — this is known, and the delta runs against us (recorded 2026-07-27).**
`notEL_unique` is **Escardó's `not-finite-is-∞'`** (TypeTopology, module
`TypeTopology.GenericConvergentSequence`), and his `CoNaturals.UniversalProperty` proves ℕ∞ is
the final coalgebra of `𝟙 + (−)` by the same bisimulation route. **His proof is `--safe
--without-K` from function extensionality alone**, where ours carries `Classical.choice` from
Mathlib's QPF quotient — so the standard version is not merely prior, it is purer, and that is
a live purity lead. The classical home is **Rutten, "Universal coalgebra: a theory of systems",
TCS 249 (2000)**, which supplies the **carrier and its finality**: p. 16, *"∞ only takes a step to
itself and hence never terminates"*; Ex. 10.2(4) p. 44 for `(ℕ̄, pred)` final; and the
**bisimulation technique on that carrier** at §12 pp. 51–52, where it is applied to arithmetic laws
(addition of naturals and its commutativity), *not* to this uniqueness statement. (Corrected
2026-07-29: an earlier revision said §12 ran "this exact bisimulation on this exact carrier" — the
technique and carrier are his, the application is not.) Mathlib itself has no `Conat` and no such
lemma, so the Lean formalization is a genuine small addition — the mathematics is not.

**And the framework already had it, in another dress:** `Miniature.lean`'s
`enat_fp_iff : x + 1 = x ↔ x = ⊤` is this same fact in the `ℕ∞ = WithTop ℕ` presentation.

**What is NOT claimed.** Which bottom the framework reads as such a behaviour, and that the reading
is a modelling commitment: the `loop_unfolds_to_infinity` entry of
`ZeroParadox/Computability/ComputationCannotBe.lean` § VIII. The results here are conditional on
non-termination. Nothing here makes the snap occur: occurrence is still
the halting problem (`occurs_iff_halts`, `occurrence_undecidable`). And the mathematics is not
new — the final coalgebra of `X ↦ 1 + X` being `ℕ ∪ {∞}` is standard (Jacobs, *Introduction to
Coalgebra*, Ex. 2.4.1 p. 66). **Note the scope of that citation:** Jacobs supports the *object*,
not the uniqueness *lemma*. **The uniqueness lemma is Escardó's** (`not-finite-is-∞'`, TypeTopology)
— Rutten never states it; his paper gives the carrier, its finality, and the bisimulation technique,
and uniqueness is a consequence he does not draw. (Attribution narrowed 2026-07-29: an earlier
revision credited the lemma to "Escardó and Rutten".) What is assembled here is the bridge, not the
coalgebra.

**Axiom footprint (measured, not quoted).** § I is axiom-free. § II and § III carry
`[propext, Classical.choice, Quot.sound]`, inherited from Mathlib's QPF machinery — so the
"already executing" half is free and the "is infinity" half is not.

## Structure

- § I   The head is `Bool` — there is no unstarted state (axiom-free)
- § II  The apophatic characterization, and its UNIQUENESS
- § III The bridge: a self-looping configuration unfolds to `natInfinity`
- § IV  NO-GO gauge: the forcing needs the binary split (a three-valued counter-model)
