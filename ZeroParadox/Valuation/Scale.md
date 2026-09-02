# Scale — ride-along documentation

Moved from `ZeroParadox/Valuation/Scale.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## The road surface

ZeroParadox/Computability/SelfApp.lean reduced AFAStructure to AbstractSelfApp (two axioms: fixed_bot, unique_fp).
This file adds the next layer: a ValuationStructure that explains *why* ⊥ is the unique
fixed point — because scale strictly increases valuation, and ⊥ is the unique element
with infinite valuation. unique_fp becomes a theorem, not an axiom.

## The valuation argument

In ℚ_[2]: v₂(2x) = v₂(x) + 1 for x ≠ 0. Scale increases the 2-adic valuation by 1
each step. If 2x = x, then v₂(x) = v₂(x) + 1 — impossible for any finite valuation.
Only 0 has v₂ = ∞, and 2·0 = 0. So the fixed point of ×2 is exactly 0.

In ZPSemilattice: the same argument in the abstract. val : L → ℕ∞, val ⊥ = ⊤,
val strictly increases under scale. Unique fixed point = unique element with val = ⊤ = ⊥.

## What this derives without AFA

  ValuationStructure (scale + val axioms)
    → scale_ne_fixed (scale x ≠ x for x ≠ ⊥)
    → AbstractSelfApp (selfApp SUPPLIED as `selfApp := scale`; fixed_bot, unique_fp as theorems)
    → AFAStructure   (selfMem SUPPLIED by `def selfMemDerived`; bot_self_mem, quine_unique as theorems)

AFA content is derived from the valuation structure — not imported from Aczel.

⚠ **TWO of three at each step, never three.** A Lean typeclass field is either a LAW you discharge
with a proof or DATA you supply, and this chain supplies data at *both* steps — so "the fields
become theorems" counts a data field as a law. The measurement lives at
`ZeroParadox/Computability/SelfApp.lean` § III, and `tools/verify/check_fields.py` computes
`proved` against `supplied` from the Lean binding rather than from any wording here.

## What ZeroParadox/Valuation/ScaleBridge.lean resolved

The ZPSemilattice constraint was an encoding artefact: ValuationStructure required
[ZPSemilattice L] but the join operation ⊔ never appears in any of its four axioms.
ZeroParadox/Valuation/ScaleBridge.lean resolves this by defining ValBridge — the same four axioms
with bot as a plain field — and builds a formal ℤ_[2] instance using the standalone
theorems in §V below. A toValBridge instance makes any ZPSemilattice+ValuationStructure
type also a ValBridge instance, unifying both tracks under a common ancestor.
The formal gap described here is closed.
