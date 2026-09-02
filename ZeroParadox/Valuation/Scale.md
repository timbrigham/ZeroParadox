# Scale — ride-along documentation

Moved from `ZeroParadox/Valuation/Scale.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## The road surface

ZeroParadox/Computability/SelfApp.lean reduced AFAStructure to AbstractSelfApp (two axioms: fixed_bot, unique_fp).
`ZeroParadox/Valuation/Scale.lean` adds the next layer: a ValuationStructure that explains *why* ⊥ is the unique
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
theorems in `ZeroParadox/Valuation/Scale.lean` § V. A toValBridge instance makes any ZPSemilattice+ValuationStructure
type also a ValBridge instance, unifying both tracks under a common ancestor.
The formal gap described in `ZeroParadox/Valuation/Scale.lean` § V is closed.

## § V — the 2-adic parallel: what holds, what is registered, and the prior art

`ZeroParadox/Valuation/Scale.lean` § V proves every `ValuationStructure` axiom in ℤ_[2] with
scale = ×2 and val = the 2-adic valuation.

**Two different questions, and § V answers both.** Whether a `ZPSemilattice ℤ_[2]` instance is
REGISTERED, and whether one EXISTS, are not the same question, and only the first is what
instance synthesis reports. Both are measured: `#synth` fails, because no such instance is
declared; and the existential is provable, because § V's closing example supplies a semilattice
with bottom 0 and discharges all four axioms over it. ⚠ So "ℤ_[2] cannot be a ValuationStructure
instance" is true only in the not-registered reading and false read modally. The related gap
once recorded at `ZeroParadox/Valuation/Scale.lean` § V — "a ZPSemilattice instance for a concrete
type carrying a ValuationStructure" — is CLOSED in two independent ways: ℕ∞ carries both structures (`instNatInfZPS` and
`instNatInfVal` in `ZeroParadox/Settheory/Model.lean`, which imports Scale.lean), and
`ZeroParadox/Valuation/ScaleBridge.lean` closes it for ℤ_[2] via `ValBridge`.

**Why ℤ_[2] and not ℚ_[2].** `PadicInt.valuation : ℤ_[2] → ℕ` is ℕ-valued, which is what makes
`q2Val_scale` provable. In ℚ_[2], `valuation : ℚ_[2] → ℤ` can be negative, and the `.toNat`
truncation makes the key identity false (take x = 2⁻¹). ⚠ That is a fact about a ℕ∞-TARGETED
valuation built by truncation — the only kind this class admits — and NOT a fact about ℚ_[2].
`Padic.addValuation : AddValuation ℚ_[2] (WithTop ℤ)` has no truncation, satisfies the same
identity, and is already used at `ZeroParadox/Valuation/ValuationAFA_Padic.lean`. The
obstruction is this class's ℕ∞ target, a design choice, not the field.

**Prior art, found 2026-09-01 and verified by compiling the reconstruction.**
`multiplicity_addValuation PadicInt.prime_p : AddValuation ℤ_[2] ℕ∞`
(`Mathlib/RingTheory/Valuation/PrimeMultiplicity.lean`) discharges all four axioms from stock
API at the same axiom footprint § V already emits. Its `val_scale` is strictly stronger:
unguarded, holding at 0 as well, because ⊤ + 1 = ⊤ in ℕ∞ — so `q2Val_scale`'s `x ≠ 0`
hypothesis is one this class does not need. ⚠ **`AddValuation.top_iff` does NOT cover the `val_bot` + `val_unique` pair on this
carrier, and this section claimed it did until 2026-09-01.** `top_iff` is stated over a
`[DivisionRing K]` (`Mathlib/RingTheory/Valuation/Basic.lean`, and its docstring says "on a
division ring"); ℤ_[2] is a discrete valuation ring, not a division ring, since 2 is not
invertible. The stock route to `val_unique` on ℤ_[2] is `emultiplicity_eq_top`
(`Mathlib/RingTheory/Multiplicity.lean`) with `FiniteMultiplicity.of_prime_left`
(`Mathlib/RingTheory/UniqueFactorizationDomain/Multiplicity.lean`): x ≠ 0 and 2 prime give
finite multiplicity, so val x ≠ ⊤. **The rest of the prior-art claim survives** — the type,
the footprint and the unguarded `val_scale` were all verified — and `top_iff` was standing
in for the one axiom it could not give. The hand-rolled chain is kept for readability; the pointer it
owed is now at the site.

**The classical names, both already in this corpus and neither previously cited at § V.**
`q2Val_unique` — "only 0 has infinite 2-adic valuation" — is SEPARATEDNESS of the 2-adic
filtration, i.e. Krull's intersection theorem: an element of every 2ⁿℤ₂ lies in ⋂ₙ 2ⁿℤ₂ = (0).
⚠ **This is a `Reading:`, not a claim about either proof term, and the 2026-09-01 version of
this paragraph got that wrong in both directions.** It moved the name off
`q2Scale_unique_fp` on the grounds that its proof is `linear_combination` with no
filtration in it — correct — and then attached it to `q2Val_unique` as though that proof
*did* contain the filtration. It does not: `q2Val_unique` is `split_ifs` on
`if x = 0 then ⊤ else ↑valuation`, so the infinite value at 0 is stipulated by a branch,
and `PadicInt.valuation` is ℕ-valued with no top element in it at all. **The separatedness
reading is about what the STATEMENT means, and neither proof term exhibits it.** ⚠ Nor does the
stock route: `FiniteMultiplicity.of_prime_left` runs on a `WfDvdMonoid` and carries no filtration
in its term either. What that route gives is the same STATEMENT reached from stock API —
finiteness of the multiplicity is the separatedness assertion, not a construction of it. The
classical name attaches to what is being said, and to none of the three proofs that say it.

`q2Scale_unique_fp` does carry a second, legitimate **reading**: it is the uniqueness half of an
ATTRACTING FIXED POINT in the sense of Benedetto's non-Archimedean dynamics (multiplier 2, and
|2|₂ = 1/2 < 1, so all of ℤ_[2] lies in the basin). That is an interpretation of the STATEMENT,
never a claim about the proof term — the definition is already cited at
`ZeroParadox/Computability/Occurrence.md`, with the p-adic contraction result carried in
`ZeroParadox/Valuation/ContractionRate.lean`.

**Nearest in-corpus neighbour, uncited until 2026-09-01.** `BottomValuation` in
`ZeroParadox/Valuation/ValuationAFA.lean` carries `v_bot` and `v_top_unique` — the `val_bot` and
`val_unique` axioms verbatim, on the same ZPSemilattice carrier — and reaches `AFAStructure` by
a shorter route via `BottomValuation.toAFA`. Three formulations of one axiom pair live in this
directory (§ V, `BottomValuation`, and ScaleBridge's `ValBridge`); whether they merge is a
design question, that they point at each other is not.
