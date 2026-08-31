import ZeroParadox.Valuation.Scale
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# A priced p-adic interface: a choice-free carrier for ZP-B/ZP-J Group A, a map into `ℤ_[2]`, and both sides' axiom footprints

## Engineer's Take

Same interface move as the ordinal side, on the p-adic carrier. You take a class that came in one order
of magnitude too big and you initialize the single instance you actually needed, then cross reference it
back to the general one.

The point of the roots work was to separate where choice is used from where it is needed, and a footprint
only ever shows you the first. Build the carrier small enough to state the Group A content without the
whole Padic type, and the only choice left is what you pay at the crossing.

The surprise was that the price was not all p-adic. The still machinery is priced and the motion is free,
and that interface between the constructive side and the choice side is the thing worth having.

## Formal Overview
A choice-free carrier for the ZP-B/ZP-J Group A content, a named map into `ℤ_[2]`, and the axiom
footprint of each side measured rather than assumed. The rationale, the measured prices, the
fences on what is NOT proved, and the prior art on the carrier are in
`ZeroParadox/Valuation/PricedPadicInterface.md`, beside this file.
-/

namespace ZeroParadox

open scoped ENat

/-! ## § I. The valuation face — `v2` on ℕ

A choice-free 2-adic valuation into `ℕ∞`, and the four ZP-J `ValuationStructure` axioms
(`ValuationStructure`, in `ZeroParadox/Valuation/Scale.lean`) instantiated on ℕ with
`scale = (2 * ·)`. Compare `q2Val_bot`, `q2Val_unique`, `q2Scale_bot` and `q2Scale_unique_fp` in the
same file, which prove the same four in `ℤ_[2]` and carry `Classical.choice`. -/

/-- **The 2-adic valuation counter on ℕ, by structural fuel recursion.** `v2nat n f` counts factors of
2 in `n`, using `f` as a structurally-decreasing fuel; for `f ≥ n` the fuel is always sufficient
(`v2nat_stable`). Structural recursion, so no well-founded-recursion apparatus and no choice. -/
def v2nat : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, f + 1 => if n % 2 = 1 then 0 else if n = 0 then 0 else v2nat (n / 2) f + 1

/-- **The 2-adic valuation on ℕ, into `ℕ∞`.** `v2 0 = ⊤` (the bottom has infinite valuation); a
nonzero `n` gets the finite count `v2nat n n`. Choice-free. -/
def v2 (n : ℕ) : ℕ∞ := if n = 0 then ⊤ else (v2nat n n : ℕ∞)

/-! ### Fuel saturation

`v2nat n f` is constant once `f ≥ n`, so `v2` (which uses fuel `= n`) is well-behaved. These lemmas
are the only non-immediate step in the valuation face, used once to prove `v2_scale_nat`. -/

/-- The recursion step, as a rewrite. -/
theorem v2nat_succ (n f : ℕ) :
    v2nat n (f + 1) = if n % 2 = 1 then 0 else if n = 0 then 0 else v2nat (n / 2) f + 1 := rfl

/-- One extra unit of fuel does not change the value, once there is already enough. -/
theorem fuel_irrel (b a : ℕ) (h : a ≤ b) : v2nat a b = v2nat a (b + 1) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.le_zero.mp h
      subst ha; rfl
  | succ b ih =>
      rw [v2nat_succ, v2nat_succ]
      by_cases h1 : a % 2 = 1
      · rw [if_pos h1, if_pos h1]
      · by_cases h0 : a = 0
        · rw [if_neg h1, if_pos h0, if_neg h1, if_pos h0]
        · rw [if_neg h1, if_neg h0, if_neg h1, if_neg h0]
          have hle : a / 2 ≤ b := by omega
          rw [ih (a / 2) hle]

/-- Adding any amount of fuel beyond a sufficient amount does not change the value. -/
theorem v2nat_add (k a b : ℕ) (h : a ≤ b) : v2nat a (b + k) = v2nat a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show b + (k + 1) = (b + k) + 1 from by ring, ← fuel_irrel (b + k) a (by omega), ih]

/-- Any fuel `≥ n` computes the same value as fuel `= n`. -/
theorem v2nat_stable (f n : ℕ) (h : n ≤ f) : v2nat n f = v2nat n n := by
  rw [show f = n + (f - n) from by omega]
  exact v2nat_add (f - n) n n (le_refl n)

/-- **ZP-J `val_bot`, choice-free.** The bottom has infinite valuation. (Mirror of `q2Val_bot`.) -/
theorem v2_bot : v2 0 = ⊤ := by simp [v2]

/-- **ZP-J `val_unique`, choice-free.** Only the bottom has infinite valuation. (Mirror of
`q2Val_unique`.) -/
theorem v2_unique (n : ℕ) (h : v2 n = ⊤) : n = 0 := by
  by_contra hn
  rw [v2, if_neg hn] at h
  simp at h

/-- **ZP-J `scale_bot`, choice-free.** Doubling fixes the bottom. (Mirror of `q2Scale_bot`.) -/
theorem nScale_bot : 2 * 0 = 0 := rfl

/-- **The `val_scale` content, choice-free.** Doubling raises the 2-adic count by one, off the bottom —
here with the successor taken on ℕ (`v2nat n n + 1`) and then cast, so the statement is choice-free.
This is the mathematical content of ZP-J's `val_scale` on this carrier; the one lemma needing fuel
saturation. Compare `v2_scale`, which states the same fact in the axiom's literal `+ 1`-in-`ℕ∞` form and
thereby inherits `Classical.choice` from the ambient `ℕ∞` LITERAL (`AddMonoidWithOne ℕ∞`), not from
the addition and not from the carrier. -/
theorem v2_scale_nat (n : ℕ) (hn : n ≠ 0) : v2 (2 * n) = ((v2nat n n + 1 : ℕ) : ℕ∞) := by
  have h2n : 2 * n ≠ 0 := by omega
  rw [v2, if_neg h2n]
  congr 1
  have e : v2nat (2 * n) (2 * n) = v2nat (2 * n) ((2 * n - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
  rw [e, v2nat_succ, if_neg (by omega : ¬ (2 * n) % 2 = 1), if_neg h2n,
      show (2 * n) / 2 = n from by omega, v2nat_stable (2 * n - 1) n (by omega)]

/-- **The `ℕ∞` numerals `0` and `1` carry `Classical.choice` — the localization instrument,
corrected twice.** ⚠⚠ EVERY FOOTPRINT HERE IS PIN-RELATIVE, NOT STRUCTURAL, and this one is known
to have moved: Brasca and Clemente (*Synthetic Differential Geometry in Lean*, arXiv:2603.17457,
§2.2) report that writing `(2 : R)` for a ring `R` USED to require choice through this same
`instOfNatAtLeastTwo` route, and that it was subsequently fixed in Mathlib. Their constraint forces
the audit ours only benefits from — the Kock–Lawvere axiom is inconsistent with excluded middle, so
for them a stray `Classical.choice` is a contradiction rather than a blemish. Read every claim below
as "measured at the pinned Mathlib, 2026-08-30", never as a fact about the library.
⚠ Numerals ≥ 2 are CLEAN AT THE PIN: `(2 : ℕ∞)` is `[propext]`, resolving through
`instOfNatAtLeastTwo` and `Nat.cast`. Only `0` and `1` are tainted, and through DIFFERENT
bundles: `1` via `instAddMonoidWithOneENat` (the `AddMonoidWithOne ℕ∞`), `0` via
`instCommSemiringENat` (the `CommSemiring ℕ∞`). ⚠ Cite the INSTANCES, not their projections:
`AddMonoidWithOne.toOne` is itself axiom-free.
⚠⚠ This docstring previously said ℕ∞ ADDITION is classical "regardless of the summands". That is
FALSE, measured 2026-08-30: `Add ℕ∞`, `HAdd ℕ∞ ℕ∞ ℕ∞`, `NatCast ℕ∞` and `(a : ℕ∞) + (b : ℕ∞)`
all report NO axioms. What carries choice is the LITERAL: `One ℕ∞`, `OfNat ℕ∞ 1` and the bundled
`AddMonoidWithOne ℕ∞` — and `Zero ℕ∞` / `OfNat ℕ∞ 0` likewise. Hence `(a : ℕ∞) + 1` carries it
and `(a : ℕ∞) + ((1 : ℕ) : ℕ∞)` does not.
The CONCLUSION stands and is confirmed directly — `#print axioms ValuationStructure` reports
`Classical.choice`, so `val_scale` as spelled costs choice on every carrier — but it follows from
the numeral, not from the operator. ⚠ And this theorem does not witness it: the same proposition
proved by `induction b with | zero => rfl | succ n ih => rfl` reports NO axioms, so the footprint
below comes from THIS proof term, not from any instance in the statement. An instance's footprint
must be EMITTED, never inferred from a theorem that mentions it. -/
-- ⚠ THE NAME RECORDS THE ORIGINAL, MISTAKEN DIAGNOSIS and is kept as a stable handle (R-NAMING:
-- never rename a formal identifier). The choice is the NUMERAL, not the addition, and this
-- theorem's own footprint is its proof term's — the same proposition proved by induction and
-- `rfl` is axiom-free. Same technique, one domain over: ZeroParadox/Ordinal/SyntacticCollapse.lean
-- pins Mathlib's ℚ instances the same way, by a `rfl` proof that still reports choice.
theorem enat_add_choice (a b : ℕ) : (a : ℕ∞) + (b : ℕ∞) = ((a + b : ℕ) : ℕ∞) :=
  (Nat.cast_add a b).symm

/-- **ZP-J `val_scale`, literal form — carries the `ℕ∞`-NUMERAL choice.** The same fact as
`v2_scale_nat`, written with the successor in `ℕ∞` exactly as the ZP-J axiom states it (`val x + 1`).
Its footprint is `[propext, Classical.choice, Quot.sound]`, from the `ℕ∞` numeral (`One ℕ∞`), NOT from
the addition. ⚠ On THIS carrier (ℕ) that is the whole story. On ℤ_[2] it is not: `PadicInt` itself
carries `Classical.choice`, so `q2Val_scale` would be tainted even with a choice-free numeral, and
the two contributions do NOT separate there. -/
theorem v2_scale (n : ℕ) (hn : n ≠ 0) : v2 (2 * n) = v2 n + 1 := by
  rw [v2_scale_nat n hn, v2, if_neg hn, Nat.cast_add_one]

/-- **The fixed-point content, choice-free.** The bottom is the unique fixed point of doubling. (Mirror
of `q2Scale_unique_fp`.) -/
theorem nScale_unique_fp (n : ℕ) (h : 2 * n = n) : n = 0 := by omega

/-- Doubling moves everything except the bottom. (Mirror of `scale_ne_fixed`.) -/
theorem nScale_ne_self (n : ℕ) (hn : n ≠ 0) : 2 * n ≠ n := by omega

/-! ## § II. The ball face — digit streams

`Str := ℕ → Fin 2`, the 2-adic digit streams. `AgreeTo n` is the ball "agree to depth n"; `Apart` is
its positive complement. All choice-free — provided separation takes the positive hypothesis. -/

/-- **2-adic digit streams.** -/
abbrev Str : Type := ℕ → Fin 2

/-- The bottom stream (all zero digits) — the digit expansion of the bottom. -/
def botStr : Str := fun _ => 0

/-- **The ball relation: `x` and `y` agree to depth `n`.** -/
def AgreeTo (n : ℕ) (x y : Str) : Prop := ∀ i, i < n → x i = y i

/-- **Positive apartness.** There is a depth at which the two streams differ. This is the constructive
complement of equality — the hypothesis under which separation is choice-free. -/
def Apart (x y : Str) : Prop := ∃ n, x n ≠ y n

/-- Agreement to a fixed depth is decidable — a bounded quantifier over decidable equality on `Fin 2`.
This is the decidability that makes `clopen_gap_at_bot` choice-free. -/
instance decidableAgreeTo (n : ℕ) (x y : Str) : Decidable (AgreeTo n x y) :=
  Nat.decidableBallLT n (fun i _ => x i = y i)

/-- **Ultrametric strong triangle, depth form.** Agreement to a fixed depth is transitive. -/
theorem agree_trans (n : ℕ) (x y z : Str) (hxy : AgreeTo n x y) (hyz : AgreeTo n y z) :
    AgreeTo n x z := fun i hi => (hxy i hi).trans (hyz i hi)

/-- **Nested balls.** Agreeing to depth `n` implies agreeing to any shallower depth. -/
theorem agree_mono {m n : ℕ} (hmn : m ≤ n) (x y : Str) (h : AgreeTo n x y) :
    AgreeTo m x y := fun i hi => h i (lt_of_lt_of_le hi hmn)

/-- **Descent to a single point: `⋂ₙ Bₙ(x) = {x}`.** Agreeing to every depth is equality. The forward
direction is `funext`. -/
theorem agree_all_iff (x y : Str) : (∀ n, AgreeTo n x y) ↔ x = y := by
  constructor
  · intro h; funext i; exact h (i + 1) i (Nat.lt_succ_self i)
  · rintro rfl n i _; rfl

/-- **Separation from apartness.** If two streams are apart, some ball separates them. Takes the
positive `Apart` hypothesis — this is exactly where a negative `x ≠ y` would force choice. -/
theorem separated_of_apart (x y : Str) (h : Apart x y) : ∃ n, ¬ AgreeTo n x y := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + 1, fun hag => hm (hag m (Nat.lt_succ_self m))⟩

/-- **The gap at the bottom is decidable (the constructive content of "clopen").** For every depth,
either `x` is in the ball around the bottom stream or it is not — no intermediate. This is the
step-function character of p-adic balls, choice-free via decidability of a bounded quantifier. -/
theorem clopen_gap_at_bot (n : ℕ) (x : Str) :
    AgreeTo n botStr x ∨ ¬ AgreeTo n botStr x := by
  rcases decidableAgreeTo n botStr x with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Agreement at every depth is incompatible with apartness. -/
theorem not_apart_of_agree_all (x y : Str) (h : ∀ n, AgreeTo n x y) : ¬ Apart x y := by
  rintro ⟨m, hm⟩
  exact hm (h (m + 1) m (Nat.lt_succ_self m))

/-! ## § III. The crossing — one named map into `ℤ_[2]`

This is where the classical assumption is paid. `natToZ2` is `Nat.cast`; `q2Val`
(`ZeroParadox/Valuation/Scale.lean`) is the choice-carrying 2-adic valuation on `ℤ_[2]`. Expect
`[propext, Classical.choice, Quot.sound]` at every declaration here. -/

/-- **The crossing map.** The canonical ring map ℕ → `ℤ_[2]`. -/
noncomputable def natToZ2 (n : ℕ) : ℤ_[2] := (n : ℤ_[2])

/-- The crossing respects the bottom: 0 goes to 0. -/
theorem natToZ2_bot : natToZ2 0 = 0 := by rw [natToZ2, Nat.cast_zero]

/-- The crossing respects the scale: doubling on ℕ maps to doubling on `ℤ_[2]`. -/
theorem natToZ2_scale (n : ℕ) : natToZ2 (2 * n) = 2 * natToZ2 n := by
  unfold natToZ2; push_cast; ring

/-- **The valuation crossing at the bottom.** The choice-free `v2` and the choice-carrying `q2Val`
agree at the bottom: both give `⊤`. Writing `q2Val` is the moment choice is paid; the equality is the
minimal statement that the crossing respects the valuation at the bottom. -/
theorem crossVal_bot_agrees : q2Val (natToZ2 0) = v2 0 := by
  rw [natToZ2_bot, q2Val_bot, v2_bot]

end ZeroParadox

/-! ## § IV. Axiom Purity Check — this block IS the deliverable

The two sides of the interface, measured. If this block ever prints something different from the
header's "measured price" section, the header is wrong and must be corrected to match the instrument —
the instrument is the deliverable. -/

section PurityCheck
open ZeroParadox

-- Constructive side: the valuation face. `v2_scale_nat` (the content) is choice-free; `v2_scale` (the
-- literal `ℕ∞` axiom form) carries `Classical.choice`, from the NUMERAL (`One ℕ∞`), not the addition.
-- ⚠ That localization holds on ℕ only. On ℤ_[2] nothing separates: the choice is INTRODUCED at
-- layer 0 (`padicValNat`), below the completion, and `Padic`/`PadicInt` INHERIT rather than add
-- it — which is why both report it. Every statement mentioning that carrier carries it.
#print axioms v2nat
#print axioms v2
#print axioms v2_bot
#print axioms v2_unique
#print axioms nScale_bot
#print axioms v2_scale_nat
#print axioms enat_add_choice
#print axioms v2_scale
#print axioms nScale_unique_fp
#print axioms nScale_ne_self

-- ⭐ THE NUMERAL CLAIM, EMITTED. The docstring at § I says the ℕ∞ numerals `0` and `1` carry
-- choice and that ≥ 2 do not. These print the three numerals THEMSELVES rather than the bundles
-- they resolve through. ⚠ Three prints settle three numerals; `≥ 2` beyond the `2` shown follows
-- from the shared `instOfNatAtLeastTwo` route, not from this list.
private def _enatZero : ℕ∞ := 0
private def _enatOne : ℕ∞ := 1
private def _enatTwo : ℕ∞ := 2
-- ⚠ The pair below is the LOAD-BEARING premise of `Scale.lean`'s `_VScast` counterfactual: the
-- addition is clean and only the numeral is not. It was asserted in this file and consumed in
-- that one, and printed at neither end until now.
private def _addOne (a : ℕ) : ℕ∞ := (a : ℕ∞) + 1
private def _addOneCast (a : ℕ) : ℕ∞ := (a : ℕ∞) + ((1 : ℕ) : ℕ∞)
#print axioms _enatZero
#print axioms _enatOne
#print axioms _enatTwo
#print axioms _addOne
#print axioms _addOneCast
#print axioms instAddMonoidWithOneENat
#print axioms instCommSemiringENat

-- Constructive side: the ball face.
#print axioms AgreeTo
#print axioms Apart
#print axioms agree_trans
#print axioms agree_mono
#print axioms agree_all_iff
#print axioms separated_of_apart
#print axioms clopen_gap_at_bot
#print axioms not_apart_of_agree_all

-- The crossing. This is where the price is paid.
#print axioms natToZ2
#print axioms natToZ2_bot
#print axioms natToZ2_scale
#print axioms crossVal_bot_agrees

-- The layered localization: the crossing's choice is paid at layer 0 (`padicValNat`), below the
-- completion, not at `Padic` or the field. Printed rather than asserted, so the header's localization
-- claim is reproducible. `Nat.find`/`Nat.findGreatest` — the axiom-free primitives for the same job —
-- are printed as the contrast.
#print axioms padicValNat
#print axioms Nat.maxPowDvdDiv
#print axioms multiplicity
#print axioms Padic
#print axioms PadicInt
#print axioms Nat.find
#print axioms Nat.findGreatest
end PurityCheck
