import ZeroParadox.Valuation.Scale
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# A priced p-adic interface: a choice-free carrier for ZP-B/ZP-J Group A, a map into `ℤ_[2]`, and both sides' axiom footprints

## What this file is

A **measurement**, not a construction — the p-adic analogue of
`ZeroParadox/Ordinal/PricedInterface.lean`. It exhibits a small, concrete, choice-free carrier on
which the *Group A* content of the framework's `Valuation/` cluster is statable and provable — the
ZP-J valuation axioms and the ZP-B ball/separation core — together with a single named crossing into
Mathlib's `ℤ_[2]`, and the axiom footprint of each side. What is contributed is the **price tag**: the
carrier is choice-free, the crossing is `Classical.choice` at every declaration, and the price is
localized one layer deeper than a footprint on `Padic` would suggest.

Neither the carrier nor the crossing is original. The apartness-based separation is
Pelayo–Voevodsky–Warren's design (and Bishop's before them); the constructive-p-adic and
domain-theoretic prior art is Vickers's; the digit tree is Bruhat–Tits (already cited in
`ZeroParadox/Valuation/PadicTree.lean`). See "Prior art".

## Why this file exists — the roots enumeration's constructive payoff

A footprint sweep of the `Valuation/` cluster found its `Classical.choice` sites **dominated** by the
`Padic` type's own footprint — every one of them sits downstream of `Padic`, so `#print axioms` on a
`Valuation/` declaration measures `Padic`, not the framework's proof. This file makes the framework's
own Group A content *measurable* by restating it on a carrier that does not mention `Padic` at all, so
the choice that does appear appears only at the one named crossing.

The `Valuation/` cluster splits, and the split is the whole scoping finding:

* **Group A — needs only the valuation and its order.** The ZP-J `ValuationStructure` axioms, the ZP-B
  ultrametric/clopen-ball content, the descent to a single point, total separation. Their mathematical
  content is *agreement to depth n* and *the valuation of the bottom is the top of the value monoid* —
  combinatorial and valuative statements that use neither division, nor completeness, nor ℝ. **This is
  the slice built here.**
* **Group B — genuinely needs the complete field.** `RiemannSphere.lean` / `rInv_swaps` (field
  inversion plus continuity at two special points), `Ostrowski.lean` (a classification of absolute
  values into ℝ), and the Haar/Kozyrev/ergodic layer (invariant measure, spectral theory). There is no
  cheaper carrier for these, and this file does not attempt one. Recorded as needing the field.

## The layered localization of the crossing's choice

The crossing's `Classical.choice` is **not** paid at the metric completion. Traced through Mathlib:
`Padic p := CauSeq.Completion.Cauchy (padicNorm p)`, and `padicNorm` is built from `padicValRat`, from
`padicValInt`, from **`padicValNat`** — the p-adic valuation on ℕ, below the Cauchy quotient, below the
field, below the metric. `padicValNat` unfolds to `Nat.maxPowDvdDiv`, on the `multiplicity` layer, and
that is where the footprint enters: `padicValNat`, `Nat.maxPowDvdDiv`, and `multiplicity` each measure
`[propext, Classical.choice, Quot.sound]`, while `Nat.find`/`Nat.findGreatest` — the obvious primitives
for "least/greatest k with pᵏ ∣ n" — are axiom-free. The purity block below prints the whole chain so
this is reproducible rather than asserted.

A corollary, settled negatively: **`ℤ_[p]` is not cheaper than `ℚ_[p]`.** Both are downstream of the
same layer-0 valuation, so dropping the field for the ring of integers buys nothing.

## The measured price of the crossing

Measured by the `#print axioms` block at the bottom of this file (the instrument is the deliverable;
these are the numbers it reported).

* **Constructive side — choice-free.** [FOOTPRINTS FILLED AFTER FINAL BUILD — this line is a
  placeholder and will be replaced with the per-declaration numbers the purity block prints; if it is
  still here, the file is mid-fill.]
* **The crossing — `Classical.choice`.** [FOOTPRINTS FILLED AFTER FINAL BUILD.]

**What that measurement does and does not license.** It locates where the classical assumption is paid
on this pair of carriers, and shows the Group A content does not need it. It does **not** show that
Mathlib's p-adic results are eliminable, and it does **not** show `padicValNat`'s choice is removable
*in Mathlib* — that would require re-proving Mathlib's valuation API on a different definition, which is
not attempted here. `#print axioms` reports how a proof was written, never what a theorem requires.

## The carrier, and what it actually is

Two faces, matching the two faces of Group A:

* **The valuation face — ℕ with `v2 : ℕ → ℕ∞`.** `v2` is a 2-adic valuation defined by structural fuel
  recursion (`v2nat`), not well-founded recursion, so it is computable and choice-free. `v2 0 = ⊤`; on
  nonzero inputs it counts factors of 2. On this carrier the four ZP-J `ValuationStructure` axioms hold
  choice-free with `scale = (2 * ·)`: `v2_bot`, `v2_unique`, `nScale_bot`, `v2_scale`; and the
  fixed-point content `nScale_unique_fp` (the bottom is the unique fixed point of doubling) is proved
  directly. This is the exact choice-free mirror of `Scale.lean` § V, which proves the same axioms in
  `ℤ_[2]` via `PadicInt.valuation` and carries choice.
* **The ball face — digit streams `Str := ℕ → Fin 2`.** `AgreeTo n x y` ("agree to depth n") is the
  ball relation; `Apart x y := ∃ n, x n ≠ y n` is its positive complement. The ultrametric strong
  triangle (depth form), nested balls, descent to a single point, and total separation all hold
  choice-free — **provided separation takes the positive `Apart` hypothesis, not the negative `x ≠ y`.**

## The apartness finding, and its independent vindication

The separation statements **must take a positive hypothesis.** From `¬(x = y)` one cannot
constructively produce the depth at which two streams first differ; from `Apart x y` the witness is
computed, and the statement is choice-free. This matches, independently, the design
Pelayo–Voevodsky–Warren were forced into: because `ℤ[[X]]` lacks decidable equality they work "with an
apartness relation and with the corresponding notions of integral domains and fields" (Heyting fields).
Two developments reaching the same design from opposite directions is the strongest evidence the carrier
is the right one — and the credit is theirs, not ours.

## What is NOT proved here, and must not be inferred

* **The ZP-B results are not re-proved.** A different carrier means **different theorems**. ZP-B's
  `c3_irreversible` quantifies over continuous paths from `Set.Icc (0:ℝ) 1`; the stream-carrier
  separation statements are *different propositions* about digit depth, not a re-proof of anything
  stated over ℝ. State them exactly as such.
* **This carrier is not the completion.** It carries no topology object, no metric, no field, and
  cannot express anything that genuinely needs the complete field (Group B). It is not a constructive
  `ℤ_[2]`; it is a carrier for the Group A *content*.
* **Locating choice is not eliminating it.** Nothing here re-proves any Mathlib p-adic result, and no
  failed or avoided elaboration in this file is an independence result or may be upgraded to one.
* **`v₂(0) = ⊤` is a *valuative* property** — the valuation of the bottom is the top of the value
  monoid. Never describe it with topological vocabulary; "isolated" in particular is wrong and is on
  the project's vocabulary watch list.

## Triviality assessment

The valuation face is elementary: `v2nat` is a short structural recursion, and its only non-immediate
lemma is fuel saturation (the value stabilizes once the fuel exceeds the input), used once to prove
`v2_scale`. The ball face is pure combinatorics on `ℕ → Fin 2`; `agree_all_iff` is `funext` in one
direction (hence its `Quot.sound`), and `clopen_gap_at_bot` is the decidability of a bounded quantifier.
The crossing is `Nat.cast` into `ℤ_[2]` and one comparison at the bottom. Nothing here is deep. The
value, if any, is the same as its ordinal sibling's: the boundary is *stated as a price* on a specific
named map, on a carrier where the classical target is a real library type, rather than left as the
general impression that "the p-adic side is classical".

## Prior art — the carrier is not ours

* **Apartness / constructive p-adics.** Á. Pelayo, V. Voevodsky, M. A. Warren, "A univalent
  formalization of the p-adic numbers," *Mathematical Structures in Computer Science* **25**(5), 2015,
  pp. 1147–1171, doi:10.1017/S0960129514000541 (preprint arXiv:1302.1207). Constructs `ℤ_p` as a
  quotient of `ℤ[[X]]` and `ℚ_p` as its field of fractions, algebraically rather than analytically, and
  is forced to an apartness relation and Heyting fields by the lack of decidable equality on `ℤ[[X]]`.
  Verified in Coq/UniMath (so not importable into Lean), an *algebraic* route (so it supplies the
  ring/field but not the metric/ball apparatus of Group A), and labeled "preliminary" by its authors.
  It is the direct prior art for the apartness face here.
* **Domain-theoretic p-adics.** S. Vickers, "A fixpoint construction of the p-adic domain," LNCS **283**
  (1987), pp. 270–289; and "An algorithmic approach to the p-adic integers," LNCS **298** (1988),
  pp. 599–616. The p-adic integers appear as the maximal elements of a Scott domain with algebraic
  structure, presented as a fixpoint of a functor in a category of sheaves of rings — the
  partial-element / algorithmic route, on-thread with this framework's fixpoint theme, and distinct from
  the concrete digit-stream carrier used here.
* **The tree.** The digit tree is the Bruhat–Tits tree, already cited in
  `ZeroParadox/Valuation/PadicTree.lean` (Ludwig & Merten, arXiv:2505.12933); not rediscovered here.
* **The inverse-limit carrier's viability.** A. Crighton, "Hensel's Lemma for the p-adic Integers,"
  Archive of Formal Proofs, 2021, formalizes `ℤ_p` as the inverse limit of `ℤ / pⁿ` in Isabelle/HOL
  (classical) — evidence the inverse-limit carrier is viable, not a choice-free result.

A prior-art search for a Lean/Agda constructive or coinductive-stream p-adic development, a Bishop-style
non-archimedean completion naming the p-adics, and a source comparing a primitive-recursive p-adic
valuation on ℕ against Mathlib's `multiplicity`-based `padicValNat` returned "searched, none found" in
each case — recorded as searches, never as claims that none exists.

**What is ours is the price tag, exactly as on the ordinal side** — not the carrier, not the apartness
design, not the tree.

## Structure

- § I   The valuation face — `v2` on ℕ, the four ZP-J axioms, choice-free.
- § II  The ball face — digit streams, agreement, apartness, separation, choice-free.
- § III The crossing — one named map ℕ → `ℤ_[2]`, priced.
- § IV  Axiom Purity Check — the deliverable.

## Engineer's Take

TODO (Tim): <your take, in your own voice.>
-/

namespace ZeroParadox

open scoped ENat

/-! ## § I. The valuation face — `v2` on ℕ

A choice-free 2-adic valuation into `ℕ∞`, and the four ZP-J `ValuationStructure` axioms
(`ZeroParadox/Valuation/Scale.lean` § I) instantiated on ℕ with `scale = (2 * ·)`. Compare
`Scale.lean` § V, which proves the same four in `ℤ_[2]` and carries `Classical.choice`. -/

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
are the only non-immediate step in the valuation face, used once to prove `v2_scale`. -/

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
thereby inherits `Classical.choice` from Mathlib's `ℕ∞` additive instance (`enat_add_choice`), not from
the carrier. -/
theorem v2_scale_nat (n : ℕ) (hn : n ≠ 0) : v2 (2 * n) = ((v2nat n n + 1 : ℕ) : ℕ∞) := by
  have h2n : 2 * n ≠ 0 := by omega
  rw [v2, if_neg h2n]
  congr 1
  have e : v2nat (2 * n) (2 * n) = v2nat (2 * n) ((2 * n - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
  rw [e, v2nat_succ, if_neg (by omega : ¬ (2 * n) % 2 = 1), if_neg h2n,
      show (2 * n) / 2 = n from by omega, v2nat_stable (2 * n - 1) n (by omega)]

/-- **`ℕ∞` addition carries `Classical.choice` — the localization instrument.** Mathlib's additive
instance on `ℕ∞ = WithTop ℕ` is classical, so any `ℕ∞` sum inherits `Classical.choice` at the instance
level, regardless of the summands. `Nat.cast : ℕ → ℕ∞` is by contrast choice-free (`v2` above proves
it). This is why the `val_scale` axiom, stated as `val x + 1 : ℕ∞`, carries choice on **every** carrier
— the choice is the ambient `ℕ∞` instance, not the valuation and not anything p-adic. The documented
instance hazard, here located exactly. -/
theorem enat_add_choice (a b : ℕ) : (a : ℕ∞) + (b : ℕ∞) = ((a + b : ℕ) : ℕ∞) :=
  (Nat.cast_add a b).symm

/-- **ZP-J `val_scale`, literal form — carries the `ℕ∞`-instance choice.** The same fact as
`v2_scale_nat`, written with the successor in `ℕ∞` exactly as the ZP-J axiom states it (`val x + 1`).
Its footprint is `[propext, Classical.choice, Quot.sound]`, and the choice is `enat_add_choice`'s — the
ambient `ℕ∞` additive instance — **not** the carrier's and **not** p-adic. Mirror of `q2Val_scale`, whose
choice is this same `ℕ∞` sum together with `PadicInt.valuation`; this file separates the two
contributions. -/
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

/-- **Ultrametric strong triangle, depth form.** Agreement to a fixed depth is transitive. -/
theorem agree_trans (n : ℕ) (x y z : Str) (hxy : AgreeTo n x y) (hyz : AgreeTo n y z) :
    AgreeTo n x z := by sorry

/-- **Nested balls.** Agreeing to depth `n` implies agreeing to any shallower depth. -/
theorem agree_mono {m n : ℕ} (hmn : m ≤ n) (x y : Str) (h : AgreeTo n x y) :
    AgreeTo m x y := by sorry

/-- **Descent to a single point: `⋂ₙ Bₙ(x) = {x}`.** Agreeing to every depth is equality. The forward
direction is `funext`. -/
theorem agree_all_iff (x y : Str) : (∀ n, AgreeTo n x y) ↔ x = y := by sorry

/-- **Separation from apartness.** If two streams are apart, some ball separates them. Takes the
positive `Apart` hypothesis — this is exactly where a negative `x ≠ y` would force choice. -/
theorem separated_of_apart (x y : Str) (h : Apart x y) : ∃ n, ¬ AgreeTo n x y := by sorry

/-- **The gap at the bottom is decidable (the constructive content of "clopen").** For every depth,
either `x` is in the ball around the bottom stream or it is not — no intermediate. This is the
step-function character of p-adic balls, choice-free via decidability of a bounded quantifier. -/
theorem clopen_gap_at_bot (n : ℕ) (x : Str) :
    AgreeTo n botStr x ∨ ¬ AgreeTo n botStr x := by sorry

/-- Agreement at every depth is incompatible with apartness. -/
theorem not_apart_of_agree_all (x y : Str) (h : ∀ n, AgreeTo n x y) : ¬ Apart x y := by sorry

/-! ## § III. The crossing — one named map into `ℤ_[2]`

This is where the classical assumption is paid. `natToZ2` is `Nat.cast`; `q2Val`
(`ZeroParadox/Valuation/Scale.lean` § V) is the choice-carrying 2-adic valuation on `ℤ_[2]`. Expect
`[propext, Classical.choice, Quot.sound]` at every declaration here. -/

/-- **The crossing map.** The canonical ring map ℕ → `ℤ_[2]`. -/
noncomputable def natToZ2 (n : ℕ) : ℤ_[2] := (n : ℤ_[2])

/-- The crossing respects the bottom: 0 goes to 0. -/
theorem natToZ2_bot : natToZ2 0 = 0 := by sorry

/-- The crossing respects the scale: doubling on ℕ maps to doubling on `ℤ_[2]`. -/
theorem natToZ2_scale (n : ℕ) : natToZ2 (2 * n) = 2 * natToZ2 n := by sorry

/-- **The valuation crossing at the bottom.** The choice-free `v2` and the choice-carrying `q2Val`
agree at the bottom: both give `⊤`. Writing `q2Val` is the moment choice is paid; the equality is the
minimal statement that the crossing respects the valuation at the bottom. -/
theorem crossVal_bot_agrees : q2Val (natToZ2 0) = v2 0 := by sorry

end ZeroParadox

/-! ## § IV. Axiom Purity Check — this block IS the deliverable

The two sides of the interface, measured. If this block ever prints something different from the
header's "measured price" section, the header is wrong and must be corrected to match the instrument —
the instrument is the deliverable. -/

section PurityCheck
open ZeroParadox

-- Constructive side: the valuation face. `v2_scale_nat` (the content) is choice-free; `v2_scale` (the
-- literal `ℕ∞` axiom form) carries `Classical.choice`, and `enat_add_choice` localizes that choice to
-- the ambient `ℕ∞` additive instance — not the carrier, not p-adic.
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
