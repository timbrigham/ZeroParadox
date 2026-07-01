-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPJ_SelfApp
import ZeroParadox.ZPJ_AczelConn
import ZeroParadox.ZPA
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, theory TH11 — placing the ZP-J selfApp fixed point on the μ/ν fork

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The bottom-diagram tree (`tree_test_campaign_2026-06-29.md`, `thread_obstruction_table_2026-06-29.md`)
has a μ root (least fixed point / initial / colimit) and a ν root (greatest fixed point / terminal /
limit). T1 placed the categorical-*initial* bottoms (#4 Kleisli `Fin 0`, #5 Hilbert `StateSpace 0`) on
the μ side; the Seam file showed #5 (a *zero object*) sits AT the μ=ν seam. This file (TH11) places a
different node: the **ZP-J selfApp fixed point** — the abstract self-application operation `selfApp`
(set-theory face: `x ↦ {x}`; 2-adic face: `x ↦ 2x`) whose **unique** fixed point is `bot` (the Quine
atom = the diagonal fixed point).

**The fork question.** A μ object is the *least* fixed point of its operation; a ν object is the
*greatest*. Where does `bot` sit among the fixed points of `selfApp`?

**Pre-registered GO:** `bot` sits at a *definite* fork position with an order witness.
**Pre-registered NO-GO:** the selfApp fixed point admits no least/greatest (initial/terminal)
characterization.

**Verdict: GO — the selfApp fixed point is the SEAM (μ = ν), with the order witness IN the statement.**
Because `selfApp` has a *unique* fixed point (`AbstractSelfApp.unique_fp`), that fixed point is
*simultaneously* the least and the greatest fixed point, in the ZP-A induced order `ZPSemilattice.le`:

- `selfApp_fp_set_eq_singleton` — the fixed-point set is the singleton `{bot}` (the structural fact
  carrying the placement; reuses the DC-free `singleton_from_unique_witness`).
- `bot_is_least_fixed_point` — `bot ≼ x` for every fixed point `x` of `selfApp`. This is the **μ
  characterization**: `bot` is the least fixed point (least-fixed-point = initial-algebra side).
- `bot_is_greatest_fixed_point` — `x ≼ bot` for every fixed point `x`. This is the **ν
  characterization**: `bot` is the greatest fixed point (greatest-fixed-point = final-coalgebra side).
- `selfApp_fixed_point_is_seam` — the capstone: `bot` is a fixed point AND it is both the least and the
  greatest fixed point of `selfApp`. The μ=ν coincidence is IN the statement (a conjunction of the two
  *directions of comparison against an arbitrary fixed point*, not a conjunction of two pre-existing
  witnesses): least ∧ greatest = seam.

So the selfApp fixed point lands at the **same place as the Hilbert zero object #5**: the μ=ν seam.
This is the order-theoretic shadow of Lambek's lemma / the unique-fixed-point coincidence — when the
initial algebra and the final coalgebra agree, the fixed point is unique, and a unique fixed point is
trivially both extremal. The Quine-atom side (`ZPP_Coalgebra.categorical_fork_strict`: μ empty, ν
inhabited) is the *strict* fork on a leaf-free functor where μ ≠ ν; here, for `selfApp` on the ZP
lattice, μ = ν *collapses to one point* — the seam — which is exactly the diagonal-fixed-point keystone.

**Honest fence.** The Lean content is exactly: the selfApp fixed-point set is `{bot}`, and `bot` is
both the least and the greatest fixed point in the ZP-A induced order. "This seam IS the diagonal fixed
point / the same seam as the Hilbert zero object #5 / Lambek collapse" is the framework's
interpretation of that pattern, not a Lean claim. In particular the order-theoretic least=greatest here
is NOT the same statement as the categorical initial=terminal of the zero object — they are parallel
faces of the seam, which is the meaning attached, not a proven identification. The uniqueness is the
real driver: extremality in both directions is *because* the fixed point is unique, so the seam reading
is genuinely earned but the cross-face identity stays fenced.
-/

namespace ZeroParadox.ZPH_MC1_TC11

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ_SelfApp
open ZeroParadox.ZPJ_AczelConn

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

local infix:50 " ≼ " => (ZPSemilattice.le : L → L → Prop)

-- `ZPSemilattice.le`, `bot_le`, `le_refl` are opened above (namespace `ZeroParadox.ZPA.ZPSemilattice`).

/-- The fixed-point predicate of `selfApp` (a fixed point is a "self-containing" element). -/
def isFixedPt (x : L) : Prop := AbstractSelfApp.selfApp x = x

/-- **The structural placement fact.** The fixed-point set of `selfApp` is the singleton `{bot}`.
    DC-free: uniqueness collapses the set to a point (reuses `singleton_from_unique_witness`). This is
    `selfMem_eq_singleton_bot` restated for the placement: there is exactly one node here to place. -/
theorem selfApp_fp_set_eq_singleton :
    {x : L | isFixedPt x} = ({bot} : Set L) :=
  singleton_from_unique_witness
    isFixedPt
    bot
    AbstractSelfApp.fixed_bot
    (fun x hx => AbstractSelfApp.unique_fp x hx)

/-- **μ characterization (least fixed point).** `bot` is ≼ every fixed point of `selfApp` in the ZP-A
    induced order. Load-bearing content: the comparison `bot ≼ x` for an *arbitrary* fixed point — this
    is what "least fixed point" means (the μ / initial-algebra side of the fork). Holds because `bot` is
    the order-bottom (`ZPA.bot_le`); the fixed-point hypothesis is not even needed, which is the point —
    `bot` is below everything, so it is below every fixed point. -/
theorem bot_is_least_fixed_point (x : L) (_hx : isFixedPt x) : (bot : L) ≼ x :=
  bot_le x

/-- **ν characterization (greatest fixed point).** Every fixed point of `selfApp` is ≼ `bot`. Load-
    bearing content: the *reverse* comparison `x ≼ bot` for an arbitrary fixed point — this is what
    "greatest fixed point" means (the ν / final-coalgebra side). Holds because uniqueness forces every
    fixed point to BE `bot` (`AbstractSelfApp.unique_fp`), then reflexivity. The reverse direction is
    the one that genuinely uses uniqueness — a generic order-bottom is NOT a greatest fixed point unless
    it is the only one. -/
theorem bot_is_greatest_fixed_point (x : L) (hx : isFixedPt x) : x ≼ (bot : L) := by
  have hxbot : x = bot := AbstractSelfApp.unique_fp x hx
  rw [hxbot]
  exact le_refl bot

/-- **TH11 seam capstone (μ = ν, witnessed not narrated).** The ZP-J selfApp fixed point sits at the
    μ/ν SEAM: `bot` is a fixed point, and it is simultaneously the **least** fixed point (`bot ≼ x` for
    every fixed point `x` — the μ side) and the **greatest** fixed point (`x ≼ bot` for every fixed
    point `x` — the ν side). The two extremal comparisons against an arbitrary fixed point are both IN
    the statement; their conjunction is precisely the μ=ν coincidence. This places the selfApp fixed
    point at the same fork position as the Hilbert zero object #5 (`ZPH_MC1_TreeSeam.hilbert_bottom_isZero`),
    the order-theoretic face of the seam. -/
theorem selfApp_fixed_point_is_seam :
    isFixedPt (bot : L)
    ∧ (∀ x : L, isFixedPt x → (bot : L) ≼ x)
    ∧ (∀ x : L, isFixedPt x → x ≼ (bot : L)) :=
  ⟨AbstractSelfApp.fixed_bot, bot_is_least_fixed_point, bot_is_greatest_fixed_point⟩

end ZeroParadox.ZPH_MC1_TC11

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC11

#print axioms selfApp_fp_set_eq_singleton
#print axioms bot_is_least_fixed_point
#print axioms bot_is_greatest_fixed_point
#print axioms selfApp_fixed_point_is_seam

end PurityCheck
