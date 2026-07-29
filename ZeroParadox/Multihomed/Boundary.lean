import ZeroParadox.Computability.SelfApp
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic

/-!
# ZPJ — The well-foundedness boundary (keystone snap-as-boundary probe)

## Engineer's Take

Continuing to look at the shape of ZPJ, we pivoted from Lawvere to Taylor / AMM coalgebra. This was
mostly due to a gut reaction about the three failing cases, the original assessment, that they were
really the larger and more specific case for our framework. And if so, it gives the structure of our
binary snap an official home as a boundary crossing.

---

**Status: PROBE, stub-first, local branch `keystone-boundary`.** Rung A of the iterative A→B plan
(see `.claude-local/notes/wellfounded_coalgebra_foray_2026-06-23.md`).

Conjecture (Taylor/AMM framing): the forced snap ⊥→ε₀ crosses the **well-foundedness boundary** —
from the non-well-founded floor (⊥ is the self-loop / back edge, where recursion cannot reach,
Taylor Prop 111) to the well-founded ascent (the ε₀ ordinal tower, recursively generated).

**Rung A (this file): the RELATION-LEVEL form.** Mathlib has `WellFounded` and ordinal well-foundedness
but NOT Taylor's coalgebraic well-founded coalgebras — so this is the faithful relation-level *shadow*
of the Taylor boundary, not the full coalgebraic statement (that is Rung C, deferred). Honest scope: this
proves "the self-application floor is non-well-founded; the ordinal ascent is well-founded; the snap
crosses between," at the level of relations.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice ZeroParadox

set_option maxHeartbeats 400000

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-! ## § I. The floor is non-well-founded (the back edge)

    `selfApp` has ⊥ as a fixed point (`fixed_bot`): ⊥ self-loops. The relation "a is the selfApp-image
    of b" therefore has a self-loop at ⊥, so it cannot be well-founded. -/

/-- The descent relation induced by `selfApp`: `a` is the self-application image of `b`. -/
def floorRel (a b : L) : Prop := AbstractSelfApp.selfApp b = a

/-- An accessible point cannot have a self-loop (well-founded relations are irreflexive). -/
private theorem acc_irrefl {α : Type*} {r : α → α → Prop} : ∀ {a : α}, Acc r a → ¬ r a a := by
  intro a h
  induction h with
  | intro x _ ih => intro hself; exact ih x hself hself

/-- **The floor is non-well-founded.** ⊥ self-loops under `selfApp` (`fixed_bot`), so `floorRel` has a
    self-loop at ⊥ and cannot be well-founded — the back edge. -/
theorem floor_not_wellFounded : ¬ WellFounded (floorRel (L := L)) := fun hwf =>
  acc_irrefl (hwf.apply bot) AbstractSelfApp.fixed_bot

/-! ## § I-b. The INFINITE-POLE reading of the same floor — an infinite descent, not merely a loop

§ I states the floor's non-well-foundedness as a **self-loop** (`r x x`) — the EMPTY-pole form: nothing
below ⊥, the loop goes nowhere. The two-pole hard rule (`CLAUDE.md`) asks where the zero that runs to
infinity is, and the library already supplies the answer: well-foundedness is equivalent to the absence of
an **infinite descending chain** (the descending-chain condition), so the same fact reads as *"an infinite
descent issues from the floor."* That is the INFINITE pole of ⊥ in this face, and it is the one § I hides.

Standard form, read at source in the pinned Mathlib (`v4.30.0-rc2`):
* `wellFounded_iff_isEmpty_descending_chain` (`Mathlib/Order/WellFounded.lean:51`) —
  `WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n+1)) (f n) }`.
* `not_acc_iff_exists_descending_chain` (`:34`) — `¬ Acc r x ↔ ∃ f, f 0 = x ∧ ∀ n, r (f (n+1)) (f n)`;
  the **pointwise** version, which is what "at the floor" needs.

**Purity — MEASURED 2026-07-29, and the measurement overturned the expectation. Read this before
adopting the standard form anywhere else.** Mathlib's *extract-a-chain* direction (`:36-38`) builds the
sequence with `.choose_spec`, so it carries `Classical.choice`. The natural inference — "supply the witness
yourself and use only the other direction, and you stay choice-free" — is **FALSE**, and was measured false
here: `#print axioms` follows the **statement**, so citing the *biconditional at all* pulls in the choice
used by the direction you did not take. Measured footprints:

* `floor_descent_from_bot` — **does not depend on any axioms.** The explicit descent at ⊥ is free.
* `bot_not_acc` — **axiom-free**, but only because it is proved BY HAND from `fixed_bot`. The one-line
  version via `not_acc_iff_exists_descending_chain.mpr` measured `[propext, Classical.choice, Quot.sound]`.
* `floor_not_wellFounded_via_descent` — `[propext, Classical.choice, Quot.sound]`, inherited from
  `wellFounded_iff_isEmpty_descending_chain`. § I's `floor_not_wellFounded` is **axiom-free** and remains
  the load-bearing statement.

So this follows the `CovBy` precedent exactly: **keep the hand proof, cite the standard name.** The DCC
route is retained below for the citation and the reading, not as the cheapest proof — and the framework's
own rule applies (`CLAUDE.md`): inert-in-the-proof and absent-from-the-footprint are different properties;
measure, never infer.

**FENCE — the constant chain is the DEGENERATE descent.** The witness here is `fun _ => bot`, i.e. the
self-loop re-read as a chain; it is the *smallest* infinite descent, not a rich one. A genuine
non-constant descent is strictly more, and does **not** follow from a self-loop — `Occurrence.lean`'s
§ IV-b table already records the non-implication ("infinite descent through distinct states has no
self-loop"). So this section converts the empty-pole form into the infinite-pole form at ⊥; it does not
claim the floor hosts a non-degenerate descent. -/

/-- The floor's descending chain: the constant sequence at ⊥. Explicit (no choice), and a descending
    chain for `floorRel` precisely because ⊥ is a fixed point of `selfApp` (`fixed_bot`). -/
def floorDescent : ℕ → L := fun _ => bot

/-- **The floor hosts an infinite descent FROM ⊥** — the infinite-pole reading, pointwise at the bottom.
    `Statement:` there is a sequence starting at ⊥ that descends under `floorRel` at every step. The
    witness is `floorDescent`, so this is choice-free.
    `Reading:` the bottom is not a still point with nothing under it; the same configuration is an
    unending descent. Empty pole and infinite pole, one object. -/
theorem floor_descent_from_bot :
    ∃ f : ℕ → L, f 0 = bot ∧ ∀ n, floorRel (f (n + 1)) (f n) :=
  ⟨floorDescent, rfl, fun _ => AbstractSelfApp.fixed_bot⟩

/-- **⊥ is not accessible** — the empty pole stated as inaccessibility. Proved by hand from `fixed_bot`
    (via this file's `acc_irrefl`), **axiom-free**.
    That this is *equivalent* to the descent above is Mathlib's `not_acc_iff_exists_descending_chain`
    (`Order/WellFounded.lean:34`) — cited, deliberately **not** used: routing through that biconditional
    puts `Classical.choice` in the footprint (measured — see the purity note in § I-b). So "unreachable
    from below" and "an infinite descent issues from it" are the same fact about ⊥ in the two charts, and
    both halves are available here without choice. -/
theorem bot_not_acc : ¬ Acc (floorRel (L := L)) bot :=
  fun h => acc_irrefl h AbstractSelfApp.fixed_bot

/-- **§ I's conclusion, re-derived by the infinite-descent route.** Same statement as
    `floor_not_wellFounded`; different witness — there the self-loop contradicts accessibility, here an
    explicit infinite chain contradicts the descending-chain condition. Kept as a distinct declaration
    because the *route* is the content: it is the citation to the standard DCC characterization. -/
theorem floor_not_wellFounded_via_descent : ¬ WellFounded (floorRel (L := L)) := by
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff]
  exact ⟨⟨floorDescent, fun _ => AbstractSelfApp.fixed_bot⟩⟩

/-! ## § II. The ascent is well-founded (the ε₀ tower)

    The ordinal order is well-founded (ordinals are well-ordered); ε₀ and the snap ascent live inside it.
    This is the recursively-generated side — Taylor: well-founded ⟹ recursive. -/

/-- **The ascent is well-founded.** The strict order on ordinals is well-founded; the ε₀ tower (ZP-L)
    is an initial segment of it. -/
theorem ascent_wellFounded : WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  Ordinal.lt_wf

/-! ## § III. The boundary (Rung A statement)

    The snap crosses from the non-well-founded floor to the well-founded ascent. -/

/-- **Rung A — the well-foundedness boundary (relation level).** The floor relation is non-well-founded;
    the ascent relation is well-founded. The snap ⊥→ε₀ crosses between them. -/
theorem snap_crosses_boundary :
    ¬ WellFounded (floorRel (L := L)) ∧ WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  ⟨floor_not_wellFounded, ascent_wellFounded⟩

/-! ## § IV. Rung B — the snap as ONE crossing on a single carrier

    Glue the self-looping floor and the ordinal ascent into one carrier `Phase`, and show the
    non-well-foundedness is localized entirely at the floor: every post-snap state is accessible, the
    floor alone is not. The snap is the irreversible exit `floor ↦ up 0`.

    MODELING NOTE (honest): the carrier + relation are a *modeling choice* (how the floor, the ascent,
    and the irreversible snap are represented). Given that model the theorems below are proven — B2
    nontrivially, by ordinal well-founded induction. So "the snap is one crossing" is a faithful,
    coherent MODEL whose content is the two proven endpoints + an identification — and that
    identification is NOT a new commitment: it is the framework's existing ⊥/ε₀ identification (MC-1,
    plus the ε₀ identity already open under OQ-E2). The floor endpoint is tied to ZP's real ⊥
    (`floor_not_wellFounded`, axiom-free); the abstract `Phase` carrier is the illustrative toy form
    (non-well-foundedness localized at the floor by construction). No new commitment is introduced. -/

/-- The combined carrier: the self-looping floor, and the ordinal-indexed ascent. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Illustrative single-carrier model for the well-foundedness boundary — floor (self-looping ⊥) + up : Ordinal → Phase (ε₀ ascent); phaseRel self-loops at the floor, follows ordinal < above it, snap := up 0 is the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent. A modeling choice (content = two proven endpoints + the existing ⊥/ε₀ identification MC-1/OQ-E2, no new commitment); the real-⊥ endpoint (floorRel/floor_not_wellFounded) is axiom-free on the actual lattice.
inductive Phase where
  | floor : Phase
  | up : Ordinal → Phase

/-- The combined descent relation: the floor self-loops (non-well-founded); the ascent follows ordinal
    `<` (well-founded); no cross edges — the snap is irreversible, not a descent edge. -/
def phaseRel : Phase → Phase → Prop
  | Phase.floor, Phase.floor => True
  | Phase.up a, Phase.up b => a < b
  | _, _ => False

/-- The snap: the irreversible exit from the floor to the first ascent state. -/
def snap : Phase := Phase.up 0

/-- **B1 — the whole carrier is non-well-founded** (floor self-loop). -/
theorem phase_not_wellFounded : ¬ WellFounded phaseRel := fun hwf =>
  acc_irrefl (hwf.apply Phase.floor) trivial

/-- **B2 — every post-snap state is accessible** (the ascent is well-founded; non-wf localized off the
    ascent), by ordinal well-founded induction. -/
theorem phase_acc_of_up (o : Ordinal) : Acc phaseRel (Phase.up o) := by
  induction o using Ordinal.lt_wf.induction with
  | _ o ih =>
    refine Acc.intro _ (fun y hy => ?_)
    cases y with
    | floor => simp only [phaseRel] at hy
    | up a => exact ih a hy

/-- **B3 — the crossing.** The floor is the sole non-accessible point; every post-snap state is
    accessible. The snap exits the unique non-well-founded point into the well-founded ascent. -/
theorem snap_crossing :
    ¬ Acc phaseRel Phase.floor ∧ ∀ o : Ordinal, Acc phaseRel (Phase.up o) :=
  ⟨fun hacc => acc_irrefl hacc trivial, phase_acc_of_up⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms floor_not_wellFounded
#print axioms floor_descent_from_bot
#print axioms bot_not_acc
#print axioms floor_not_wellFounded_via_descent
#print axioms ascent_wellFounded
#print axioms phase_not_wellFounded
#print axioms phase_acc_of_up
#print axioms snap_crossing
end PurityCheck
