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

## Formal Overview
**Status: CORE.** The relation-level *shadow* of the Taylor/AMM well-foundedness boundary — the
self-application floor is non-well-founded, the ordinal ascent is well-founded, and the snap crosses
between. Rung C, the full coalgebraic statement, is **not** claimed. Status, scope and argument: `ZeroParadox/Multihomed/Boundary.md`.
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

Well-foundedness is equivalent to the absence of an infinite descending chain, so the floor's self-loop
re-reads as *an infinite descent issues from the floor* — the INFINITE pole the `r x x` form hides.
⚠ The witness is the **constant** chain, the degenerate descent; a non-constant one is strictly more
and does not follow. Measured footprints and the fence: `ZeroParadox/Multihomed/Boundary.md`. -/

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
    (`Mathlib/Order/WellFounded.lean`) — cited, deliberately **not** used: routing through that biconditional
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

/-! ### § I-c. The descent route, choice-free — and TWO separate sources of `Classical.choice`

The mathematics is not new; the delta is generality and purity. **Naming the successor is necessary but
not sufficient** — a nameable successor on a dirty carrier still costs choice from the LIBRARY, and the
one genuine SELECTION is the biconditional's own `mp`. The measured table and both sources: `ZeroParadox/Multihomed/Boundary.md`. -/

/-- **Generic, axiom-free: no member of an explicit descending chain is accessible.**
    `Statement:` given any `f : ℕ → α` descending under `r` at every step, no `f n` is `Acc r`.
    The one-directional, choice-free half of Mathlib's `not_acc_iff_exists_descending_chain`. -/
theorem not_acc_of_descent {α : Type*} {r : α → α → Prop} (f : ℕ → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : ∀ x, Acc r x → ∀ n, x ≠ f n := by
  intro x hx
  induction hx with
  | intro y _ ih =>
    intro n hn
    subst hn
    exact ih (f (n + 1)) (hf n) (n + 1) rfl

/-- **Generic, axiom-free: an explicit descending chain refutes well-foundedness.**
    `Statement:` any explicitly given `f : ℕ → α` descending under `r` witnesses `¬ WellFounded r`.
    The choice-free half of `wellFounded_iff_isEmpty_descending_chain`; use this rather than the
    biconditional wherever the chain is written down, and the footprint stays clean. -/
theorem not_wf_of_descent {α : Type*} {r : α → α → Prop} (f : ℕ → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : ¬ WellFounded r := fun hwf =>
  not_acc_of_descent f hf (f 0) (hwf.apply (f 0)) 0 rfl

/-- **§ I's conclusion by the descent route, now CHOICE-FREE.**
    `Statement:` `¬ WellFounded floorRel` — the same statement as `floor_not_wellFounded_via_descent`
    and the same witness (`floorDescent`), but routed through `not_wf_of_descent` instead of the
    biconditional, so the descending-chain reading of the floor is available without paying for the
    direction not taken. Measured axiom-free, against that one's
    `[propext, Classical.choice, Quot.sound]`.
    `Reading:` the pair is kept deliberately — the choice-carrying version is retained because its
    *citation* of the standard characterization is its content, and the two side by side are the
    cleanest exhibit that the footprint here is a property of the ROUTE, not of the statement. -/
theorem floor_not_wellFounded_via_descent' : ¬ WellFounded (floorRel (L := L)) :=
  not_wf_of_descent floorDescent (fun _ => AbstractSelfApp.fixed_bot)

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

/-! ## § III-b. Oscillation — excluded on the ascent, MANDATORY at the floor

A 2-cycle is an oscillation, so cycle-freeness is exactly the exclusion of liar-type flip-flop — and it
needs well-foundedness, which the floor provably lacks. **"The snap does not oscillate" is true above the
floor and false at it; do not state it unqualified.** Prior art and measured purity: `ZeroParadox/Multihomed/Boundary.md`. -/

/-- **No oscillation on the ascent.** No ordinal is reachable from itself by one-or-more `<`-steps, so the
    ε₀ ascent admits no cycle of any length — in particular no 2-cycle, i.e. no flip-flop between two
    ordinals. `Statement:` cycle-freeness of `<` on `Ordinal`, which is `wf_no_cycle` at
    `ascent_wellFounded`; proved directly here since `<` on ordinals is already transitive.

    **Prior art (cited, not reproved).** The inner step below — `TransGen (· < ·) a b → a < b` — is
    the forward direction of Mathlib's `Relation.transGen_eq_self` (`Mathlib/Logic/Relation.lean`,
    `[IsTrans α r] : TransGen r = r`), which `Ordinal` satisfies. The hand proof is kept per the
    `CovBy` precedent (keep the proof, cite the standard name); the footprint here is already
    `[propext, Classical.choice, Quot.sound]` from `Ordinal`, not from anything done here.
    The asymmetry route is `WellFounded.asymmetric` (`Mathlib/Order/RelClasses.lean`), whose
    `Std.Asymm` instance is registered for `IsWellFounded`. -/
theorem ascent_no_oscillation (o : Ordinal) :
    ¬ Relation.TransGen ((· < ·) : Ordinal → Ordinal → Prop) o o := by
  intro h
  have key : ∀ a b : Ordinal, Relation.TransGen (· < ·) a b → a < b := by
    intro a b hab
    induction hab with
    | single hlt => exact hlt
    | tail _ hlt ih => exact lt_trans ih hlt
  exact lt_irrefl o (key o o h)

/-- **A cycle at the floor — present, not merely permitted.** ⊥ is a fixed point of `selfApp`
    (`fixed_bot`), so `floorRel` relates ⊥ to itself and ⊥ lies on a 1-cycle. This is why
    `ascent_no_oscillation` cannot be extended downward: the hypothesis it needs is exactly what
    `floor_not_wellFounded` denies. -/
theorem floor_has_cycle :
    Relation.TransGen (floorRel (L := L)) ZPSemilattice.bot ZPSemilattice.bot :=
  Relation.TransGen.single AbstractSelfApp.fixed_bot

/-- **The oscillation split, in one statement.** Above the floor no cycle exists; at the floor one does.
    `Statement:` a conjunction of the two facts above, at two different relations on two different carriers.
    `Reading:` the framework's "the snap fires once and does not flip back" is the FIRST conjunct only — a
    statement about the ascent. The second conjunct is the floor's self-reference, and it is a cycle by
    construction. No cross-carrier identity is asserted; `Ordinal` and `L` are distinct types. -/
theorem oscillation_split (o : Ordinal) :
    ¬ Relation.TransGen ((· < ·) : Ordinal → Ordinal → Prop) o o
      ∧ Relation.TransGen (floorRel (L := L)) ZPSemilattice.bot ZPSemilattice.bot :=
  ⟨ascent_no_oscillation o, floor_has_cycle⟩

/-! ## § IV. Rung B — the snap as ONE crossing on a single carrier

Glue the self-looping floor and the ordinal ascent into one carrier `Phase`: non-well-foundedness is
localized entirely at the floor, and the snap is the irreversible exit `floor ↦ up 0`. The carrier is a
MODELING CHOICE and introduces no new commitment — what that means, exactly: `ZeroParadox/Multihomed/Boundary.md`. -/

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
-- § I-c: the same route WITHOUT the biconditional's inherited choice. Expected axiom-free.
#print axioms not_acc_of_descent
#print axioms not_wf_of_descent
#print axioms floor_not_wellFounded_via_descent'
#print axioms ascent_wellFounded
#print axioms ascent_no_oscillation
#print axioms floor_has_cycle
#print axioms oscillation_split
#print axioms phase_not_wellFounded
#print axioms phase_acc_of_up
#print axioms snap_crossing
end PurityCheck
