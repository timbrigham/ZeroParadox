-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the instance-vs-requirements gap ("can only characterize, never pin the instance") as an instance of the μ/ν fixed-point fork. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Settheory.ForkFrameChange
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The instance-vs-requirements gap as a fork instance (probe)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The framework keeps hitting a pattern: a structure provably meets a general schema's criteria, but we
may only say "it is *one witness* of [any object meeting the criteria]," never "it *is* the object."
(QuineHost: AFA is a witness, not the forced theory. MC-1: a family, not one object. ⊥ itself:
apophatic, never canonical.) The conjecture being probed is that the gap between *this one instance*
and *any object meeting the requirements* is the same self-referential 0↔∞ gap as everywhere else —
the diagonal fixed point.

This file makes the **object-level** half of that conjecture precise and checkable by reading it off
the ZP-P fork (`FixedPointFork.lean`). Nothing here is new order theory — it is a *renaming* of
`fork_collapse_iff` in the instance-vs-requirements language, plus the identity operator as the
maximal-gap witness, plus the observation that the fork is self-describing. What is genuinely
conjectural — the **meta-level** recursion (the fork reappearing at the level of the *characterization
itself*) and that *every* such gap is a fork — is fenced in § V and never asserted as a theorem.

Read "you can pin the instance" as `∃! x, P x`. For a fixed-point characterization `P x := f x = x`,
`fork_collapse_iff` says that is exactly the fork collapsing (`lfp = gfp`). So:
- **instance pinnable ⟺ fork collapses ⟺ the operator has a unique fixed point** (§ I),
- the fork's own detectors (`lfp`, `gfp`) are themselves fixed points — the measuring tool is an
  instance of the measured thing (§ II, the self-similar "right angle inside a right angle" seed),
- the identity operator flings the fork fully open — every object a witness, none *the* instance —
  the maximal gap, the fork image of "self-membership without a uniqueness clause admits everything"
  (§ III),
- the two open ends swap under the order dual (`ForkFrameChange`) — the "0" (μ, `lfp`) and "∞" (ν,
  `gfp`) poles of the gap are one structure seen from opposite sides (§ IV).

## Structure
- § I   The identification: instance pinnable ⟺ fork collapses
- § II  Self-similarity: the fork's detectors are themselves instances
- § III The maximal gap: the identity operator (every object a witness, none pinnable)
- § IV  The two poles: 0 (μ/lfp) and ∞ (ν/gfp) swap under the dual
- § V   FENCE: the meta-level recursion, and "every gap is a fork" (open, not a theorem)
-/

namespace ZeroParadox

variable {α : Type*} [CompleteLattice α]

/-! ## § I. The identification — instance pinnable ⟺ fork collapses -/

/-- **The gap is the fork.** For a fixed-point characterization `f x = x`, "the requirements pin a
unique instance" (`∃! x`) holds *iff* the fork collapses (`lfp = gfp`). This is `fork_collapse_iff`
renamed in the instance-vs-requirements language: uniqueness (the recurring `(Z)` requirement, e.g.
QuineHost `selfMem_unique`) is exactly the collapse condition, and its failure is exactly the gap. -/
theorem instance_pinnable_iff_fork_collapse (f : α →o α) :
    (∃! x, f x = x) ↔ f.lfp = f.gfp :=
  (fork_collapse_iff f).symm

/-- **The gap, negated form.** No unique instance is pinnable *iff* the fork is open (`lfp ≠ gfp`):
the "can only characterize, never instantiate" register is exactly a non-collapsed fork. -/
theorem no_pinnable_instance_iff_fork_open (f : α →o α) :
    (¬ ∃! x, f x = x) ↔ f.lfp ≠ f.gfp :=
  (instance_pinnable_iff_fork_collapse f).not

/-! ## § II. Self-similarity — the detectors are themselves instances -/

/-- **The right angle inside a right angle.** The fork's detectors `lfp` and `gfp` — the tools that
*measure* the gap — are themselves fixed points of `f`, i.e. instances of the very characterization
they measure. The gap detector is built out of the thing it detects: self-reference at the floor. -/
theorem detectors_are_instances (f : α →o α) :
    f f.lfp = f.lfp ∧ f f.gfp = f.gfp :=
  ⟨f.map_lfp, f.map_gfp⟩

/-- **Collapse resolves the self-reference.** When the fork collapses, the common detector *is* the
unique instance: every fixed point equals `lfp = gfp`. The measuring tool and the measured object
coincide — pinnable exactly when detector = instance. -/
theorem collapse_detector_is_the_instance (f : α →o α) (h : f.lfp = f.gfp) :
    ∀ y, f y = y → y = f.lfp :=
  unique_of_collapse f h

/-! ## § III. The maximal gap — the identity operator -/

/-- The least fixed point of the identity is `⊥`: `⊥` is a fixed point, and `lfp` is the least. -/
theorem id_lfp_bot : (OrderHom.id : α →o α).lfp = ⊥ :=
  le_antisymm (OrderHom.lfp_le_fixed OrderHom.id rfl) bot_le

/-- The greatest fixed point of the identity is `⊤`, dually. -/
theorem id_gfp_top : (OrderHom.id : α →o α).gfp = ⊤ := by
  apply le_antisymm le_top
  apply OrderHom.le_gfp
  simp

/-- **The maximal gap.** In any nontrivial complete lattice the identity's fork is flung fully open:
`lfp = ⊥ ≠ ⊤ = gfp`. Every element is a fixed point, so *every object is a witness* and the
requirement is vacuous — no instance is pinnable. This is the fork image of "self-membership without
a uniqueness clause admits everything" (the Boffa shape: `boffa_fails_unique`). -/
theorem id_fork_open [Nontrivial α] :
    (OrderHom.id : α →o α).lfp ≠ (OrderHom.id : α →o α).gfp := by
  rw [id_lfp_bot, id_gfp_top]
  exact bot_ne_top

/-- Consequently the identity pins no unique instance: the maximal instance-vs-requirements gap. -/
theorem id_no_pinnable_instance [Nontrivial α] :
    ¬ ∃! x : α, (OrderHom.id : α →o α) x = x :=
  (no_pinnable_instance_iff_fork_open OrderHom.id).mpr id_fork_open

/-! ## § IV. The two poles — 0 (μ / lfp) and ∞ (ν / gfp) swap under the dual -/

/-- **The gap's two poles are one structure, dually.** The μ-floor (`lfp`) of `f` is the ν-ceiling
(`gfp`) of the order-dual operator, and vice versa. So the "0" and "∞" ends of the gap are the same
fork seen from opposite poles — the rInv / frame-change of `ForkFrameChange`, read here as: the
located-instance side and the unbounded-witness side are one object. -/
theorem gap_poles_swap_under_dual (f : α →o α) :
    (OrderHom.dual f).lfp = f.gfp ∧ (OrderHom.dual f).gfp = f.lfp :=
  ⟨lfp_dual_eq_gfp f, gfp_dual_eq_lfp f⟩

end ZeroParadox

/-!
## § V. FENCE — the meta-level recursion (open conjecture, NOT proved here)

What is proved above is entirely **object-level**: for a single operator `f`, the instance-vs-
requirements gap is its fork. Two things are conjectural and deliberately unproved:

1. **The meta-level recursion (the "double dereference").** When the fork is open you cannot pin the
   instance, so you ascend to the *characterization* itself (the predicate `f x = x`) — the
   requirements. The same collapse question then applies one level up: is the *characterization*
   uniquely realized (is AFA the only theory meeting the requirements)? The conjecture is that this
   ascent is the fork applied to itself — `detectors_are_instances` (§ II) is its base case (the fork
   is already built from the fixed points it characterizes), but the full self-applied fork on the
   space of characterizations is not formalized here.

2. **"Every gap is a fork."** That *every* instance-vs-requirements gap in the framework is an
   instance of this μ/ν schema. This is the same soft fence ZP-P (`FixedPointFork.lean`) already
   carries for its instance catalogue; this probe adds the instance-vs-requirements reading, not a
   proof of the universal.

Both are connection/architecture conjectures of the same status class as "the keystone is a
manifestation of Lawvere" — never a Lean claim. The candidate standard-math home for making (1)
precise is Yoneda / representability (an object is its relational signature `Hom(-, X)`;
instance-vs-requirements = representable-vs-general-presheaf; representability being what may fail).
See `.claude-local/notes/instance_vs_requirements_gap_2026-07-15.md`.

## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms instance_pinnable_iff_fork_collapse
#print axioms no_pinnable_instance_iff_fork_open
#print axioms detectors_are_instances
#print axioms collapse_detector_is_the_instance
#print axioms id_lfp_bot
#print axioms id_gfp_top
#print axioms id_fork_open
#print axioms id_no_pinnable_instance
#print axioms gap_poles_swap_under_dual

end PurityCheck
