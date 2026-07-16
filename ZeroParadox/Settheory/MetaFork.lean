-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the meta-level of the instance-vs-requirements fork — the "double dereference", the fork recurring on the space of a characterization's own witnesses. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.RequirementsGap
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The meta-level fork — the double dereference (probe)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`RequirementsGap.lean` proved the *object-level* half: the instance-vs-requirements gap for an
operator `f` is its μ/ν fork. This file probes the *meta-level* — the "double dereference": when the
fork is open you cannot pin the instance, so you ascend to the *characterization* (the predicate
`f x = x`, whose witnesses are `Fix(f)`) and ask the collapse question again, one level up.

The pivot is Knaster-Tarski (Mathlib `fixedPoints.completeLattice`): `Fix(f)` is itself a complete
lattice, with `⊥ = f.lfp` and `⊤ = f.gfp`. So the fork machinery recurs on `Fix(f)` verbatim — the
object-level theorems of `RequirementsGap` apply to their own fixed-point lattice. The natural
meta-operator is `f` restricted to its own fixed points; but `f` fixes every fixed point, so that
restriction is the **identity** on `Fix(f)`. By `id_fork_open`, the identity's fork is maximally open
exactly when `Fix(f)` is nontrivial — i.e. exactly when the object fork was open.

**The result being probed (H1):** the double dereference *reproduces the same gap*. The meta-fork
collapses iff the object fork collapses; ascending to the characterization returns the identical
collapse condition. The recursion is a fixed point — self-similar, depth-1 stable (the "right angle
inside a right angle" is the *same* angle). It is turtles all the way up unless some level supplies a
*new* collapsing operator, which is exactly `(Z)`/uniqueness one level up. Nothing here claims the
grand unification; the meta-recursion and "every gap is a fork" stay fenced (RequirementsGap § V).

## Structure
- § I   `Fix(f)` is a complete lattice; its `⊥`/`⊤` are the object fork ends
- § II  The meta-operator: `f` restricted to `Fix(f)` is the identity (the dereference)
- § III The meta-fork ends are the object fork ends
- § IV  Double dereference is idempotent: meta-collapse ⟺ object-collapse
- § V   The punchline: the meta-level reproduces the gap (turtles up)
-/

namespace ZeroParadox

open Function (fixedPoints)

variable {α : Type*} [CompleteLattice α] (f : α →o α)

/-! ## § I. `Fix(f)` is a complete lattice; its `⊥`/`⊤` are the object fork ends -/

/-- The bottom of the fixed-point lattice is the object's least fixed point (μ / lfp). -/
theorem fixedPoints_bot_val : (⊥ : fixedPoints f).val = f.lfp := rfl

/-- The top of the fixed-point lattice is the object's greatest fixed point (ν / gfp). -/
theorem fixedPoints_top_val : (⊤ : fixedPoints f).val = f.gfp := rfl

/-! ## § II. The meta-operator — `f` restricted to `Fix(f)` is the identity -/

/-- `f` acts as the identity on its own fixed points: every witness is fixed. This is the
"dereference" — passing from `f` to how `f` acts on the space of its own witnesses. -/
theorem f_id_on_fixedPoints (x : fixedPoints f) : f x.val = x.val := x.2

/-- The meta-operator: `f` restricted to its own fixed-point lattice. -/
def fMeta : fixedPoints f →o fixedPoints f where
  toFun x := ⟨f x.val, by rw [x.2]; exact x.2⟩
  monotone' _ _ hab := f.mono hab

/-- **The double dereference collapses to the identity.** `f` dereferenced onto the space of its own
witnesses is the identity operator — the second hop points back at the same objects. -/
theorem fMeta_eq_id : fMeta f = OrderHom.id := by
  ext x
  exact x.2

/-! ## § III. The meta-fork ends are the object fork ends -/

/-- The meta-fork's least fixed point is the object's `lfp` (via the identity's `lfp = ⊥`). -/
theorem meta_lfp_val : ((OrderHom.id : fixedPoints f →o fixedPoints f).lfp).val = f.lfp := by
  rw [id_lfp_bot]; rfl

/-- The meta-fork's greatest fixed point is the object's `gfp`. -/
theorem meta_gfp_val : ((OrderHom.id : fixedPoints f →o fixedPoints f).gfp).val = f.gfp := by
  rw [id_gfp_top]; rfl

/-! ## § IV. Double dereference is idempotent — meta-collapse ⟺ object-collapse -/

/-- **The recursion is a fixed point.** The meta-fork collapses iff the object fork collapses:
ascending to the characterization level returns the identical collapse condition. -/
theorem meta_collapse_iff_object_collapse :
    (OrderHom.id : fixedPoints f →o fixedPoints f).lfp
        = (OrderHom.id : fixedPoints f →o fixedPoints f).gfp
      ↔ f.lfp = f.gfp := by
  rw [id_lfp_bot, id_gfp_top, Subtype.ext_iff, fixedPoints_bot_val, fixedPoints_top_val]

/-! ## § V. The punchline — the meta-level reproduces the gap (turtles up) -/

/-- **The double dereference reproduces the gap.** No unique instance is pinnable at the meta level
iff the object fork was open — the gap ascends unchanged. Without a *new* collapsing operator (a
fresh `(Z)`/uniqueness one level up), it is turtles all the way up. -/
theorem meta_reproduces_gap :
    (¬ ∃! x : fixedPoints f, (OrderHom.id : fixedPoints f →o fixedPoints f) x = x)
      ↔ f.lfp ≠ f.gfp := by
  rw [no_pinnable_instance_iff_fork_open, ne_eq, meta_collapse_iff_object_collapse]

/-! ## § VI. The tower is stationary — turtles all the way up, unchanged -/

/-- The identity operator fixes everything: its fixed-point set is the whole type. -/
theorem id_fixedPoints_univ {β : Type*} [Preorder β] :
    fixedPoints (⇑(OrderHom.id : β →o β)) = Set.univ :=
  Set.eq_univ_of_forall (fun _ => rfl)

/-- **The tower is stationary.** The meta-operator is the identity (`fMeta_eq_id`), and the identity
fixes everything (`id_fixedPoints_univ`), so the *next* lattice up — the fixed points of the
meta-operator — is the whole meta lattice `Fix(f)` again. The ascent never refines: it reproduces the
same collapse condition at every level (`meta_collapse_iff_object_collapse`). The "right angle inside a
right angle" is the *same* angle, forever — a genuine fixed point of the ascend operation, not an
infinite regress and not a Lawvere-type diagonal obstruction. (This settles the *element-level* reading
only; the operator-level and model-level readings are separate — see the iteration log.) -/
theorem meta_operator_fixedPoints_univ :
    fixedPoints (⇑(fMeta f)) = Set.univ := by
  rw [fMeta_eq_id]; exact id_fixedPoints_univ

/-! ## § VII. Scale-invariance — the SAME fork law at every level -/

/-- **The gap law at the fixed-point level.** `instance_pinnable_iff_fork_collapse` is polymorphic over
complete lattices, so it applies verbatim to `Fix(f)` (itself a complete lattice): a meta-operator on
the witnesses pins a unique instance iff its fork collapses. Same theorem, one level up. -/
theorem gap_is_fork_at_meta (g : fixedPoints f →o fixedPoints f) :
    (∃! x, g x = x) ↔ g.lfp = g.gfp :=
  instance_pinnable_iff_fork_collapse g

/-- **The gap law at the operator level.** The space of operators `α →o α` is itself a complete
lattice (pointwise), so the very same law governs it: a meta-operator on *characterizations* pins a
unique characterization iff its fork collapses. The "double dereference" is not a new phenomenon — it
is one polymorphic fork law, recurring at every complete-lattice level (element, witness, operator).
No Lawvere-type diagonal appears; the recursion is scale-invariant. -/
theorem gap_is_fork_at_operators (Φ : (α →o α) →o (α →o α)) :
    (∃! g, Φ g = g) ↔ Φ.lfp = Φ.gfp :=
  instance_pinnable_iff_fork_collapse Φ

/-! ## § VIII. Why there is no diagonal — existence is free (Knaster-Tarski) -/

/-- **An instance always exists** (Knaster-Tarski): every monotone operator on a complete lattice has a
fixed point (`f.lfp`). So the gap is *never* about existence — only about uniqueness (the width of the
fork).

**No Lawvere obstruction at any lattice level.** Because existence is free at every complete-lattice
level — `α`, `Fix(f)`, `α →o α`, and up — the Lawvere / diagonal "no fixed point" obstruction *cannot*
occur anywhere in the meta-tower. The self-referential fixed point is always present; what can fail is
only its *uniqueness* (`fork_collapse_iff`). This is the precise reason the double dereference is
scale-invariant and hits no wall: monotonicity + completeness forbid the very obstruction the keystone
diagonal (Lawvere/Cantor/Russell, `Wall.lean`) is built from. The diagonal edge therefore lives strictly
OUTSIDE complete-lattice-land — in the well-foundedness / negation setting (`wf_no_selfloop`, where a
self-loop is *refuted*) and in the space of theories/models (candidate 2 — not a complete lattice, so no
fork law applies; the genuine apophatic "AFA vs any theory" gap). Within the lattice tower the gap is
uniqueness-only and self-similar; the wall is where you leave it. -/
theorem instance_always_exists : ∃ x, f x = x :=
  ⟨f.lfp, f.map_lfp⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms fixedPoints_bot_val
#print axioms f_id_on_fixedPoints
#print axioms fMeta_eq_id
#print axioms meta_lfp_val
#print axioms meta_collapse_iff_object_collapse
#print axioms meta_reproduces_gap

end PurityCheck
