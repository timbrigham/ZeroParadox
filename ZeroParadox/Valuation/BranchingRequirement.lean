import ZeroParadox.Valuation.PadicTree
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A further requirement — the branching axis: branches are incomparable (the tower does not stack)

## Engineer's Take

I was curious whether there is another requirement, something like the branches not being able to sit
directly above one another as the tower rises. Trees grow outward and upward, and towers grow only upward,
so the branches not stacking is what makes this a field instead of a line. It is a real requirement, and the
pole corners do not carry it.

---

## Formal Overview (AI-assisted)

The four corners (`PoleCorners`) characterize the **pole** `{0, ∞}` — two elements — and say *nothing* about
branching. Tim's candidate further requirement: "branches can't be directly above one another as the tower
rises." Read precisely, that is **incomparability of branches**: the two children of a node are neither above
nor below each other in the prefix order (`branches_incomparable`), so the order is **not a chain** — it
genuinely branches. By self-similarity (`PadicTree.adj_prefix_iff`, every vertex roots an exact copy) the
same holds at every node, so the whole tree branches, never stacks.

**Why it is a genuine, INDEPENDENT requirement (not forced by the others).**
* The four corners live on a two-element pole — no branching structure exists there to force or forbid.
* `AbstractSelfApp` (the self-reference requirement) is satisfied by the non-branching two-element
  `OntologicalStates` (`Settheory/OntBridge.lean`) — so self-reference does **not** force branching.
* `InfinitudeFloor.member` is a single **chain** `ℕ → α` (`cx_member_strictMono`) — a rising line, the tower,
  not a branching tree.
So the current requirement set — four corners + `AbstractSelfApp` + `InfinitudeFloor` — is **partial**: none
of it captures branching. This answers the completeness question from the pole side with a clear *no*.

**Why it is LOAD-BEARING.** Branching (incomparable pairs) is exactly what makes the boundary a **continuum**
— the field ℤ₂, uncountably many ends (`PadicTree`, boundary ≅ ℤ₂) — rather than a single chain's single end
(a point). It is the requirement that supplies the *infinity* in "one instance out of infinity": with no
branching there is one instance; with it, infinitely many. The four corners fix the pole; this fifth
requirement is the **field-generating** axis, orthogonal to them — the tower rising without stacking is what
opens the field.

**Honest scope.** This file proves the *seed* — the two immediate branches are incomparable — and leans on
`adj_prefix_iff` for propagation and on `PadicTree`'s boundary ≅ ℤ₂ for the uncountable consequence. It does
NOT claim the requirement set is now complete; it identifies one previously-unabstracted requirement and
shows it is independent of the pole-side ones.
-/

namespace ZeroParadox

/-- **The branching seed.** The root's two children `[0]` and `[1]` are **incomparable** in the prefix order:
neither is directly above the other. This non-stacking is what makes the structure a tree (branching), not a
tower (a chain) — "branches can't be directly above one another." -/
theorem branches_incomparable :
    ¬ (([0] : List (Fin 2)) <+: ([1] : List (Fin 2))) ∧
      ¬ (([1] : List (Fin 2)) <+: ([0] : List (Fin 2))) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **No node is directly above its sibling branch.** For any vertex `v`, its two children `v ++ [0]` and
`v ++ [1]` are incomparable — the branching never collapses into a stack. (The root case is
`branches_incomparable`; this is its propagation to every node.) -/
theorem children_incomparable (v : List (Fin 2)) :
    ¬ (v ++ [0] <+: v ++ [1]) ∧ ¬ (v ++ [1] <+: v ++ [0]) := by
  constructor
  · intro h; exact (branches_incomparable.1) ((List.prefix_append_right_inj v).mp h)
  · intro h; exact (branches_incomparable.2) ((List.prefix_append_right_inj v).mp h)

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms branches_incomparable
#print axioms children_incomparable
end PurityCheck
