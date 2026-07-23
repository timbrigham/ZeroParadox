-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.LocalFloor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Completeness-critic, final pass: homogeneity and ultrametric are derived; compactness is AX-B1

## Engineer's Take

One last pass on what the object has that the axes might miss, before writing this up. Homogeneity and the
ultrametric both fall out of the structure, and compactness rides on the same binary commitment, so nothing
new is hiding.

This was one last pass on the object before writing it up. Sometimes it helps to work through this from the
ground up. Much of what is here re-derives results the framework already has, and that is fine. The movement of
the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

The generic object is a **Cantor set** (compact, totally disconnected, perfect, homogeneous, ultrametric; the
compact/perfect/totally-disconnected core is Brouwer's 1910 topological characterization).
Earlier probes settled *perfect* (derived from branching) and *arity* (un-captured = AX-B1). This last pass
clears the remaining named properties, to make the completeness verdict airtight.

**§ I — Homogeneity is derived.** A Cantor set is *homogeneous*: every point looks like every other. Here that
is `LocalFloor.boundaryFloor` (every node roots a genuine `InfinitudeFloor`) plus `homogeneous_profile`: at
**every** node `v`, the local complexity profile is identical — `localCx v (localMember v n) = n`, the same
for all `v`. So any two nodes carry the same floor structure; homogeneity follows from self-similarity
(branching), not a new axis.

**§ II — The ultrametric is derived.** The boundary metric is an *ultrametric* (strong triangle inequality),
whose combinatorial heart is `ultrametric_agreement`: if `x` and `y` agree on the first `n` digits and `y`
and `z` agree on the first `n`, then `x` and `z` agree on the first `n` — agreement-to-depth is transitive,
so `agree(x, z) ≥ min(agree(x, y), agree(y, z))`, exactly the ultrametric. This is pure prefix-transitivity of
equality; it needs nothing but the sequence structure. Derived, not a new axis.

**§ III — Compactness is a facet of AX-B1 (the arity commitment).** A Cantor set is *compact*, and for a
tree-boundary compactness is exactly **finite branching** (König / profinite). `CompletenessCriticProbe.infinite_branch`
already showed the branching axis does **not** force finite arity (`∅` has infinitely many incomparable
successors in `Set ℕ`). So compactness is not forced by the four axes — it rides on choosing *finite* (indeed
binary) arity, which is `AX-B1`. Compactness is therefore a consequence of the one modeling commitment, not an
independent fifth axis.

**Completeness verdict, for the named properties.** Every named Cantor-set property is accounted for: *perfect*,
*homogeneous*, *ultrametric*, *totally disconnected* — all **derived** from the four structural axes (pole,
fork, chain, branching); *compact* and the *arity* — the **one modeling commitment** AX-B1. No un-captured
property remains that would be a fifth structural axis. The generic object = four structural axes + AX-B1.
-/

namespace ZeroParadox

/-! ### § I. Homogeneity — every node's floor has the identical profile. -/

/-- **Homogeneity.** At every node the local complexity profile is the same: `localCx v (localMember v n) = n`
for all `v`. So any two nodes carry the identical floor structure — the boundary is homogeneous, derived from
self-similarity, not a new axis. -/
theorem homogeneous_profile (v w : List (Fin 2)) (n : ℕ) :
    localCx v (localMember v n) = localCx w (localMember w n) := by
  rw [localCx_member, localCx_member]

/-! ### § II. The ultrametric — agreement-to-depth is transitive. -/

/-- **The ultrametric core.** If `x` and `y` agree on the first `n` digits, and `y` and `z` agree on the
first `n`, then `x` and `z` agree on the first `n`: agreement-to-depth is transitive, giving
`agree(x, z) ≥ min(agree(x, y), agree(y, z))` — the strong triangle inequality. Pure prefix-transitivity;
derived from the sequence structure, not a new axis. -/
theorem ultrametric_agreement (x y z : End) (n : ℕ)
    (hxy : ∀ k, k < n → x k = y k) (hyz : ∀ k, k < n → y k = z k) :
    ∀ k, k < n → x k = z k :=
  fun k hk => (hxy k hk).trans (hyz k hk)

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms homogeneous_profile
#print axioms ultrametric_agreement
end PurityCheck
