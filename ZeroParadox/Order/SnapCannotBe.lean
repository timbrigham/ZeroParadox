import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Reals.OrderedField

/-!
# Machine-checked characterization index of the snap ⊥ → ε₀ — what the snap IS and IS NOT

The snap counterpart of `ZeroParadox/BottomCannotBe.lean` and `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`,
closing the third leg of the trio. A `#check`-only index of established results characterizing the Binary
Snap ⊥ → ε₀ (T-SNAP), organized into **IS NOT** and **IS**. This file states no new results and reproduces
no logic: every line `#check`s an already-proven theorem in its home file, so the `import`s recompile those
files and the index cannot point at a dead or renamed result. A `#check`-only index creates no declarations
and so *structurally cannot overclaim* the snap's nature. Read this index (and the theorems it points at)
before writing anything about the snap; the home files are the ground truth.

Bedrock (each a live theorem below): the snap is a **derived** theorem, not an axiom (`t_snap_derived`,
AX-1 retired); it is **one-way** (`t_snap_irreversible`); and it returns to a **new** ⊥ — a successor
null. **The novelty is a commitment, not a theorem**: `t_iz_limit_is_new_null` gives only the role half
(anything playing the ⊥ role is `bot`), `c_da2_novelty` its contrapositive, and within one lattice `bot`
is unique — see the § IV glosses.

## Engineer's Take

A canonical official representation of what the snap can and cannot be. Defined in Lean and referenced
by the proof assistant during development.
-/

section SnapCannotBeIndex

/-! ### § I. What the snap IS NOT — not an axiom, not reversible, not a return to the same ⊥ -/
#check @ZeroParadox.t_snap_derived                    -- DERIVED (c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁) — AX-1 retired
#check @ZeroParadox.t_snap_irreversible               -- NOT reversible: no join from ε₀ returns to ⊥
#check @ZeroParadox.dp2_execution_distinguishability  -- the post-snap null ≠ the pre-snap null (distinct instances)
#check @ZeroParadox.da1_minimal_path                  -- the snap moves c₀ → c₁; c₀ is not recoverable

/-! ### § II. What the snap IS — the forced join transition ⊥ → ε₀ -/
#check @ZeroParadox.t_snap_join                       -- the algebraic core: ⊥ ∨ ε₀ = ε₀ (from A4/bot_join)
#check @ZeroParadox.t_snap_machine                    -- concrete: c₀ ∨ c₁ = c₁ (initial → running)

/-! ### § III. What the snap DOES — it narrows reachability, permanently -/
#check @ZeroParadox.t_snap_accessible_proper_subset   -- from ε₀ only a proper subset is reachable; ⊥ is foreclosed
#check @ZeroParadox.da2_bottom_characterization       -- the ⊥ role: (∀ x, join S x = x) ↔ S = ⊥
#check @ZeroParadox.da3_accessibleCardinality         -- reachable cardinality is position-relative

/-! ### § IV. The snap returns to a ⊥ (read as a successor null — a commitment); its 2-adic realization is a loop -/
#check @ZeroParadox.c_da2_novelty                     -- contrapositive of the role fact: a non-⊥ state cannot satisfy the join-identity. "Distinct successor instantiation" is the reading, not the statement
#check @ZeroParadox.snap_arc_z2_loop                  -- the ℤ₂ realization: start 0, depart, reapproach 0
#check @ZeroParadox.t_iz_limit_is_new_null            -- role half only: (∀ x, join terminal x = x) → terminal = bot. Novelty is NOT in this statement; do not cite it as the novelty witness

/-! ### § V. WHERE the snap is RULED OUT — and what only removes the obstruction

Reading: CARRIER. These lines BOUND the snap; none supplies it. ZP-F rules it out in every ordered
field; ZP-B removes the topological obstruction in ℚ_p without replacing it, since the 2-adic norms
accumulate at 0 and ℚ_p has no closest non-zero element either. The first step is AX-B1, a modelling
commitment — see `ZeroParadox/Valuation/Padic.lean`'s classification note. -/
#check @ZeroParadox.HasFirstStep                      -- Statement: the first step IS Mathlib's covering relation, `∃ a, bot ⋖ a`
#check @ZeroParadox.f_snap_blocked                    -- Statement: over `Field + LinearOrder + IsStrictOrderedRing`, every positive ε₀ admits a smaller positive δ
#check @ZeroParadox.f_snap_impossible                 -- Statement: hence no such field has a least positive element. No Archimedean hypothesis appears in the binders
#check @ZeroParadox.axb1_fails_in_ordered_field       -- Statement: `¬ HasFirstStep (0 : F)`. AX-B1 is what supplies the step, and it is a commitment, not a carrier property
#check @ZeroParadox.real_no_snap                      -- Statement: ℝ is NOT totally disconnected
#check @ZeroParadox.padic_snaps                       -- Statement: ℚ_p IS totally disconnected. Removes the obstruction; supplies no first step
#check @ZeroParadox.snap_dichotomy                    -- Statement: for NONTRIVIAL absolute values on ℚ, real and p-adic are exclusive and exhaustive (Ostrowski). ⚠ SCOPE: completions of ℚ only

end SnapCannotBeIndex
