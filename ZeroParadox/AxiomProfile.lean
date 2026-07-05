import ZeroParadox.Basic

/-!
# Axiom Profile — the choice-free core of the Zero Paradox

## Engineer's Take

Here my system engineering background shows through. This is a unit test on the core axioms for the
Zero Paradox project. While classical choice may exist elsewhere in the project, and may even be
required in places... the heart of what we're trying to prove is choice free.

---

This file is a **checkable artifact**. Build it and read the `#print axioms` output: the Lean kernel
reports the complete axiom dependency of each result, so the claims below are verifiable, not asserted.

**The core results are free of `Classical.choice`. The central theorem — the Binary Snap (T-SNAP) —
depends on no axioms at all.** The lattice algebra (ZP-A) and the Quine-atom self-reference keystone
(ZP-J) are likewise choice-free.

`Classical.choice` appears in the framework only in the layers that *realize* these results inside
standard analytic structures (p-adic topology, Hilbert space, ordinals, computability, category
theory), where it is **inherited from Mathlib's classically-built libraries** — shown in Section III
for honest contrast. Whether that inherited dependence is removable or genuinely necessary is a
separate open question (see the README Question Register and the `choice-probe` experiment, which
found it mostly incidental in the one layer classified so far). It is not load-bearing for any ZP
*claim*: the things the framework asserts are proved above without choice.

Distinction worth keeping: "does not depend on any axioms" (T-SNAP, the lattice, the Quine atom) is
stronger than "choice-free" — those use not even propositional extensionality. The `[propext,
Quot.sound]` results are choice-free but use propext and quotient soundness (both Lean 4 standard).

Run:  `lake build ZeroParadox.AxiomProfile`
-/

/-! ## I. The choice-free core — T-SNAP, the lattice, the Quine atom

Each of these reports `'<name>' does not depend on any axioms`. -/
section ChoiceFreeCore

-- The Binary Snap (T-SNAP) and its derivation (ZP-E):
#print axioms ZeroParadox.t_snap_machine
#print axioms ZeroParadox.t_snap_derived
#print axioms ZeroParadox.t_snap_join
#print axioms ZeroParadox.t_snap_irreversible
#print axioms ZeroParadox.da1_minimal_path
#print axioms ZeroParadox.dp2_execution_distinguishability

-- The lattice algebra (ZP-A):
#print axioms ZeroParadox.ZPSemilattice.bot_le
#print axioms ZeroParadox.ZPSemilattice.cc1

-- The Quine-atom self-reference keystone (ZP-J):
#print axioms ZeroParadox.bot_is_quine_atom
#print axioms ZeroParadox.cc1_derived
#print axioms ZeroParadox.t_exec
#print axioms ZeroParadox.quine_atom_unique

end ChoiceFreeCore

/-! ## II. Choice-free structural results (`[propext, Quot.sound]` or none)

No `Classical.choice`; at most propositional extensionality and quotient soundness. -/
section ChoiceFreeStructural

#print axioms ZeroParadox.J_self_is_largest        -- does not depend on any axioms
#print axioms ZeroParadox.ZPI.t_iz_limit_is_new_null         -- does not depend on any axioms
#print axioms ZeroParadox.ps_structural_floor   -- [propext, Quot.sound]
#print axioms ZeroParadox.instWheel                -- [propext, Quot.sound]
#print axioms ZeroParadox.inf_ne_bot               -- [propext, Quot.sound]
#print axioms ZeroParadox.quine_self_members_eq_bot  -- [propext, Quot.sound]  (Quine-atom identity = {⊥})

end ChoiceFreeStructural

/-! ## III. Where `Classical.choice` enters — the analytic realizations (honest contrast)

These realize the snap floor inside standard analytic structures and inherit `Classical.choice` from
Mathlib's classically-built topology / inner-product / category / probability libraries. The
dependence is in the realization, not in the core claim of Section I. -/
section WhereChoiceEnters

#print axioms ZeroParadox.c3_irreversible        -- [propext, Classical.choice, Quot.sound]  (p-adic topology)
#print axioms ZeroParadox.t4_snap_orthogonal     -- [propext, Classical.choice, Quot.sound]  (Hilbert space)
#print axioms ZeroParadox.ZPH_TopFunctor.fB_functor          -- [propext, Classical.choice, Quot.sound]  (TopCat)
#print axioms ZeroParadox.fD_functor         -- [propext, Classical.choice, Quot.sound]  (ModuleCat ℂ)
#print axioms ZeroParadox.fC_functor         -- [propext, Classical.choice, Quot.sound]  (KleisliCat PMF)
#print axioms ZeroParadox.snap_dichotomy   -- [propext, Classical.choice, Quot.sound]  (snap-occurrence dichotomy, ℝ/ℚ_p)
#print axioms ZeroParadox.quine_dichotomy -- [propext, Classical.choice, Quot.sound]  (Quine-atom structural μ/ν fork)

end WhereChoiceEnters
