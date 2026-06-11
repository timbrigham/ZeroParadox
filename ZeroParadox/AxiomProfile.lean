import ZeroParadox.Basic

/-!
# Axiom Profile — the choice-free core of the Zero Paradox

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
#print axioms ZeroParadox.ZPE.t_snap_machine
#print axioms ZeroParadox.ZPE.t_snap_derived
#print axioms ZeroParadox.ZPE.t_snap_join
#print axioms ZeroParadox.ZPE.t_snap_irreversible
#print axioms ZeroParadox.ZPE.da1_minimal_path
#print axioms ZeroParadox.ZPE.dp2_execution_distinguishability

-- The lattice algebra (ZP-A):
#print axioms ZeroParadox.ZPA.ZPSemilattice.bot_le
#print axioms ZeroParadox.ZPA.ZPSemilattice.cc1

-- The Quine-atom self-reference keystone (ZP-J):
#print axioms ZeroParadox.ZPJ.bot_is_quine_atom
#print axioms ZeroParadox.ZPJ.cc1_derived
#print axioms ZeroParadox.ZPJ.t_exec
#print axioms ZeroParadox.ZPJ.quine_atom_unique

end ChoiceFreeCore

/-! ## II. Choice-free structural results (`[propext, Quot.sound]` or none)

No `Classical.choice`; at most propositional extensionality and quotient soundness. -/
section ChoiceFreeStructural

#print axioms ZeroParadox.AczelConn.J_self_is_largest        -- does not depend on any axioms
#print axioms ZeroParadox.ZPI.t_iz_limit_is_new_null         -- does not depend on any axioms
#print axioms ZeroParadox.ZPH_PowerSet.ps_structural_floor   -- [propext, Quot.sound]
#print axioms ZeroParadox.WheelFrac.instWheel                -- [propext, Quot.sound]
#print axioms ZeroParadox.WheelFrac.inf_ne_bot               -- [propext, Quot.sound]

end ChoiceFreeStructural

/-! ## III. Where `Classical.choice` enters — the analytic realizations (honest contrast)

These realize the snap floor inside standard analytic structures and inherit `Classical.choice` from
Mathlib's classically-built topology / inner-product / category / probability libraries. The
dependence is in the realization, not in the core claim of Section I. -/
section WhereChoiceEnters

#print axioms ZeroParadox.ZPB.c3_irreversible        -- [propext, Classical.choice, Quot.sound]  (p-adic topology)
#print axioms ZeroParadox.ZPD.t4_snap_orthogonal     -- [propext, Classical.choice, Quot.sound]  (Hilbert space)
#print axioms ZeroParadox.ZPHTop.fB_functor          -- [propext, Classical.choice, Quot.sound]  (TopCat)
#print axioms ZeroParadox.ZPHHilb.fD_functor         -- [propext, Classical.choice, Quot.sound]  (ModuleCat ℂ)
#print axioms ZeroParadox.ZPHInfo.fC_functor         -- [propext, Classical.choice, Quot.sound]  (KleisliCat PMF)

end WhereChoiceEnters
