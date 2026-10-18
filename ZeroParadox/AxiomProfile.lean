import ZeroParadox.Order.Lattice
import ZeroParadox.Valuation.Padic
import ZeroParadox.Information.Surprisal
import ZeroParadox.State.StateSpace
import ZeroParadox.Order.Snap
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Category.Category
import ZeroParadox.Multihomed.CategoricalBridge
import ZeroParadox.Order.PowerSet
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Multihomed.MC1Bridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Settheory.AczelConn
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Valuation.Scale
import ZeroParadox.Valuation.ScaleBridge
import ZeroParadox.Settheory.Model
import ZeroParadox.Computability.Kleene
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Settheory.OntBridge
import ZeroParadox.Settheory.APG
import ZeroParadox.Algebra.Wheel
import ZeroParadox.Algebra.WheelFrac
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Valuation.Ostrowski
import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Category.Lawvere
import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Multihomed.BoundaryBridge
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Settheory.QuineDichotomy
import ZeroParadox.Category.LawvereTaboo
import ZeroParadox.Ordinal.OrdinalChoiceEssential
import ZeroParadox.Die


/-!
# Axiom Profile — the choice-free core of the Zero Paradox

## Engineer's Take

Here my system engineering background shows through. This is a unit test on the core axioms for the
Zero Paradox project. While classical choice may exist elsewhere in the project, and may even be
required in places... the heart of what we're trying to prove is choice free.

---

A **checkable artifact** (`lake build ZeroParadox.AxiomProfile`): the `#print axioms` output reports
each result's complete axiom dependency. **The core is choice-free; T-SNAP depends on no axioms at
all.** Choice appears mostly in the realization layers, inherited from Mathlib, and also in the die's
meta objects (`ZeroParadox/Die.lean`); where it is essential, and on what premise:
`ZeroParadox/Category/ChoiceCannotBe.lean` § IV, whose cases § 0 prints. -/

/-! ## 0. Choice-free reductions to taboos — essential on the premise in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV

⚠ PROVENANCE and NECESSITY are independent axes. `fixedPointFree_of_nontrivial` and the die's
`classical`s spend the framework's OWN `classical`; well-order comparability spends MATHLIB's, in
`InitialSeg.total`. The reductions below are choice-free, which is what makes them reductions rather
than measurements. Full argument: `ZeroParadox/AxiomProfile.md`. -/
section FrameworkOwnChoice

-- PROVENANCE: bare `classical`s written in framework source (`ZeroParadox/Category/Lawvere.lean`,
-- `ZeroParadox/Die.lean`), not inherited.
#print axioms ZeroParadox.fixedPointFree_of_nontrivial   -- [propext, Classical.choice, Quot.sound]
#print axioms ZeroParadox.botCovered_botIntervalTwo_classical -- [propext, Classical.choice, Quot.sound]
#print axioms ZeroParadox.Motion.registeredDecidable_of_classical -- [propext, Classical.choice, Quot.sound]
#print axioms ZeroParadox.Motion.selectedTotal_of_classical -- [propext, Classical.choice, Quot.sound]
-- NECESSITY: one reduction to a taboo per principle, each CHOICE-FREE, about the declarations above,
-- in the same order.
#print axioms ZeroParadox.wem_of_fixedPointFree          -- [propext, Quot.sound]
#print axioms ZeroParadox.wem_of_botCovered_botIntervalTwo -- [propext]
#print axioms ZeroParadox.Motion.em_of_registeredDecidable -- does not depend on any axioms
#print axioms ZeroParadox.Motion.em_of_selectedData      -- [propext, Quot.sound]
-- NECESSITY for well-order comparability, whose choice is MATHLIB's, so an INHERITED dependence can
-- be essential too, on § IV's premise.
#print axioms ZeroParadox.em_of_wellOrder_comparable     -- [propext, Quot.sound]
-- The consumer and the supplier of a fixed-point-free map; `ZeroParadox/AxiomProfile.md` says why the
-- consumer's footprint is no evidence the supplier's choice is avoidable.
#print axioms ZeroParadox.no_witness_of_fixedPointFree   -- does not depend on any axioms
#print axioms ZeroParadox.no_witness_of_nontrivial       -- [propext, Classical.choice, Quot.sound]

end FrameworkOwnChoice

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
#print axioms ZeroParadox.t_iz_limit_is_new_null         -- does not depend on any axioms
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
#print axioms ZeroParadox.fB_functor          -- [propext, Classical.choice, Quot.sound]  (TopCat)
#print axioms ZeroParadox.fD_functor         -- [propext, Classical.choice, Quot.sound]  (ModuleCat ℂ)
#print axioms ZeroParadox.fC_functor         -- [propext, Classical.choice, Quot.sound]  (KleisliCat PMF)
#print axioms ZeroParadox.snap_dichotomy   -- [propext, Classical.choice, Quot.sound]  (snap-occurrence dichotomy, ℝ/ℚ_p)
#print axioms ZeroParadox.quine_dichotomy -- [propext, Classical.choice, Quot.sound]  (Quine-atom structural μ/ν fork)

end WhereChoiceEnters
