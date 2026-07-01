import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Notation

/-!
# ZP-N choice probe (scratch)

Bounded experiment for Fork 2 of the axiomatic-choice-collapse conjecture
(`.claude-local/notes/axiomatic_choice_collapse_at_bottom_2026-06-15.md`):
is ZP-L's `Classical.choice` *forced* at ε₀, or merely *inherited* from Mathlib's classical ordinal API?

Method: print the axiom footprint of the Mathlib theorems ZP-L's ε₀-snap result rests on. ε₀ is
characterised as the next-fixed-point of ordinal exponentiation (`epsilon_zero_eq_nfp`); that IS the
snap threshold. If these carry `Classical.choice` in Mathlib itself, ZP-L's choice is inherited
(not ZP-forced) — but possibly unavoidable without rebuilding ordinal theory.

NOT wired into Basic.lean — scratch probe only.
-/

open Ordinal

section ChoiceProbe
-- ε₀ semantics (classical Ordinal): expect Classical.choice
#print axioms epsilon_zero_eq_nfp
#print axioms lt_epsilon_zero
#print axioms iterate_omega0_opow_lt_epsilon_zero
-- ONote constructive notation: is the SYNTAX choice-free, and where does the boundary fall?
#print axioms ONote.repr_zero          -- definitional (rfl) — syntax/semantics seam
#print axioms ONote.lt_def             -- order via repr → classical Ordinal?
#print axioms ONote.NFBelow.repr_lt    -- a real semantic fact (repr o < ω^b)
-- The constructive seed: is ONote's SYNTACTIC comparison choice-free?
#print axioms ONote.cmp                -- purely structural recursion — no repr
#print axioms ONote.eq_of_cmp_eq       -- structural proof — no repr
#print axioms ONote.cmp_compares       -- the semantic bridge (cmp ↔ ordinal order) — expect choice
end ChoiceProbe
