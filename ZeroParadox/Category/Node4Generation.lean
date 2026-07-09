-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H node #4 GENERATION — the floor `Fin 0` generates the ceiling `ℕ` by iteration (an Adámek instance)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The GEN slot of the ⊥-matrix is **generation by iteration**: the floor ⊥ generates the structure built
above it as the least fixed point `lfp F = ⊔ₙ Fⁿ(⊥)` — the categorical Adámek construction (initial
algebra = colimit of the initial chain `0 → F0 → F²0 → …`; J. Adámek, *Free algebras and automata
realizations in the language of categories*, Comment. Math. Univ. Carolin. 15 (1974), 589–602). Mathlib
carries the *order-theoretic* engine
(`fixedPoints.lfp_eq_sSup_iterate`) and ZP carries the *ordinal* instance (`epsilonZero_eq_nfp`:
ε₀ = nfp(ω^·)0), but the *categorical* Adámek colimit was recorded open (not in Mathlib). This file builds
the canonical instance for node #4's floor.

**The construction.** Take the endofunctor `F X = X + 1` (whose initial algebra is `ℕ`). Its initial
chain is `Fⁿ(∅) = Fin n`, with connecting maps the inclusions `Fin n ↪ Fin (n+1)` (`Fin.castSucc`). The
**base of the chain is `Fin 0 = ∅` — node #4's Kleisli floor** (`fC_obj 0 = Fin 0`). Its colimit is `ℕ`,
with cocone legs `Fin.val : Fin n → ℕ`.

**`node4_generates_nat` — the GEN witness, stated as the colimit universal property** (in `Type`, to avoid
the bundled-hom category boilerplate; the universal property *is* the statement "ℕ is the colimit of the
chain"): for any target `P` and any compatible family `f n : Fin n → P` along the chain
(`f (n+1) i.castSucc = f n i`), there is a **unique** `g : ℕ → P` factoring every leg through `Fin.val`
(`g i.val = f n i`). So the floor `Fin 0` generates `ℕ` as the colimit of the iteration chain — the
categorical form of `lfp F = ⊔ₙ Fⁿ(⊥)`, rooted at node #4's bottom. Node #4 is thus not merely the initial
*object* (the μ-base, `node4_isColimit`) but the *seed of generation*.

**Honest scope.** One concrete Adámek instance (`X ↦ X+1`, initial algebra `ℕ`), at the `Type` level where
`Fin 0` is node #4's underlying object. NOT the general Adámek theorem (any ω-cocontinuous endofunctor),
which remains unbuilt. Proved: `ℕ` (with legs `Fin.val`) is the colimit of the successor chain rooted at
the floor `Fin 0`.
-/

namespace ZeroParadox

/-- Compatibility across an arbitrary gap `m ≤ n`: a family compatible along each single step is
    compatible along the inclusion `Fin.castLE` of any gap. (The reindexing lemma the colimit needs.) -/
private theorem succChain_castLE_compat {P : Type*} (f : (n : ℕ) → Fin n → P)
    (compat : ∀ (n : ℕ) (i : Fin n), f (n + 1) i.castSucc = f n i)
    (m : ℕ) (i : Fin m) : ∀ (n : ℕ) (h : m ≤ n), f n (Fin.castLE h i) = f m i := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      have hstep : Fin.castLE (Nat.le_succ_of_le hmn) i = (Fin.castLE hmn i).castSucc := by
        ext; simp
      rw [hstep, compat, ih]

/-- **GEN witness for node #4 (Adámek instance).** `ℕ` is the colimit of the successor chain
    `Fin 0 → Fin 1 → Fin 2 → …` rooted at the floor `Fin 0`: every family `f` compatible along the chain
    factors **uniquely** through `ℕ` via the value maps `Fin.val`. This is the universal property that
    *defines* "ℕ is the colimit", i.e. the floor `Fin 0` generates the ceiling `ℕ` by iteration —
    the categorical `lfp F = ⊔ₙ Fⁿ(⊥)` for `F X = X + 1`. -/
theorem node4_generates_nat {P : Type*} (f : (n : ℕ) → Fin n → P)
    (compat : ∀ (n : ℕ) (i : Fin n), f (n + 1) i.castSucc = f n i) :
    ∃! g : ℕ → P, ∀ (n : ℕ) (i : Fin n), g i.val = f n i := by
  refine ⟨fun k => f (k + 1) (Fin.last k), ?_, ?_⟩
  · -- factoring: g i.val = f n i, via the gap-compatibility lemma
    intro n i
    have hi : Fin.castLE (Nat.succ_le_of_lt i.isLt) (Fin.last i.val) = i := by ext; simp
    calc f (i.val + 1) (Fin.last i.val)
        = f n (Fin.castLE (Nat.succ_le_of_lt i.isLt) (Fin.last i.val)) :=
          (succChain_castLE_compat f compat (i.val + 1) (Fin.last i.val) n
            (Nat.succ_le_of_lt i.isLt)).symm
      _ = f n i := by rw [hi]
  · -- uniqueness
    intro g' hg'
    funext k
    have := hg' (k + 1) (Fin.last k)
    simpa using this

/-- The base of the generating chain is exactly node #4's floor `Fin 0` (the empty type, `= fC_obj 0`). -/
theorem succChain_base_is_empty : IsEmpty (Fin 0) := Fin.isEmpty

end ZeroParadox

/-! ## Axiom Purity Check

`node4_generates_nat` uses only `propext` and `Quot.sound` (via `funext` on the unique factoring map and
`Fin`/`Nat` quotient reasoning) — NO `Classical.choice`. Generation from the floor is choice-free.
`succChain_base_is_empty` depends on no axioms. -/

section PurityCheck
open ZeroParadox

#print axioms node4_generates_nat
#print axioms succChain_base_is_empty

end PurityCheck
