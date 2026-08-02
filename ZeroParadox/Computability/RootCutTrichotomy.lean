-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Data.W.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The root cut is a TRICHOTOMY (leaf × recursive position)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Earlier tree tests (`ZeroParadox/Category/RootCutDegeneracy.lean` and `ZeroParadox/Category/RootCutBinary.lean`) separated polynomial-functor bottoms into a **dichotomy** by whether
the functor has a recursive position: a leaf-free functor with no recursive position is a *seam*
(`Fix ≃ Cofix`), one with a recursive position but no leaf is *strict* (`Fix` empty, `Cofix`
inhabited). **Neither of those tests varied the leaf independently** — the head set was
all-or-nothing on recursive positions: `constPF A = ⟨A, fun _ => PEmpty⟩` is **all-leaf** with no
recursive position, while `idPF_Coalgebra` and `binPF` are leaf-free with one and two. *(This
sentence read "Both of those tests used **leaf-free** functors", which is false of `constPF`;
corrected 2026-08-02. The load-bearing half — all-or-nothing on recursive positions — was accurate
and is what the argument below uses.)*

This file introduces the **mixed** functor — one node type carrying a leaf (no recursive position)
and another carrying a recursive position — and shows it realizes a **third** root-cut regime, so the
cut is governed by a 2×2 product (presence of leaf) × (presence of recursive position), not by
recursive-position presence alone.

The three functors under test, all polynomial (`PFunctor`):
- `seamPF = ⟨PUnit, fun _ => PEmpty⟩` — one node, a leaf, **no** recursive position.
- `idPF_RootCutTrichotomy = ⟨PUnit, fun _ => PUnit⟩` — one node, one recursive position, **no** leaf.
- `natPF_RootCutTrichotomy = ⟨Bool, fun b => cond b PUnit PEmpty⟩` — `false` is a leaf, `true` carries one recursive
  position. This is the natural-number / list shape.

**The in-statement findings (the load-bearing content lives in the theorem statements):**

- `seam_fix_finite` — `W seamPF` (the least fixed point, `Fix`) is **finite**: the seam regime.
- `strict_fix_isEmpty` — `W idPF_RootCutTrichotomy` is **empty**: no base case, so no finite tree exists — the strict
  regime. (`W` is `Fix`; emptiness is the strict fork's `Fix = ∅`.)
- `mixed_fix_nonempty` — `W natPF_RootCutTrichotomy` is **nonempty**: the leaf (`false`) supplies a genuine base case.
- `mixed_fix_infinite` — `W natPF_RootCutTrichotomy` is **infinite**: the recursive position (`true`) lets finite trees
  grow without bound.
- `strict_cofix_nonempty`, `mixed_cofix_nonempty` — the greatest fixed points `M idPF_RootCutTrichotomy`, `M natPF_RootCutTrichotomy`
  (`Cofix`) are nonempty. With `strict_fix_isEmpty` the strict fork is fully exhibited in-statement:
  `Fix = ∅`, `Cofix ≠ ∅`. The mixed regime has both a nonempty `Fix` (`mixed_fix_nonempty`) and a
  `Cofix`, so it is neither the seam (finite `Fix`) nor the strict fork (empty `Fix`).

The pair `strict_fix_isEmpty` (no leaf ⇒ `Fix` empty) versus `mixed_fix_nonempty` (add a leaf ⇒
`Fix` nonempty), at fixed recursive-position presence, is the **leaf doing independent work** —
exactly what `ZeroParadox/Category/RootCutDegeneracy.lean` and
`ZeroParadox/Category/RootCutBinary.lean` could not see. The pair `seam_fix_finite` (no position ⇒ `Fix` finite) versus
`mixed_fix_infinite` (add a position ⇒ `Fix` infinite), at fixed leaf presence, is the **recursive
position doing independent work**. Together they witness the three regimes as a genuine trichotomy.

**What is proved vs. interpretation.** Proved in Lean: the four W-type (`Fix`) cardinality facts
above, and `mixed_trichotomy`, the bundled three-regime statement. The "non-surjective injection
`Fix ↪ Cofix`" framing of the mixed case is *interpretation* of these facts: `Fix` nonempty-but-
distinct-from a strictly larger `Cofix` is read off `mixed_fix_nonempty` together with the standard
`W ↪ M` (which this file does not build); the machine-checked separation is carried by the
cardinality theorems, which is where the new leaf×position content actually is.
-/

namespace ZeroParadox

open PFunctor

/-! ## The three polynomial functors -/

/-- Seam: one node, a leaf, no recursive position. -/
def seamPF : PFunctor.{0, 0} := ⟨PUnit, fun _ => PEmpty⟩

/-- Strict: one node, one recursive position, no leaf (the identity polynomial functor). -/
def idPF_RootCutTrichotomy : PFunctor.{0, 0} := ⟨PUnit, fun _ => PUnit⟩

/-- Mixed (the nat/list shape): `false` is a leaf, `true` carries one recursive position. -/
def natPF_RootCutTrichotomy : PFunctor.{0, 0} := ⟨Bool, fun b => cond b PUnit PEmpty⟩

/-! ## Seam regime — `Fix` finite -/

/-- `W seamPF` (= `Fix`) is finite: the seam node has no recursive position, so the only tree is the
    single leaf. -/
theorem seam_fix_finite : Finite (W seamPF) := by
  -- `W seamPF = WType seamPF.B`; every tree is `⟨(), PEmpty.elim⟩`, so it is a subsingleton.
  have : Subsingleton (W seamPF) := by
    constructor
    intro x y
    induction x with
    | mk a f ih =>
      induction y with
      | mk b g _ =>
        cases a; cases b
        congr 1
        funext (p : PEmpty)
        exact p.elim
  exact Finite.of_subsingleton

/-! ## Strict regime — `Fix` empty -/

/-- `W idPF_RootCutTrichotomy` (= `Fix`) is empty: `idPF_RootCutTrichotomy` has no leaf (every node has exactly one recursive position),
    so no finite tree exists. The strict fork's `Fix = ∅`. -/
theorem strict_fix_isEmpty : IsEmpty (W idPF_RootCutTrichotomy) := by
  constructor
  intro w
  -- well-founded recursion on the W-tree: every node forces a strictly smaller child, no base case
  induction w with
  | mk a f ih => exact ih PUnit.unit

/-! ## Mixed regime — `Fix` nonempty and infinite -/

/-- `W natPF_RootCutTrichotomy` (= `Fix`) is nonempty: the leaf node `false` (whose child type is `PEmpty`) is a base
    case, giving the finite tree `⟨false, PEmpty.elim⟩`. -/
theorem mixed_fix_nonempty : Nonempty (W natPF_RootCutTrichotomy) :=
  ⟨WType.mk false (fun (p : cond false PUnit PEmpty) => (p : PEmpty).elim)⟩

/-- `W natPF_RootCutTrichotomy` (= `Fix`) is infinite: the recursive node `true` (child type `PUnit`, nonempty) and the
    leaf node `false` (child type `PEmpty`) together build trees of unbounded depth. -/
theorem mixed_fix_infinite : Infinite (W natPF_RootCutTrichotomy) := by
  -- `natPF_RootCutTrichotomy.B true = PUnit` is nonempty, `natPF_RootCutTrichotomy.B false = PEmpty` is empty.
  haveI : Nonempty (natPF_RootCutTrichotomy.B true) := ⟨PUnit.unit⟩
  haveI : IsEmpty (natPF_RootCutTrichotomy.B false) := inferInstanceAs (IsEmpty PEmpty)
  exact WType.infinite_of_nonempty_of_isEmpty (β := natPF_RootCutTrichotomy.B) true false

/-! ## Cofix witnesses (the `M`-type / greatest fixed point) -/

/-- The strict fork's `Cofix` is inhabited: `M idPF_RootCutTrichotomy` is nonempty (the infinite unary unfolding).
    With `strict_fix_isEmpty` this is the full strict fork: `Fix = ∅`, `Cofix ≠ ∅`. -/
theorem strict_cofix_nonempty : Nonempty (M idPF_RootCutTrichotomy) := by
  haveI : Inhabited idPF_RootCutTrichotomy.A := ⟨PUnit.unit⟩
  exact ⟨default⟩

/-- The mixed `Cofix` is inhabited: `M natPF_RootCutTrichotomy` is nonempty. (Its inhabitants include both the finite
    images of `Fix` and strictly larger infinite unfoldings; `Fix` is nonempty by
    `mixed_fix_nonempty`, so the mixed regime has both a nonempty `Fix` and a `Cofix` — neither the
    seam's finite-`Fix` nor the strict fork's empty-`Fix`.) -/
theorem mixed_cofix_nonempty : Nonempty (M natPF_RootCutTrichotomy) := by
  haveI : Inhabited natPF_RootCutTrichotomy.A := ⟨false⟩
  exact ⟨default⟩

/-! ## The trichotomy, bundled -/

/-- The root cut is a **trichotomy** governed by (leaf) × (recursive position):
    - seam (leaf, no position): `Fix` finite;
    - strict (position, no leaf): `Fix` empty;
    - mixed (leaf and position): `Fix` nonempty and infinite.
    The three regimes are pairwise distinguished in-statement by the cardinality of `Fix`. -/
theorem mixed_trichotomy :
    Finite (W seamPF) ∧
    (IsEmpty (W idPF_RootCutTrichotomy) ∧ Nonempty (M idPF_RootCutTrichotomy)) ∧
    (Nonempty (W natPF_RootCutTrichotomy) ∧ Infinite (W natPF_RootCutTrichotomy) ∧ Nonempty (M natPF_RootCutTrichotomy)) :=
  ⟨seam_fix_finite,
   ⟨strict_fix_isEmpty, strict_cofix_nonempty⟩,
   ⟨mixed_fix_nonempty, mixed_fix_infinite, mixed_cofix_nonempty⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `WType` infinitude lemma (`not_injective_infinite_finite`
and friends) — a library dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox

#print axioms seam_fix_finite
#print axioms strict_fix_isEmpty
#print axioms mixed_fix_nonempty
#print axioms mixed_fix_infinite
#print axioms strict_cofix_nonempty
#print axioms mixed_cofix_nonempty
#print axioms mixed_trichotomy

end PurityCheck
