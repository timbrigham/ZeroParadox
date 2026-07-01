-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC49 — the third root-cut regime: the nat/list functor (leaf + recursive position)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The bottom-diagram root cut sorts polynomial functors `P` by the inhabitance of their initial algebra
`Fix P.Obj` (least fixed point, μ) versus final coalgebra `Cofix P.Obj` (greatest fixed point, ν):

* **pure-seam** (`constPF`, the seam constant functor): `Fix ≃ Cofix` — both are the constant set.
* **pure-strict** (`idPF`, identity functor `X ↦ X`): `Fix` is empty, `Cofix` is inhabited — the
  strict μ/ν gap.

This file tests a **third regime**, the nat/list functor `natPF = ⟨Bool, fun b => cond b PUnit PEmpty⟩`
(the polynomial functor `1 + X`): the `b = false` head is a leaf (`PEmpty` children, a base case),
the `b = true` head is a successor (one `PUnit`-indexed recursive child). The pre-registered claim is
that this is *strictly between* the two pure regimes: `Fix` is **inhabited** (the leaf gives a base
case) yet `Fix ↪ Cofix` is a **non-surjective** injection — the infinite unfolding (all `b = true`)
lives only in `Cofix`.

**Race outcome: GO — the third regime is fully witnessed in-type.**

* `natFix_nonempty` — `Nonempty (Fix natPF.Obj)`, choice-free (`propext, Quot.sound` only) from the
  leaf via `Fix.mk` of the empty-child node. (Distinguishes natPF from `idPF`, whose `Fix` is empty.)
* `natCofix_nonempty` — `Nonempty (Cofix natPF.Obj)`; an explicit inhabitant `natInfinity`, the
  all-`b = true` infinite unfolding via `Cofix.corec`.
* `natCofix_infinity_dest` — `natInfinity` is its own successor (`dest natInfinity = ⟨true, fun _ => natInfinity⟩`):
  a genuine non-well-founded element that never reaches a leaf.
* `fixToCofix_not_surjective` — **the load-bearing edge, PROVEN.** The canonical comparison
  `fixToCofix = Cofix.corec Fix.dest : Fix natPF.Obj → Cofix natPF.Obj` is not surjective: `natInfinity`
  is not in its range. The invariant `EventuallyLeaf` ("reaches a leaf head under finitely many
  destructurings") holds on the entire range — `fixToCofix_eventuallyLeaf`, by `Fix.ind` (well-founded
  descent of the initial algebra) — but fails on `natInfinity` (`natInfinity_not_eventuallyLeaf`,
  its head is always the successor). So the infinite unfolding lives only in `Cofix`.
* `tc49_three_regimes` — the classification claim bundled: `Fix` inhabited ∧ `Cofix` inhabited ∧
  comparison non-surjective.

**What is Lean vs interpretation.** Lean proves: `natPF`'s initial algebra is inhabited and its
canonical map into the final coalgebra strictly omits a specific infinite element. The reading that
this is a "third root-cut regime strictly between pure-seam (`constPF`, `Fix ≃ Cofix`) and pure-strict
(`idPF`, `Fix` empty)" is the framework interpretation: `constPF`/`idPF` are defined here but their
`Fix ≃ Cofix` / `Fix` empty placements are stated as the regime description, not separately proven in
this file. The witnessed substance is the `natPF` triple above.
-/

namespace ZeroParadox.ZPH_MC1_TC49

open QPF

/-! ### Every polynomial functor is a QPF (with `abs = repr = id`). -/

/-- A polynomial functor's object map is a `QPF`, trivially: the abstraction maps are identities. -/
instance pfunctorQPF (P : PFunctor.{u, u}) : QPF P.Obj where
  P := P
  abs := id
  repr := id
  abs_repr _ := rfl
  abs_map _ _ := rfl

/-! ### The three regimes as polynomial functors. -/

/-- The seam constant functor on a one-point set: `X ↦ 1` (head `PUnit`, no children). -/
def constPF : PFunctor.{0, 0} := ⟨PUnit, fun _ => PEmpty⟩

/-- The identity functor `X ↦ X` (head `PUnit`, one child). Pure-strict regime. -/
def idPF : PFunctor.{0, 0} := ⟨PUnit, fun _ => PUnit⟩

/-- The nat/list functor `X ↦ 1 + X` (head `Bool`; `false` = leaf with no children,
    `true` = successor with one recursive child). The third regime under test. -/
def natPF : PFunctor.{0, 0} := ⟨Bool, fun b => cond b PUnit PEmpty⟩

/-! ### Regime 3, base case: `Fix natPF.Obj` is INHABITED.

This is the structural separation from `idPF` (pure-strict), whose `Fix` is empty: the `b = false`
leaf node has `PEmpty` children, so `Fix.mk` applies with no recursive arguments. -/

/-- The leaf node of `natPF` over any carrier: head `false`, empty child map. -/
def leafNode {α : Type} : natPF.Obj α := ⟨false, fun e => e.elim⟩

/-- **Regime 3 base case.** `Fix natPF.Obj` is inhabited — the leaf builds a base inhabitant
    choice-free. (Contrast `idPF`, whose `Fix` is empty: it has no leaf.) -/
theorem natFix_nonempty : Nonempty (Fix natPF.Obj) :=
  ⟨Fix.mk leafNode⟩

/-! ### Regime 3, infinite element: `Cofix natPF.Obj` has the all-`true` unfolding.

The coalgebra `fun (_ : Unit) => (⟨true, fun _ => ()⟩ : natPF.Obj Unit)` keeps choosing the successor
head, so its `Cofix.corec` never reaches a leaf. This is the non-well-founded element living only in
`Cofix`. -/

/-- The "always successor" coalgebra on the one-point carrier. -/
def succCoalg : Unit → natPF.Obj Unit := fun _ => ⟨true, fun _ => ()⟩

/-- `natInfinity` : the all-`true` infinite unfolding, an explicit `Cofix natPF.Obj` inhabitant. -/
def natInfinity : Cofix natPF.Obj := Cofix.corec succCoalg ()

/-- **Regime 3 final-coalgebra inhabitant.** `Cofix natPF.Obj` is inhabited. -/
theorem natCofix_nonempty : Nonempty (Cofix natPF.Obj) :=
  ⟨natInfinity⟩

/-- **`natInfinity` is genuinely non-well-founded:** its destructor is the successor head whose unique
    child is `natInfinity` again — it never reaches a leaf. This is the load-bearing witness that the
    element is an infinite unfolding (the kind that cannot live in `Fix`). -/
theorem natCofix_infinity_dest :
    Cofix.dest natInfinity = ⟨true, fun _ => natInfinity⟩ := by
  unfold natInfinity
  rw [Cofix.dest_corec]
  rfl

/-! ### The load-bearing edge: the canonical `Fix → Cofix` comparison is NOT surjective.

`natInfinity` is in `Cofix` but not in the range of the canonical comparison
`fixToCofix = Cofix.corec Fix.dest`. The invariant: a `Cofix` element in the range of the comparison
**eventually reaches a leaf head** (`false`) under iterated destructuring — this is forced by `Fix`
well-foundedness (`Fix.ind`). `natInfinity` never does (its head is always `true`). -/

/-- The canonical comparison `Fix → Cofix`: unfold a `Fix` element as a coalgebra. -/
def fixToCofix : Fix natPF.Obj → Cofix natPF.Obj := Cofix.corec Fix.dest

/-- "Eventually reaches a leaf head under iterated destructuring." A least-fixed-point predicate on
    `Cofix`, so it is legitimate even though `Cofix` itself is non-well-founded. Phrased via an explicit
    destructor equation `Cofix.dest x = ⟨head, c⟩` to keep the recursive child cast-free. -/
inductive EventuallyLeaf : Cofix natPF.Obj → Prop
  | leaf (x : Cofix natPF.Obj) (c : cond false PUnit PEmpty → Cofix natPF.Obj)
      (h : Cofix.dest x = ⟨false, c⟩) : EventuallyLeaf x
  | step (x : Cofix natPF.Obj) (c : cond true PUnit PEmpty → Cofix natPF.Obj)
      (h : Cofix.dest x = ⟨true, c⟩) (ih : EventuallyLeaf (c PUnit.unit)) : EventuallyLeaf x

/-- Helper: no `EventuallyLeaf` element can equal `natInfinity`. Proven by induction on the
    `EventuallyLeaf` derivation (so `x` stays general): the leaf case clashes with `natInfinity`'s
    `true` head; the step case reduces the child back to `natInfinity` and uses the IH. -/
theorem eventuallyLeaf_ne_infinity : ∀ x, EventuallyLeaf x → x ≠ natInfinity := by
  intro x h
  induction h with
  | leaf x c hx =>
      intro hxe
      subst hxe
      rw [natCofix_infinity_dest] at hx
      exact Bool.noConfusion (congrArg Sigma.fst hx)
  | step x c hx ih ihrec =>
      intro hxe
      subst hxe
      -- the unique child of natInfinity's successor head is natInfinity again
      apply ihrec
      -- from `Cofix.dest natInfinity = ⟨true, c⟩` and `= ⟨true, fun _ => natInfinity⟩`, get c = const
      rw [natCofix_infinity_dest] at hx
      have hc : c = (fun _ => natInfinity) := by
        have := (Sigma.mk.injEq _ _ _ _).mp hx.symm
        simpa using this.2
      rw [hc]

/-- `natInfinity` never reaches a leaf. -/
theorem natInfinity_not_eventuallyLeaf : ¬ EventuallyLeaf natInfinity := fun h =>
  eventuallyLeaf_ne_infinity natInfinity h rfl

/-- One destructuring step of the canonical comparison: `Cofix.dest (fixToCofix (Fix.mk y))` unfolds
    to the same head as `y` with children mapped through `fixToCofix`. -/
theorem fixToCofix_dest_mk (y : natPF.Obj (Fix natPF.Obj)) :
    Cofix.dest (fixToCofix (Fix.mk y)) = ⟨y.1, fun i => fixToCofix (y.2 i)⟩ := by
  unfold fixToCofix
  rw [Cofix.dest_corec, Fix.dest_mk]
  rfl

/-- **Range invariant.** Every element in the range of the canonical comparison eventually reaches a
    leaf. Proved by `Fix.ind`: the leaf head `false` is a base case; the successor head `true` steps
    to its unique child, which is again a comparison image, handled by the inductive hypothesis. -/
theorem fixToCofix_eventuallyLeaf : ∀ x : Fix natPF.Obj, EventuallyLeaf (fixToCofix x) := by
  apply Fix.ind
  intro y hy
  rw [QPF.liftp_iff'] at hy
  obtain ⟨u, hu, hchild⟩ := hy
  -- abs = id, so u = y; extract the per-child predicate on y itself
  have huy : u = y := hu
  subst huy
  -- now `hchild : ∀ i, EventuallyLeaf (fixToCofix (u.2 i))`
  obtain ⟨a, f⟩ := u
  cases a with
  | false =>
      -- leaf head: the comparison image destructs directly to a `false` node
      exact EventuallyLeaf.leaf _ (fun i => fixToCofix (f i)) (fixToCofix_dest_mk ⟨false, f⟩)
  | true =>
      -- successor head: step to the unique `PUnit` child, which is a comparison image
      exact EventuallyLeaf.step _ (fun i => fixToCofix (f i)) (fixToCofix_dest_mk ⟨true, f⟩)
        (hchild PUnit.unit)

/-- **TC49 load-bearing edge — the canonical comparison is NOT surjective.** `natInfinity` is a
    `Cofix natPF.Obj` element that is not in the range of `fixToCofix : Fix → Cofix`: every comparison
    image eventually reaches a leaf (`fixToCofix_eventuallyLeaf`), but `natInfinity` never does
    (`natInfinity_not_eventuallyLeaf`). This witnesses the third root-cut regime: `Fix` inhabited
    (`natFix_nonempty`) yet `Fix ↪ Cofix` strictly omits the infinite unfolding. -/
theorem fixToCofix_not_surjective : ¬ Function.Surjective fixToCofix := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj natInfinity
  exact natInfinity_not_eventuallyLeaf (hx ▸ fixToCofix_eventuallyLeaf x)

/-- **Three-regime placement, head-level summary.** The three functors are separated by the head of
    their fixpoint's bottom unfolding: `constPF` and `idPF` are the pure regimes; `natPF` is the third,
    with both `Fix` and `Cofix` inhabited and the comparison non-surjective. (The substance is the
    three theorems above; this records the classification claim in one place.) -/
theorem tc49_three_regimes :
    Nonempty (Fix natPF.Obj) ∧ Nonempty (Cofix natPF.Obj) ∧ ¬ Function.Surjective fixToCofix :=
  ⟨natFix_nonempty, natCofix_nonempty, fixToCofix_not_surjective⟩

end ZeroParadox.ZPH_MC1_TC49

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC49

#print axioms natFix_nonempty
#print axioms natCofix_nonempty
#print axioms natCofix_infinity_dest
#print axioms natInfinity_not_eventuallyLeaf
#print axioms fixToCofix_eventuallyLeaf
#print axioms fixToCofix_not_surjective
#print axioms tc49_three_regimes

end PurityCheck
