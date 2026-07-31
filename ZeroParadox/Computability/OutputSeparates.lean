-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): two Lean instances of Rutten's final-system
-- formula for polynomial functors - the HEAD type decides whether the final coalgebra is a single point, and
-- the arity does not. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Computability.GroundZero
import ZeroParadox.Category.RootCutBinary
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The head decides, the arity does not: two instances of Rutten's final-system formula

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer.

## Engineer's Take

I know I am obsessed with this, and it still feels to me like we can get a self starting system out
of self reference.

The difference is on the computation side. It is not a loop. It is a recursive algorithm.

When I looked at the extended naturals with a point at infinity and the predecessor map, that read to
me like multiple levels of nested loops, and nested loops are something I would personally refactor
into a recursive algorithm.

I defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

**This file claims NO new mathematics.** It records two Lean-checked instances of a published formula,
and cross-links a third the corpus already had.

**The governing result — Rutten, *Universal coalgebra: a theory of systems*, TCS 249 (2000),
Example 10.2(5), printed p. 44** (`.claude-local/papers/rutten_universal_coalgebra_2000.pdf`): for
`F(S) = A × S^B` the final system is `A^{B*}`. A polynomial functor `⟨A, fun _ => B⟩` is exactly that
`F`, so its final coalgebra has `|A|^{|B*|}` elements — **a single point iff `|A| = 1`, for every `B`
whatsoever.** The head type decides; the arity `B` is irrelevant to whether the pole is a point.

The two instances proved here:

* `binCofix_subsingleton` — `binPF = ⟨Unit, fun _ => Bool⟩` (`A = 1`, `B = 2`): `1^{2*}` is one
  element, so `Cofix binPF.Obj` is a **subsingleton**. Two recursive positions buy nothing.
  `Category/RootCutBinary.lean`'s `arity_collapse` already showed arity does not move the *seam*
  question; this shows it does not move the *cardinality* question either.
* `output_separates` — `streamPF = ⟨Bool, fun _ => PUnit⟩` (`A = 2`, `B = 1`): `2^{1*}` is the
  `Bool`-streams, and two of them are provably distinct.

**The corpus already had the `B = 0` instance and it was never connected:**
`Category/RootCutDegeneracy.lean`'s `cofixEquiv : Cofix (constPF A).Obj ≃ A`, since `B* ` is then a
single point and `A^1 = A`. Three instances of one formula, in three files.

**⚠ CORRECTED 2026-07-30 (adversary + prior-art gates, bedrock). Read before citing this file against
`notEL_unique`.** An earlier revision was titled *"the infinite pole is a POINT unless the functor
emits"* and concluded *"the discriminator is what a step emits."* **That is false**, and its own foil
refutes it: `natPF_NatListRegime = ⟨Bool, fun b => cond b PUnit PEmpty⟩` has head type `Bool` — the
**same head type as `streamPF`** — yet `GroundZero.notEL_unique` proves its non-terminating part is a
single point. The stated discriminator was identical on both sides of the comparison.

The real error was **comparing across families**: `natPF`'s child type *depends on its head*, so it is
**not** of the form `⟨A, fun _ => B⟩` and Rutten 10.2(5) does not apply to it at all. Nothing here
bears on `natPF`, and this file must not be cited as explaining `notEL_unique`.

`Reading:` CARRIER — the framework reads this as the computational-face counterpart of
`Valuation/BranchingRequirement.lean`, which proves branching is what makes the 2-adic boundary a
continuum "rather than a single chain's single end". On the 2-adic tree a branch choice **is** a
digit, so branching and head-labelling coincide there and come apart here. **Conjectural**: different
carriers, no map between them is claimed, and no framework bottom is identified with any behaviour in
this file (⊥ does not appear in it).

`Reading:` a criterion covering all three functors above **and** `natPF` would be *the number of head
values with inhabited child type* (`natPF`: one; `binPF`: one; `streamPF`: two). **Conjectural — not
proved here, and not Rutten's**, whose formula is stated for constant arity only.

**Fences.** `output_separates` proves exactly **two** distinct behaviours, not the continuum; the
cardinality `2^ω` is Rutten's formula, not proved here. **Uncountability is NOT Adámek–Milius–Moss's**
— their Example 7.7 (p. 31, arXiv:1910.09401v2) gives the terminal coalgebra `A^∞ ∪ A*` and the
initial algebra `A*` and states no cardinality; cite Rutten 10.2(5) for that. The general formula is
cited, not formalized: what is machine-checked here is two of its instances.

## Structure
- § I   `A = 1`: `Cofix binPF.Obj` is a subsingleton (arity is irrelevant)
- § II  `A = 2`: `streamPF`, its constant behaviours, and their distinctness
- § III The contrast, bundled
-/

namespace ZeroParadox

open QPF

/-! ## § I — `A = 1`: the head is a singleton, so the final coalgebra is -/

/-- **Two recursive positions, one behaviour.** `binPF`'s head type is `Unit`, so every node of the
    tree looks alike and there is nothing to tell two infinite trees apart. Proved by bisimulation on
    the total relation: `liftr_iff` demands a *shared head*, and `Unit` supplies it by structure eta,
    after which the children are related for free. The technique is gated on the head type — the same
    proof fails for `streamPF` (§ II), where the conclusion is false.

    This is Rutten 10.2(5) at `A = 1, B = 2`: `1^{2*}` is one element. Compare
    `Category/RootCutDegeneracy.lean`'s `cofixEquiv` (`A` arbitrary, `B = 0`) and `output_separates`
    below (`A = 2, B = 1`). -/
theorem binCofix_subsingleton (x y : Cofix binPF.Obj) : x = y := by
  refine Cofix.bisim (fun _ _ => True) ?_ x y trivial
  intro a b _
  rw [liftr_iff]
  exact ⟨(), (Cofix.dest a).2, (Cofix.dest b).2, rfl, rfl, fun _ => trivial⟩

/-! ## § II — `A = 2`: a two-element head, and the behaviours come apart -/

/-- The **labelled chain** functor: one recursive position, the same arity as `idPF_Coalgebra`, but a
    two-element head. `Cofix streamPF.Obj` is Rutten's `2^{1*}`, the `Bool`-streams. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the two-element-head chain functor, held at the same arity as idPF_Coalgebra so that the head type is the only thing varying against binPF; Mathlib has Stream' but no PFunctor/QPF presentation of it (no Stream in Data/QPF or Data/PFunctor, no PFunctor in Data/Stream).
def streamPF : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

/-- The constant behaviour emitting `b` forever. -/
def constStream (b : Bool) : Cofix streamPF.Obj :=
  Cofix.corec (fun _ : PUnit => (⟨b, fun _ => PUnit.unit⟩ : streamPF.Obj PUnit)) PUnit.unit

/-- One step of the constant behaviour: it emits `b` and continues as itself. -/
theorem constStream_dest (b : Bool) :
    Cofix.dest (constStream b) = ⟨b, fun _ => constStream b⟩ := by
  unfold constStream
  rw [Cofix.dest_corec]
  rfl

/-- **THE HEAD SEPARATES.** Two behaviours at chain arity — one recursive position each, fewer than
    `binPF`'s two, and both non-terminating — are nevertheless **distinct**, told apart by a single
    observation of the head. Fewer successors than the subsingleton case, and yet more behaviours:
    that is the point. Rutten 10.2(5) at `A = 2, B = 1`. -/
theorem output_separates : constStream false ≠ constStream true := by
  intro h
  have hd : Cofix.dest (constStream false) = Cofix.dest (constStream true) := congrArg _ h
  rw [constStream_dest, constStream_dest] at hd
  exact Bool.false_ne_true (congrArg Sigma.fst hd)

/-! ## § III — The contrast -/

/-- **The head decides, not the arity.** Bundling the two instances: doubling the recursive positions
    while holding the head a singleton (`binPF`, `A = 1, B = 2`) leaves the final coalgebra a
    subsingleton, while doubling the head at chain arity (`streamPF`, `A = 2, B = 1`) already yields
    two distinct behaviours. Both are instances of Rutten 10.2(5), `|A|^{|B*|}`; neither is new. -/
theorem head_not_arity_separates :
    (∀ x y : Cofix binPF.Obj, x = y) ∧ constStream false ≠ constStream true :=
  ⟨binCofix_subsingleton, output_separates⟩

end ZeroParadox

/-! ## Axiom Purity Check

**Measured 2026-07-30, all four: `[propext, Classical.choice, Quot.sound]`.** The choice is inherited
from Mathlib's `QPF.Cofix`, which is `Quot (@Mcongr F q)` over the M-type construction — every
statement here mentions `Cofix`, and `#print axioms` follows the STATEMENT, not the proof. This
matches the ν-side footprint `Category/CoalgebraForkPlace.lean` already records (μ side choice-free,
ν side not). None of it is a new commitment: the proofs themselves are one `Cofix.bisim`, one
`Cofix.dest_corec`, and one `congrArg` on a `Sigma.fst`.
-/
section PurityCheck
open ZeroParadox

#print axioms binCofix_subsingleton
#print axioms constStream_dest
#print axioms output_separates
#print axioms head_not_arity_separates

end PurityCheck
