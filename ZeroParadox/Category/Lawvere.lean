import ZeroParadox.Computability.SelfApp
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic

/-!
# ZPJ — The Lawvere bridge (keystone Tier-6 upgrade probe)

## Engineer's Take

The Lawvere file here started while researching the shape of ZPJ. At the time I wasn't as familiar
with the prior art as I would have liked. The shape of the keystone here, it felt like it could have
fit using the Lawvere framework. This iteration showed that only the computability theory really had
precisely the structure needed. This eventually gave way to me looking at other routes.

---

**Status: PROBE, stub-first.** Goal: test whether ZP's self-application fixed point (`AbstractSelfApp`,
`t_exec` / the Quine atom ⊥) is an *instance* of Lawvere's fixed-point theorem, or whether it is a
*posited* fixed point that merely has the same shape (the Tier-6 conjecture).

Mathlib gives Lawvere's theorem in function form:
  `Function.exists_fixed_point_of_surjective : (f : α → α → β) → Surjective f → ∀ g : β → β, ∃ x, g x = x`
(its docstring: "an instance of Lawvere's fixed-point theorem ... the diagonal argument underlying
cantor_surjective"). The hypothesis is a **point-surjection** `α → (α → β)` (the diagonal); the
conclusion is that *every* endofunction has a fixed point.

The honest question, made precise: ZP's `AbstractSelfApp` provides `selfApp : L → L` with a fixed point
⊥ asserted as a class field. Lawvere *derives* a fixed point from a surjection. So the bridge is: does
ZP's setting supply the diagonal surjection from which the fixed point would *follow*?
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice ZeroParadox

set_option maxHeartbeats 400000

/-! ## § I. Lawvere's theorem, repackaged (the diagonal hypothesis named) -/

/-- An endofunction `g : β → β` "has a Lawvere witness" when the diagonal hypothesis of Lawvere's
    theorem holds: a point-surjection `α → (α → β)`. This is exactly the hypothesis Cantor's theorem
    shows is *impossible* for `β` with a fixed-point-free endomap. -/
-- [ZP-CUSTOM] no Mathlib named predicate | reason: Mathlib proves Lawvere's theorem (Function.exists_fixed_point_of_surjective) but exposes no reusable predicate for the diagonal hypothesis (β admits a point-surjection α → (α → β)). Naming it lets the face-split state, per face, whether the hypothesis holds (Set faces refuted by Cantor; computability face genuine). Naming alias (cf. IsComputationalQuine); every theorem reduces to the Mathlib lemma, no new axiomatic content.
def HasLawvereWitness (β : Type*) : Prop :=
  ∃ (α : Type*) (f : α → α → β), Function.Surjective f

/-- **Lawvere (repackaged).** A Lawvere witness on `β` forces *every* endofunction of `β` to have a
    fixed point. This is just `Function.exists_fixed_point_of_surjective`. -/
theorem fixedPoint_of_witness {β : Type*} (h : HasLawvereWitness β) (g : β → β) :
    ∃ x, g x = x := by
  obtain ⟨α, f, hf⟩ := h
  exact Function.exists_fixed_point_of_surjective f hf g

/-! ## § II. A Lawvere witness is the paradox-condition (the contrapositive engine)

    A witness forces *every* endofunction to have a fixed point. So a witness is **incompatible with a
    fixed-point-free endomap** — which is exactly how the diagonal drives the paradoxes (Cantor/Russell):
    assume the surjection, the fixed-point-free map gets a fixed point, contradiction. -/

/-- A Lawvere witness on `β` is incompatible with any fixed-point-free endofunction of `β`. -/
theorem no_witness_of_fixedPointFree {β : Type*} (g : β → β) (hg : ∀ x, g x ≠ x) :
    ¬ HasLawvereWitness β := by
  intro h
  obtain ⟨x, hx⟩ := fixedPoint_of_witness h g
  exact hg x hx

/-- Any type with two distinct elements admits a fixed-point-free endofunction. -/
theorem fixedPointFree_of_nontrivial {β : Type*} {b₀ b₁ : β} (hne : b₀ ≠ b₁) :
    ∃ g : β → β, ∀ x, g x ≠ x := by
  classical
  refine ⟨fun x => if x = b₀ then b₁ else b₀, fun x => ?_⟩
  by_cases hx : x = b₀
  · subst hx; simpa using hne.symm
  · simp only [if_neg hx]; exact fun h => hx h.symm

/-- **Nontrivial types carry no Lawvere witness** (Cantor). The diagonal surjection cannot exist once
    there are two distinct points. -/
theorem no_witness_of_nontrivial {β : Type*} {b₀ b₁ : β} (hne : b₀ ≠ b₁) :
    ¬ HasLawvereWitness β := by
  obtain ⟨g, hg⟩ := fixedPointFree_of_nontrivial hne
  exact no_witness_of_fixedPointFree g hg

/-! ## § III. The keystone verdict (set-theoretic / lattice face)

    ZP's `AbstractSelfApp` provides `selfApp : L → L` with ⊥ asserted as its fixed point. For a
    *nontrivial* lattice (⊥ and at least one other element) there is **no Lawvere witness on `L`** —
    so ⊥ is a *posited* fixed point of one specific self-map, NOT a Lawvere-derived fixed point.
    The "diagonal fixed point" name is an analogy for this face, confirmed: it cannot be a literal
    Lawvere instance, because a literal instance would force *every* endomap of `L` to have a fixed
    point (false for nontrivial `L`). -/

/-- **Keystone verdict, lattice face.** A nontrivial `ZPSemilattice` (some element ≠ ⊥) carries no
    Lawvere witness — so for any `AbstractSelfApp` on it, ⊥ is a *posited* fixed point of one specific
    self-map, NOT Lawvere-produced. (The result needs only nontriviality, not the `AbstractSelfApp`
    instance — which is itself the point: the diagonal/Lawvere mechanism is structurally absent here.)
    The connection is an analogy at this face, not a literal instance. -/
theorem nontrivial_lattice_no_witness {L : Type*} [ZPSemilattice L] (a : L) (ha : a ≠ bot) :
    ¬ HasLawvereWitness L :=
  no_witness_of_nontrivial (b₀ := a) (b₁ := bot) ha

/-! ## § IV. The 2-adic face — same failure as the lattice (Cantor)

    The 2-adic fixed point (0 = unique fixed point of x ↦ 2x in ℚ₂, ZP-B / `q2_unique_fp`)
    is also a posited fixed point of one specific self-map. ℚ₂ is a nontrivial total type, so the same
    Cantor obstruction applies: no Lawvere witness. -/

theorem q2_no_witness : ¬ HasLawvereWitness ℚ_[2] :=
  no_witness_of_nontrivial (zero_ne_one (α := ℚ_[2]))

/-! ## § V. The computability face — a GENUINE fixed point, in a different category

    The verdict flips, and the reason is the **category**. § IV's failure is in **Set** (all
    endofunctions), where Cantor forbids the witness. Here "endomap" means *computable*, and Mathlib's
    `Nat.Partrec.Code.fixed_point` gives every such map a fixed point **up to `eval`**.
    ⚠ **The qualifier is load-bearing, because the Cantor contrast above is drawn in the LITERAL
    register and the literal claim is FALSE here too:** `fun c => Code.pair c c` is total, computable
    and returns its own input for no `c`. The escape is not that the diagonal stops existing — it is
    that `eval` lands in `ℕ →. ℕ`, a different codomain from `Code → Code`, so the Set refutation
    never applied. ZP-K's face (the Kleene quine), genuine at the level of `eval`. -/

/-- `Statement:` a fixed point **up to `eval`**, not a literal one (Rogers / Kleene).
    ⚠ `fun c => Code.pair c c` is a total computable endomap with no `c` satisfying `f c = c`;
    the escape is `eval`'s codomain being `ℕ →. ℕ` rather than `Code`. See § V. -/
theorem computability_face_fixedPoint {f : Nat.Partrec.Code → Nat.Partrec.Code} (hf : Computable f) :
    ∃ c, Nat.Partrec.Code.eval (f c) = Nat.Partrec.Code.eval c :=
  Nat.Partrec.Code.fixed_point hf

/-! ## § VI. The completeness verdict — the face table

**All four faces fail the Set test identically**: `Code` is a nontrivial total type, so
`nontrivial_no_witness` forbids the witness there exactly as for the lattice and the 2-adics. What
distinguishes the computability row is the SECOND category it also lives in, never its Set verdict.
⚠ The keystone unifies a **shape**, not a mechanism, and not a cross-category identity. Table,
verdict and fences: `ZeroParadox/Category/Lawvere.md`. -/

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms fixedPoint_of_witness
#print axioms no_witness_of_fixedPointFree
#print axioms fixedPointFree_of_nontrivial
#print axioms no_witness_of_nontrivial
#print axioms nontrivial_lattice_no_witness
#print axioms q2_no_witness
#print axioms computability_face_fixedPoint
end PurityCheck
