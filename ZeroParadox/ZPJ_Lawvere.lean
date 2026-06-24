import ZeroParadox.ZPJ_SelfApp
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

namespace ZeroParadox.ZPJ_Lawvere

open ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPJ_SelfApp

set_option maxHeartbeats 400000

/-! ## § I. Lawvere's theorem, repackaged (the diagonal hypothesis named) -/

/-- An endofunction `g : β → β` "has a Lawvere witness" when the diagonal hypothesis of Lawvere's
    theorem holds: a point-surjection `α → (α → β)`. This is exactly the hypothesis Cantor's theorem
    shows is *impossible* for `β` with a fixed-point-free endomap. -/
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

    The 2-adic fixed point (0 = unique fixed point of x ↦ 2x in ℚ₂, ZP-B / `ZPJ_SelfApp.q2_unique_fp`)
    is also a posited fixed point of one specific self-map. ℚ₂ is a nontrivial total type, so the same
    Cantor obstruction applies: no Lawvere witness. -/

theorem q2_no_witness : ¬ HasLawvereWitness ℚ_[2] :=
  no_witness_of_nontrivial (zero_ne_one (α := ℚ_[2]))

/-! ## § V. The computability face — a GENUINE fixed point, in a different category

    Here the verdict flips, and the reason is the **category**. The failure above is in **Set** (raw
    types, *all* endofunctions): a witness would force every endo to have a fixed point, impossible by
    Cantor. The computability face lives in the **effective** setting, where "endomap" means *computable*
    endomap — and the fixed-point-free diagonal (the `g` Cantor builds) is **not computable**, so the
    obstruction vanishes. Mathlib's `Nat.Partrec.Code.fixed_point` (Rogers / Kleene's recursion theorem)
    is exactly this: *every computable* self-map on codes has a fixed point. This is ZP-K's face (the
    Kleene quine), and it is a genuine diagonal-produced fixed point. -/

/-- **Computability face (genuine instance).** Every *computable* self-map on codes has a fixed point —
    Rogers' fixed-point / Kleene's recursion theorem (`Nat.Partrec.Code.fixed_point`). The escape from
    the Cantor obstruction is computability: the fixed-point-free diagonal is not a computable endomap. -/
theorem computability_face_fixedPoint {f : Nat.Partrec.Code → Nat.Partrec.Code} (hf : Computable f) :
    ∃ c, Nat.Partrec.Code.eval (f c) = Nat.Partrec.Code.eval c :=
  Nat.Partrec.Code.fixed_point hf

/-! ## § VI. The completeness verdict (the face table, machine-checked where it can be)

    | Face                         | self-map        | In **Set** (all endos) | Status                        |
    |------------------------------|-----------------|------------------------|-------------------------------|
    | lattice / abstract (selfApp) | `selfApp`       | NO witness — posited   | `nontrivial_lattice_no_witness` ✓ |
    | set theory (Quine atom)      | x ↦ {x}         | (= lattice; metatheoretic literal) | via the lattice ✓ |
    | 2-adic (×2 in ℚ₂)            | x ↦ 2x          | NO witness — posited   | `q2_no_witness` ✓             |
    | computability (Kleene quine) | computable endo | n/a — lives in **effective**, not Set | `computability_face_fixedPoint` ✓ (genuine) |

    **The honest verdict:** the test is *category-relative*. In **Set** (raw types, all endofunctions),
    **no** face is a Lawvere fixed point — Cantor forbids the witness for every nontrivial total type
    (lattice and 2-adic proven; set theory is the lattice case, its literal ⊥={⊥} metatheoretic). The
    computability face is a **genuine** Lawvere/recursion fixed point, but it lives in the **effective**
    category, where computability removes the fixed-point-free diagonal.

    So the keystone unifies a **shape** (the diagonal), not a single mechanism: the total faces carry a
    *posited* fixed point that shares the diagonal shape; the computability face carries a fixed point
    that is *genuinely produced* by the diagonal — in its own category. The cross-face identification is
    the MC-1-style commitment (shape-identity), confirmed precise; it is **not** a single-mechanism
    theorem, and the lattice/2-adic faces are *provably not* Set-level Lawvere instances. This is the
    sharpened, partly-proven replacement for the bare Tier-6 conjecture. -/

end ZeroParadox.ZPJ_Lawvere

section PurityCheck
open ZeroParadox.ZPJ_Lawvere
#print axioms fixedPoint_of_witness
#print axioms no_witness_of_fixedPointFree
#print axioms fixedPointFree_of_nontrivial
#print axioms no_witness_of_nontrivial
#print axioms nontrivial_lattice_no_witness
#print axioms q2_no_witness
#print axioms computability_face_fixedPoint
end PurityCheck
