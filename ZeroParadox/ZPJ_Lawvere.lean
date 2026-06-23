import ZeroParadox.ZPJ_SelfApp
import Mathlib.Tactic

/-!
# ZPJ — The Lawvere bridge (keystone Tier-6 upgrade probe)

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

/-! ## § IV. Where genuine Lawvere fixed points DO live (the face split)

    The negative above is face-specific, not a blanket "ZP has nothing to do with Lawvere." A Lawvere
    witness (point-surjection) genuinely exists in the **partial / computability** setting: a universal
    machine gives a surjection from indices onto partial computable functions, and **Kleene's recursion
    theorem is the textbook instance of Lawvere's theorem** — a real diagonal-produced fixed point.
    That is ZP-K's face (the Kleene quine). So the keystone splits honestly:

    * **set-theoretic / lattice face** (this file, `nontrivial_lattice_no_witness`): NO witness on a
      nontrivial total lattice; ⊥ is a *posited* fixed point — Lawvere is an analogy here.
    * **computability face** (ZP-K): a witness *does* exist (universality); the quine is a *genuine*
      Lawvere fixed point.

    The unifying "diagonal fixed point" keystone is therefore real in spirit but **mechanism-dependent**:
    some faces are Lawvere instances, others share only the shape. This is the precise, defensible
    refinement of the Tier-6 conjecture — and it is what the formalization establishes. -/

end ZeroParadox.ZPJ_Lawvere

section PurityCheck
open ZeroParadox.ZPJ_Lawvere
#print axioms fixedPoint_of_witness
#print axioms no_witness_of_fixedPointFree
#print axioms fixedPointFree_of_nontrivial
#print axioms no_witness_of_nontrivial
#print axioms nontrivial_lattice_no_witness
end PurityCheck
