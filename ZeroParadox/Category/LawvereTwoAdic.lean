import ZeroParadox.Category.DiagonalWitness

/-!
# The 2-adic face of the relativized Lawvere witness, and add-one on partial digit streams

## Engineer's Take

This feels almost like Lawvere is in itself describing motion, and we are trying to build a Rosetta
Stone. In my mind it is all about the shape. Motion and self-description are the same shape, Lawvere
is one way of stating it, and each specific framework, like computability, has its own language for
it. The question is whether the implication moves across if we can prove the same shape and the same
requirements are provided by another class. If computability can be claimed to be mandatory given an
infinite set of starting data and self-reference, does that allow us to make the wider claim across
the p-adics and the other frameworks? Maybe being computable is exactly the condition we are looking
for. The dead zero, zero point zero with an infinite number of zeros, is the base tape we always talk
about, almost as if it is the first fixed point itself. Zero itself blossoms outwards before it moves
up.

---

## Formal Overview (AI-assisted)

§ I: add-one on `ℤ_[2]` fixes no point, so no admissible class containing it carries a relativized
witness. § II: add-one and doubling on finite partial digit streams.
-/

/-! ## § I. Add-one on `ℤ_[2]` -/

-- Statement: if an endomap in the class `M` fixes no point, there is no relativized witness
--   `HasWitnessRel β M`.
#check @ZeroParadox.no_witnessRel_of_admissible_fpf

-- Statement: on `ℤ_[2]`, no class `M` containing `x ↦ x + 1` has a relativized witness.
example (M : (ℤ_[2] → ℤ_[2]) → Prop) (h : M (· + 1)) : ¬ ZeroParadox.HasWitnessRel ℤ_[2] M :=
  ZeroParadox.no_witnessRel_of_admissible_fpf h fun _ hx => by simp at hx

-- Statement: the continuous maps on `ℤ_[2]` are such a class.
-- Reading: on codes the obstruction is removed by equality up to `eval`
--   (`no_computable_evalFixedPointFree`); on `ℤ_[2]`, with its own equality, add-one keeps it.
example : ¬ ZeroParadox.HasWitnessRel ℤ_[2] Continuous :=
  ZeroParadox.no_witnessRel_of_admissible_fpf (continuous_add_const 1) fun _ hx => by simp at hx

namespace ZeroParadox

/-! ## § II. Add-one and doubling on finite partial digit streams

A partial stream is a `List Bool`, least-significant digit first, ordered by prefix; the empty stream
is the least element of that order (`List.nil_prefix`). It lives in a different type from ℤ_[2]'s
`0`, no `=` relates them, and this file puts no `ZPSemilattice` structure on `List Bool`. Iterating
from a least element is the schema of Scott, "Data types as lattices", SIAM J. Comput. 5 (1976),
Thm 1.4, p. 526, stated there on `Pω`; `List Bool` is not claimed an instance of it. -/

/-- `Statement:` add-one on partial streams: the carry runs through `true` digits and stops at the
    first `false`, or where the known digits end. -/
def partialAddOne : List Bool → List Bool
  | [] => []
  | true :: w => false :: partialAddOne w
  | false :: w => true :: w

/-- `Statement:` `partialAddOne` is monotone for the prefix order. -/
theorem partialAddOne_mono : ∀ {w v : List Bool}, w <+: v → partialAddOne w <+: partialAddOne v
  | [], _, _ => List.nil_prefix
  | _ :: _, [], h => absurd h (by simp)
  | b :: _, _ :: _, h => by
    obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
    cases b with
    | true => exact List.cons_prefix_cons.mpr ⟨rfl, partialAddOne_mono h'⟩
    | false => exact List.cons_prefix_cons.mpr ⟨rfl, h'⟩

/-- `Statement:` `partialAddOne` preserves length. -/
theorem partialAddOne_length : ∀ w : List Bool, (partialAddOne w).length = w.length
  | [] => rfl
  | true :: w => by simp [partialAddOne, partialAddOne_length w]
  | false :: _ => rfl

/-- `Statement:` the empty stream is the only fixed point of `partialAddOne`. -/
theorem partialAddOne_fixed_iff (w : List Bool) : partialAddOne w = w ↔ w = [] := by
  constructor
  · intro h
    cases w with
    | nil => rfl
    | cons b w => cases b <;> simp [partialAddOne] at h
  · rintro rfl; rfl

/-- `Statement:` doubling on partial streams prepends the digit `false`. -/
def partialDouble (w : List Bool) : List Bool := false :: w

/-- `Statement:` `partialDouble` fixes no partial stream. `Reading:` add-one's opposite pair; on ℚ₂,
    `x ↦ 2x` fixes exactly `0` (`q2_zero_is_fixed`, `q2_unique_fp`). -/
theorem partialDouble_ne_self (w : List Bool) : partialDouble w ≠ w :=
  List.cons_ne_self false w

/-- `Statement:` `partialDouble` iterated `n` times from the empty stream. -/
def partialDoubleStage (n : ℕ) : List Bool := Nat.repeat partialDouble n []

/-- `Statement:` stage `n` is `n` copies of `false`. -/
theorem partialDoubleStage_eq (n : ℕ) : partialDoubleStage n = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => show partialDouble (partialDoubleStage n) = _; rw [ih]; rfl

-- `Statement:` each stage is a prefix of the next: the stages form a chain in the prefix order.
example (n : ℕ) : partialDoubleStage n <+: partialDoubleStage (n + 1) := by
  rw [partialDoubleStage_eq, partialDoubleStage_eq]
  exact ⟨[false], by simp [List.replicate_succ']⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms partialAddOne
#print axioms partialAddOne_mono
#print axioms partialAddOne_length
#print axioms partialAddOne_fixed_iff
#print axioms partialDouble
#print axioms partialDouble_ne_self
#print axioms partialDoubleStage
#print axioms partialDoubleStage_eq
end PurityCheck
