import ZeroParadox.Category.DiagonalWitness

/-!
# Add-one, doubling and the relativized Lawvere witness: on ℤ, ℤ_[2] and partial digit streams

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
§ I: add-one on `ℤ_[2]`, and on `ℤ`, fixes no point, so no class containing it has a relativized
witness. § II: add-one and doubling on finite partial digit streams. § II fences the Take's dead zero,
`botEnd`, against the empty stream.
-/

/-! ## § I. Add-one on `ℤ_[2]` and on `ℤ` -/

-- Statement: if an endomap in the class `M` fixes no point, there is no relativized witness
--   `HasWitnessRel β M`.
#check @ZeroParadox.no_witnessRel_of_admissible_fpf

-- Statement: on `ℤ_[2]`, add-one fixes no point: Mathlib's `succ_ne_self`.
example (x : ℤ_[2]) : x + 1 ≠ x := succ_ne_self x

-- Statement: on `ℤ_[2]`, no class `M` containing `x ↦ x + 1` has a relativized witness.
example (M : (ℤ_[2] → ℤ_[2]) → Prop) (h : M (· + 1)) : ¬ ZeroParadox.HasWitnessRel ℤ_[2] M :=
  ZeroParadox.no_witnessRel_of_admissible_fpf h fun _ hx => by simp at hx

-- Statement: the continuous maps on `ℤ_[2]` contain add-one, so `¬ HasWitnessRel ℤ_[2] Continuous`.
-- Reading: on codes, for computable maps compared up to `eval`, the obstruction is removed
--   (`no_computable_evalFixedPointFree`); on `ℤ_[2]`, with its own equality, add-one keeps it.
example : ¬ ZeroParadox.HasWitnessRel ℤ_[2] Continuous :=
  ZeroParadox.no_witnessRel_of_admissible_fpf (continuous_add_const 1) fun _ hx => by simp at hx

-- Statement: on `ℤ`, no class `M` containing `x ↦ x + 1` has a relativized witness.
-- Reading: § I's obstruction is not 2-adic: the `ℤ_[2]` proof script closes unchanged over `ℤ`.
example (M : (ℤ → ℤ) → Prop) (h : M (· + 1)) : ¬ ZeroParadox.HasWitnessRel ℤ M :=
  ZeroParadox.no_witnessRel_of_admissible_fpf h fun _ hx => by simp at hx

namespace ZeroParadox

/-! ## § II. Add-one and doubling on finite partial digit streams

A partial stream is a `List Bool`, least-significant digit first, ordered by prefix; its least element is
the empty stream (`List.nil_prefix`), in a different type from ℤ_[2]'s `0`, and no `ZPSemilattice`
structure is put on `List Bool`. Iterating from a least element is Scott's schema, "Data types as
lattices", SIAM J. Comput. 5 (1976), Thm 1.4, p. 526, on `Pω` (any complete lattice: the `#check` below);
extending a continuous map into `Pω` from a subspace is its Thm 1.5, p. 527; and extending a
Cantor-continuous map into a continuous ω-CPO with meets, from Cantor space to finite and infinite words,
is Amorim et al., LICS 2021, Lemma 8(ii), p. 5 of arXiv:2011.13171v2. `List Bool` is not claimed an
instance of these; the doubling stages have no upper bound under `<+:` (§ II's last `example`). -/

-- Statement: Mathlib, Kleene's fixed-point theorem: on a complete lattice, for monotone
--   ω-Scott-continuous `f`, `lfp f = ⨆ n, f^[n] ⊥`.
#check @fixedPoints.lfp_eq_sSup_iterate
-- Statement: Mathlib, the dual: on a complete lattice, for monotone `f` whose order dual is
--   ω-Scott-continuous, `gfp f = ⨅ n, f^[n] ⊤`.
#check @fixedPoints.gfp_eq_sInf_iterate

-- Reading: the Take's dead zero is the all-zeros tape, in either carrier. Here it is
--   `botEnd : End = ℕ → Fin 2`.
-- Statement: COINCIDENCE — `botEnd` is ⊥ of `End` under pointwise max and the fixed point of boundary
--   doubling (`boundaryDouble_botEnd`, `boundaryDouble_unique_fp`,
--   `ZeroParadox/Valuation/PoleCompletion.lean`). The all-false tape ℕ → Bool carries the same
--   coincidence (`ZeroParadox/Category/IgnoranceSeam.lean`).
-- Statement: CARRIER — the least element of the prefix order is the empty stream `[]`, in a different
--   type from `botEnd`; zero-fill sends `[]` to the all-false tape, ⊥ of the pointwise order on
--   `ℕ → Bool` (`ZeroParadox/Category/IgnoranceSeam.lean` § I, its first `example`).

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

/-- `Statement:` `partialDouble` fixes no partial stream. -/
theorem partialDouble_ne_self (w : List Bool) : partialDouble w ≠ w :=
  List.cons_ne_self false w

-- Statement: on `ℤ_[2]`, doubling fixes exactly `0`.
-- Reading: as with § I's `ℤ` note, this cell is not 2-adic: the proof script is commutative-ring arithmetic.
example (x : ℤ_[2]) : 2 * x = x ↔ x = 0 :=
  ⟨fun h => by linear_combination h, fun h => by rw [h, mul_zero]⟩

-- Statement: cell by cell, add-one fixes only `[]` among partial streams (`partialAddOne_fixed_iff`)
--   and no point of `ℤ_[2]` (the first `example` of § I); doubling fixes no partial stream
--   (`partialDouble_ne_self`) and only `ℤ_[2]`'s `0` (the `example` above).
-- Reading: the crossed pair.

/-- `Statement:` `partialDouble` iterated `n` times from the empty stream. -/
def partialDoubleStage (n : ℕ) : List Bool := Nat.repeat partialDouble n []

/-- `Statement:` stage `n` is `n` copies of `false`. -/
theorem partialDoubleStage_eq (n : ℕ) : partialDoubleStage n = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => show partialDouble (partialDoubleStage n) = _; rw [ih]; rfl

-- Statement: each stage is a prefix of the next: the stages form a chain in the prefix order.
example (n : ℕ) : partialDoubleStage n <+: partialDoubleStage (n + 1) := by
  rw [partialDoubleStage_eq, partialDoubleStage_eq]
  exact ⟨[false], by simp [List.replicate_succ']⟩

-- Statement: every stage, its unknown digits filled with `false`, is the all-false tape.
example (n : ℕ) : (fun k => (partialDoubleStage n).getD k false) = fun _ => false := by
  funext k
  rw [partialDoubleStage_eq, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

-- Statement: read as partial digit maps `ℕ → Part Bool`, an ω-CPO under Mathlib's pointwise order,
--   the stages have a supremum: the all-false word.
example : OmegaCompletePartialOrder.ωSup
    (⟨fun n k => ((partialDoubleStage n)[k]? : Part Bool), fun n m hnm k b hb => by
      dsimp only at hb ⊢
      rw [partialDoubleStage_eq, List.getElem?_replicate] at hb ⊢
      split_ifs at hb ⊢ <;> first | exact hb | (exfalso; omega) | simp at hb⟩ :
      OmegaCompletePartialOrder.Chain (ℕ → Part Bool)) = fun _ => Part.some false := by
  funext k
  refine Part.eq_some_iff.2 ((Part.mem_ωSup false _).2 ⟨k + 1, ?_⟩)
  show Part.some false = ((partialDoubleStage (k + 1))[k]? : Part Bool)
  rw [partialDoubleStage_eq, List.getElem?_replicate, if_pos (Nat.lt_succ_self k)]
  rfl

-- Statement: the stages have no upper bound in the prefix order on `List Bool`.
example : ¬ ∃ u : List Bool, ∀ n, partialDoubleStage n <+: u := fun ⟨u, h⟩ => by
  have := (h (u.length + 1)).length_le
  rw [partialDoubleStage_eq, List.length_replicate] at this
  omega
-- Reading: CARRIER — two charts. Among finite words the stages have no upper bound (the `example`
--   above); as partial digit maps their supremum is the all-false word (the `ωSup` `example`).
--   Separately, zero-fill sends every stage, `[]` included, to the all-false tape (the zero-fill
--   `example`).

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
