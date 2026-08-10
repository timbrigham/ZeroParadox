import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.State.StateSpace

set_option maxHeartbeats 400000

/-!
# The type bridge: a separated succession as an interface, with two known implementations

The snap's succession of **targets** — its **iterative bottoms** — shows up in two charts of the framework
that are DIFFERENT TYPES. (Iterative bottom: a bottom relative to its iteration, the base the next snap
re-seeds above, never ⊥ itself. `ε₀ ≠ ⊥` is bedrock, `epsilon0_ne_bot`. The qualifier carries the role
without asserting the identity; standardized 2026-07-19.)
- the **ordinal chart** — the ε-numbers `ε₀ < ε₁ < ε₂ < …`, consecutive ones separated by strict order
  (`ZeroParadox/Ordinal/SnapSuccession.lean`, `succession_lt_succ`);
- the **Hilbert chart** — the state vectors `T(S₀), T(S₁), …`, consecutive ones separated by orthogonality
  (`ZeroParadox/State/StateSpace.lean`, `t5_strict_orthogonal`, on ZP-D's DP-1).

These are the same phenomenon — "when one instance ends, another begins separated from the last" — but their
carriers are distinct types at **different universe levels** (`Ordinal : Type 1`, `StateSpace n : Type 0`).
They literally cannot be equated; asking whether the ordinal succession *is* the Hilbert succession is
ill-typed, the same type boundary as MC-1.

The honest bridge is therefore **not an identity but an interface**: state the *required attributes* of a
separated generating succession — a carrier, a separation relation, an ℕ-indexed succession, and the law
that consecutive terms are separated — and exhibit each chart as a *known implementation*. This is the
framework's own instance-vs-requirements move (you cannot name the object, only the requirements it meets,
of which each structure is a witness — the Yoneda/representability reading), built the same way
`Computability/SelfApp.lean` handles `AbstractSelfApp` across set theory and the 2-adics.

**Honest scope.** This states no new theorem: the two `separated` laws are the already-proved
`succession_lt_succ` (ordinal) and `t5_strict_orthogonal` (Hilbert). The content is the *identification* —
that both are witnesses of one interface — and the honest fence that the carriers are provably distinct
types, so the shared shape is the interface, never a cross-type `=`. One asymmetry is kept visible: the
ordinal implementation separates unconditionally, the Hilbert one only given a genuine-transition sequence
(consecutive states distinct).

## Engineer's Take

By using the abstract shape of epsilon zero from least fixed point, we can now define a generic
relationship to the entire class. We cannot cross a type boundary, however we can dictate shared shape and
position.
-/

namespace ZeroParadox

open Order Ordinal

universe u

/-- **The required attributes of a separated generating succession** (class X): a carrier, a separation
    relation `sep` (the apartness consecutive instances satisfy), an ℕ-indexed succession `seq`, and the
    law that consecutive terms are always separated. The ordinal ε-chain and the Hilbert state-chain are
    each a known implementation. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: an interface bundling a carrier with a separation relation and
-- an ℕ-indexed succession whose consecutive terms are separated. Mathlib has chains and apartness
-- relations separately but no bundled "separated succession" interface used to bridge differently-typed
-- framework charts (ordinal strict-order vs Hilbert orthogonality) as implementations of one shape.
structure SeparatedSuccession where
  /-- The carrier of this implementation. -/
  carrier : Type u
  /-- The separation relation consecutive instances satisfy. -/
  sep : carrier → carrier → Prop
  /-- The succession of instances, indexed by ℕ. -/
  seq : ℕ → carrier
  /-- Consecutive instances are always separated. -/
  separated : ∀ k, sep (seq k) (seq (k + 1))
  /-- **No instance is separated from ITSELF.** Without it the structure is exactly `Nonempty`:
      `sep := fun _ _ => True` with a constant `seq` discharges `separated`.

      ⚠ What it buys is `seq_ne_succ` — CONSECUTIVE distinctness, and **nothing more**. It does not
      give injectivity of `seq`, and a real implementation repeats: `hilbert_seq_collision` below
      exhibits `a ≠ b` with `seq a = seq b`.

      ⚠ Scoped to the SUCCESSION, not to the whole carrier. SEP-1 proposed full irreflexivity of
      `sep` and that is **false for the Hilbert chart**: `sep` there is orthogonality, and the zero
      vector is orthogonal to itself. The succession's terms are basis vectors, which are not. -/
  sep_irrefl_on_seq : ∀ k, ¬ sep (seq k) (seq k)

/-- **`Statement:` CONSECUTIVE instances are distinct** — a repeat at `k, k+1` would separate an
    instance from itself. ⚠ NOT "never repeats": injectivity of `seq` is false here, and
    `hilbert_seq_collision` exhibits `a ≠ b` with `seq a = seq b`. -/
theorem SeparatedSuccession.seq_ne_succ (T : SeparatedSuccession) (k : ℕ) :
    T.seq k ≠ T.seq (k + 1) := by
  intro h
  have hsep := T.separated k
  rw [← h] at hsep
  exact T.sep_irrefl_on_seq k hsep

/-! ### NO-GO gauge — and the question has to be posed correctly for this one.

**`SeparatedSuccession` takes NO PARAMETER** — `carrier` is a field — so *"what carrier fails?"* is
malformed: none can, and `carrier := ℕ, sep := (· ≠ ·), seq := id` inhabits it. The answerable
question is what a FIELD VALUE must satisfy, and without `sep_irrefl_on_seq` the answer is nothing:
`sep := fun _ _ => True` with a constant `seq` discharges every other field, making the structure
exactly `Nonempty` (SEP-1/MH-1). **That field excludes the constant value**, and `seq_ne_succ` is what
it buys — consecutive distinctness, not injectivity (Mathlib's `ne_of_irrefl` is the same step for a
globally irreflexive relation). ⚠ FULL irreflexivity of `sep` would not work: orthogonality is
reflexive at the zero vector, which is why the field is scoped to `seq`. -/

/-- **Implementation 1 — the ordinal chart.** The ε-numbers `ε_ k`, separated by strict order. The
    `separated` law is tonight's `succession_lt_succ`. -/
noncomputable def ordinalSuccession : SeparatedSuccession.{1} where
  carrier := Ordinal.{0}
  sep := (· < ·)
  seq := fun k => Ordinal.epsilon (k : Ordinal.{0})
  separated := fun k => by
    have h := succession_lt_succ (k : Ordinal.{0})
    simpa [Nat.cast_succ, Order.succ_eq_add_one] using h
  sep_irrefl_on_seq := fun _ => lt_irrefl _

/-- **Implementation 2 — the Hilbert chart.** The state vectors `T(Sₖ)`, separated by orthogonality
    (`⟨·,·⟩ = 0`). The `separated` law is ZP-D's `t5_strict_orthogonal`, given a genuine-transition
    sequence (consecutive states distinct). -/
noncomputable def hilbertSuccession (n : ℕ) (S : ℕ → Fin n) (hS : ∀ k, S k ≠ S (k + 1)) :
    SeparatedSuccession where
  carrier := StateSpace n
  sep := fun x y => @inner ℂ (StateSpace n) _ x y = 0
  seq := fun k => transitionOp n (S k)
  separated := fun k => t5_strict_orthogonal n S k (hS k)
  -- A basis vector is not orthogonal to itself: `⟪e i, e i⟫ = 1 ≠ 0`.
  sep_irrefl_on_seq := fun k => by
    simp [transitionOp, basisVec]

/-! ### Faithfulness of the enumeration — an IMPLEMENTATION split

**Origin (Tim, 2026-08-05): "succession is a state of representation."** Step 0 measured the
structural fact that motivates it: `SeparatedSuccession` carries an ℕ-indexed `seq` and a *relation*
between consecutive terms, and **no transition function** — nothing maps instance `n` to instance
`n+1`. So the well-posed question about a succession is not whether the step map is injective (there is
no step map) but whether the **enumeration** is: does an index name a unique instance?

⚠ **The framing is Tim's and is not a Lean proposition.** What follows is: the two implementations
answer that question **oppositely**.

⚠ **This is an IMPLEMENTATION split, NOT a carrier split — and an earlier draft mislabelled it
`Reading: CARRIER kind`, with the ℚ₂/ℝ analogy attached.** That was wrong twice over. `StateSpace n` is
`EuclideanSpace ℂ (Fin n)`, which for `n ≥ 1` is **infinite**; what is finite is the **label set**
`Fin n`. A gate
built the counterexample (independently rebuilt and compiled at round 2): for `n ≥ 2`, a
`SeparatedSuccession` on the *same* carrier with the *same* orthogonality relation whose `seq` **is**
injective. So faithfulness is not impossible on the Hilbert carrier — it is
lost by *this labelling scheme*. The ℚ₂/ℝ analogy is inapt precisely because there the snap genuinely
**cannot** exist in ℝ.

**No POV KIND is claimed here**, because none of the five fits "depends on the implementation". What is
claimed is the two `Statement:`s below and the observation that **the structure does not force
faithfulness either way.** -/

/-- **`Statement:` the ordinal chart is a FAITHFUL enumeration** — distinct indices name distinct
instances. Immediate from `succession_strictMono`; the phrase *"never returns to a rung it has already
occupied"* is **`succession_lt_succ`'s** docstring three declarations further down
(`ZeroParadox/Ordinal/SnapSuccession.lean`), not that one's. This states it as injectivity of `seq`.

**Prior art:** `Ordinal.epsilon` is `abbrev epsilon := veblen 1`, so Mathlib gives both
`Ordinal.veblen_injective 1` and `Ordinal.veblen_right_strictMono 1` directly
(`Mathlib/SetTheory/Ordinal/Veblen.lean`). The delta here is only the `ℕ → Ordinal` cast; the corpus
route via `succession_strictMono` is kept for locality, and the library names are cited rather than
worked around. -/
theorem ordinal_seq_injective : Function.Injective ordinalSuccession.seq := by
  intro a b hab
  have h : Ordinal.epsilon (a : Ordinal.{0}) = Ordinal.epsilon (b : Ordinal.{0}) := hab
  exact_mod_cast succession_strictMono.injective h

/-- **`Statement:` the Hilbert chart's labels CANNOT be faithful.** Labels are drawn from `Fin n`, a
finite type, while the index set is `ℕ`: pigeonhole forbids injectivity outright, for **any** choice of
`S`. This is not a defect of a particular labelling — the label set has run out of room.

⚠ **This declaration IS Mathlib's `not_injective_infinite_finite` applied to `S`** — nothing is added
but the instantiation and the name. Kept for readability beside its siblings; do not cite it as new. -/
theorem hilbert_labels_not_injective (n : ℕ) (S : ℕ → Fin n) : ¬ Function.Injective S :=
  not_injective_infinite_finite S

/-- **`Statement:` and the collision is EXHIBITED** — two distinct indices whose labels agree.
⚠ Likewise **literally `Finite.exists_ne_map_eq_of_infinite S`**; an instantiation, not a new result. -/
theorem hilbert_label_collision (n : ℕ) (S : ℕ → Fin n) :
    ∃ a b : ℕ, a ≠ b ∧ S a = S b :=
  Finite.exists_ne_map_eq_of_infinite S

/-- **`Statement:` the collision reaches the INSTANCES, not just the labels.** Since
`seq k = transitionOp n (S k)`, a label collision is an instance collision: **two distinct positions in
the succession name the same instance.** That pair is the fiber — the thing an index fails to
determine. -/
theorem hilbert_seq_collision (n : ℕ) (S : ℕ → Fin n) (hS : ∀ k, S k ≠ S (k + 1)) :
    ∃ a b : ℕ, a ≠ b ∧ (hilbertSuccession n S hS).seq a = (hilbertSuccession n S hS).seq b := by
  obtain ⟨a, b, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite S
  exact ⟨a, b, hne, by simp only [hilbertSuccession]; rw [heq]⟩

/-- **`Statement:` so the Hilbert enumeration is not injective** — stated as the negation so it sits
beside `ordinal_seq_injective` and the split is readable at a glance.

⚠ **`separated` does NOT give injectivity, and that is the point.** It constrains only *consecutive*
terms, so `seq 0 = seq 5` is entirely permitted; the ordinal chart avoids it by strict monotonicity,
which is a stronger property than the structure requires. -/
theorem hilbert_seq_not_injective (n : ℕ) (S : ℕ → Fin n) (hS : ∀ k, S k ≠ S (k + 1)) :
    ¬ Function.Injective (hilbertSuccession n S hS).seq := by
  intro hinj
  obtain ⟨a, b, hne, heq⟩ := hilbert_seq_collision n S hS
  exact hne (hinj heq)

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms ordinalSuccession
#print axioms hilbertSuccession
#print axioms SeparatedSuccession.seq_ne_succ
#print axioms ordinal_seq_injective
#print axioms hilbert_labels_not_injective
#print axioms hilbert_label_collision
#print axioms hilbert_seq_collision
#print axioms hilbert_seq_not_injective
end PurityCheck
