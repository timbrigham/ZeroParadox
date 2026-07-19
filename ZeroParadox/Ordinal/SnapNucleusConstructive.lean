import ZeroParadox.Ordinal.SyntacticCollapse
import Mathlib.Order.Nucleus

set_option maxHeartbeats 1000000

/-!
# The snap nucleus has no choice-free syntactic counterpart: a proved obstruction

## What this file is

An **obstruction result**. `ZeroParadox/Ordinal/SnapNucleus.lean` defines
`snapNucleus : Nucleus Ordinal` as `Ordinal.nfp (fun a => Ordinal.omega0 ^ a)`, with measured footprint
`[propext, Classical.choice, Quot.sound]`. This file asks the ZP-N question of that object — can the
same content be had choice-free on the syntactic ordinal-notation substrate? — and answers **no**, with a
machine-checked impossibility rather than a failed attempt.

## What this does NOT establish

* **`snapNucleus` is not made choice-free here, and cannot be.** Mathlib's `Ordinal` is a quotient of
  well-ordered types; `Classical.choice` sits in the *type*, before any proof runs. No rewriting of
  `snapNucleus`'s proof can remove it. Nothing below is a re-proof, replacement, or discharge of
  `snapNucleus`, `snapNucleus_bot`, or any result in `SnapNucleus.lean`. Those stand exactly as they are,
  with the footprint they have.
* **This is a different declaration on a different carrier.** Everything here lives on `ONote` (raw
  Cantor-normal-form syntax) and on `SynONote`, the type synonym below carrying the comparator-derived
  order. `ONote` is not `Ordinal` and `SynONote` is not `Ordinal`. Exactly one theorem below mentions
  `Ordinal` at all — `mathlib_ONote_order_not_antisymm`, which is a fact about *Mathlib's* order and
  is disclosed as choice-carrying. Nothing here transports a result across the two carriers.
* **It is not a proof that ε₀ requires choice.** The obstruction proved below is about *notation
  systems of this shape* — Cantor normal form, whose terms name exactly the ordinals below ε₀. It says
  nothing about notation systems that extend past ε₀ (Veblen / Bachmann-Howard style), which are not in
  Mathlib. Whether some richer constructive substrate supports a snap nucleus is open and untouched.
* **The impossibility is not "no nucleus exists on `ONote`."** Nuclei on `SynONote` exist in
  abundance — `id` is one. What is proved impossible is the *snap property*: that a nucleus's closed
  points be ε-numbers.

## The obstruction, stated

ZP-N's `omegaPow_no_fixedpoint` proves that **no `ONote` is a fixed point of `α ↦ ω^α`**. A `Nucleus` is
by definition **idempotent**, so `j (j x) = j x` — every value in its image is one of its own closed
points, and since `ONote` is inhabited, closed points always exist. Requiring those closed points to be
ε-numbers therefore demands a fixed point of `ω^·` inside a system that provably has none.

That is `no_snap_closure` (for an arbitrary idempotent endomap, no order needed) and
`no_snap_nucleus` (the `Nucleus`-typed corollary). The two together are the answer: the failure is not
a Mathlib packaging artifact and not a missing lemma. It is that **ε₀ is exactly the ordinal Cantor
normal form cannot name** — it is the supremum of the notation system, not a member of it — so the
closure operator has nothing in the system to settle on.

The surrounding positive results make that precise rather than merely asserted:

* `cmp_lt_tower` / `tower_cofinal` — every notation is strictly below some ω-tower stage. The tower is
  **cofinal** in `ONote`.
* `tower_no_upper_bound` — consequently no notation bounds the tower. The suprema the snap-closure
  would have to land on is absent from the carrier, not merely hard to construct.

So the missing object is a *supremum of an unbounded chain*, and its absence is a theorem about the
carrier, not a limitation of the proof.

## Is the choice in `snapNucleus` accidental or structural?

Both halves are measured here, and they split:

* **The choice is still accidental in the ZP-N sense.** Every theorem in this file, including the
  impossibility itself and the full `LinearOrder`/`SemilatticeInf` structure on `SynONote`, is
  choice-free. Nothing in the *reasoning* about the snap needs choice.
* **The construction is nevertheless structurally unavailable constructively — for a different
  reason.** What blocks the counterpart is not choice but **expressive reach**: the constructive
  carrier cannot name the object the closure produces. That is a genuine obstruction, and it is the
  first one the framework has found that is not a Mathlib artifact.

These are compatible and should not be conflated. "The proof needs no choice" and "the carrier cannot
hold the answer" are different failures, and only the second one bites here.

## Does `ONote` carry a choice-free `SemilatticeInf`? (measured: yes, but not Mathlib's)

Mathlib gives `ONote` only a `Preorder` (`Mathlib/SetTheory/Ordinal/Notation.lean`), defined as
`le x y := repr x ≤ repr y` — routed through `ONote.repr` into the choice-saturated `Ordinal`. It is
also genuinely **not** a partial order: `mathlib_ONote_order_not_antisymm` below exhibits `1 + ω` and
`ω` as distinct notations with equal `repr`, so antisymmetry fails. Mathlib's order on `ONote` is
therefore unusable here on both counts, and both counts are proved rather than asserted.

A choice-free order **is** available, and is built below from the syntactic comparator `ONote.cmp`
directly. `SynONote` is a type synonym for `ONote` carrying `x ≤ y := ONote.cmp x y ≠ .gt`. The
comparator laws needed (`syn_cmp_refl`, `syn_cmp_swap`, `syn_cmp_trans_lt`) are proved here by
structural induction on the notation, never through `repr`; Mathlib's `ONote.cmp_compares` cannot be
reused because it requires the `NF` predicate, which is itself defined via `repr` and carries choice.
The result is a `LinearOrder SynONote`, hence a `SemilatticeInf`, hence `Nucleus SynONote` typechecks —
and every piece of it is `[propext]` or cleaner. That is what makes `no_snap_nucleus` a statement about
an actually-inhabitable type rather than a vacuous one.

## Triviality assessment

The impossibility itself is, as mathematics, nearly trivial: `no_snap_closure` is a two-line argument
once `omegaPow_no_fixedpoint` is in hand — an idempotent map has a closed point, ε-numbers do not
exist here, done. It should not be read as a deep theorem. Its value is entirely in *what it names*:
it converts "we tried to build the counterpart and it did not work" into "the counterpart cannot
exist, and here is the one-line reason." That is a difference in kind, not in depth.

`cmp_lt_tower` and `tower_cofinal` are elementary too — the same structural induction as
`SyntacticCollapse.le_synVal_of_tower_le`, run in the opposite direction.

The genuinely non-trivial engineering is the `LinearOrder SynONote` instance, and specifically
`syn_cmp_trans_lt`: Mathlib proves the corresponding fact only via `ONote.cmp_compares`, which
requires `NF`, which is defined through `repr` and carries choice. Getting transitivity by
lexicographic induction on raw syntax instead is what makes a choice-free `SemilatticeInf` — and
therefore the `Nucleus`-typed statement `no_snap_nucleus` — available at all. Without it, the
obstruction could only be stated for bare endomaps, and the connection to `Nucleus` would be
informal.

## Prior art

`ONote`, `ONote.cmp`, `eq_of_cmp_eq` and `linearOrderOfCompares` are Mathlib. The technique of staying
on the syntactic substrate to avoid inherited choice is ZP-N's
(`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`); `synVal` and its monotonicity are from
`ZeroParadox/Ordinal/SyntacticCollapse.lean`, reused here. Nuclei are Mathlib's `Order/Nucleus.lean`
(point-free Lawvere-Tierney). That Cantor normal form names exactly the ordinals below ε₀ is classical
proof theory, not a result of this file. The contribution is the obstruction statement and its proof on
these objects.

## Engineer's Take

TODO (Tim): if the carrier cannot name what the closure produces, is that a defect of the carrier or is
it the snap telling us where the boundary of the system actually is?
-/

namespace ZeroParadox

open ONote

/-! ### Laws of the syntactic comparator

Proved by structural induction on `ONote`. Nothing here touches `ONote.repr`, `NF`, or `Ordinal`, so
nothing inherits choice. Mathlib's `ONote.cmp_compares` proves the analogous facts but only under the
`NF` hypothesis, and `NF` is defined through `repr` — hence choice-carrying. These are the raw-syntax
replacements. -/

/-- Lexicographic decomposition of `Ordering.then` at `lt`. Both `Ordering` arguments range over a
three-element type, so this is decided outright. -/
theorem then_eq_lt_iff (o p : Ordering) :
    o.then p = Ordering.lt ↔ o = Ordering.lt ∨ (o = Ordering.eq ∧ p = Ordering.lt) := by
  cases o <;> cases p <;> decide

/-- `Ordering.swap` distributes over `Ordering.then`. -/
theorem swap_then (o p : Ordering) : (o.then p).swap = o.swap.then p.swap := by
  cases o <;> cases p <;> decide

/-- The syntactic comparator is reflexive. -/
theorem syn_cmp_refl : ∀ x : ONote, ONote.cmp x x = Ordering.eq
  | 0 => rfl
  | oadd e n a => by
      rw [ONote.cmp, syn_cmp_refl e, syn_cmp_refl a, cmp_self_eq_eq]
      rfl

/-- The syntactic comparator is antisymmetric as an orientation: swapping the arguments swaps the
`Ordering`. -/
theorem syn_cmp_swap : ∀ x y : ONote, (ONote.cmp x y).swap = ONote.cmp y x
  | 0, 0 => rfl
  | 0, oadd _ _ _ => rfl
  | oadd _ _ _, 0 => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
      rw [ONote.cmp, ONote.cmp, swap_then, swap_then, syn_cmp_swap e₁ e₂, syn_cmp_swap a₁ a₂,
        _root_.cmp_swap]

/-- `gt` in the syntactic comparator is `lt` reversed. -/
theorem syn_cmp_gt_iff_lt (x y : ONote) :
    ONote.cmp x y = Ordering.gt ↔ ONote.cmp y x = Ordering.lt := by
  constructor
  · intro h
    rw [← syn_cmp_swap x y, h]; rfl
  · intro h
    rw [← syn_cmp_swap y x, h]; rfl

/-- Transitivity of the strict syntactic order. Lexicographic induction on the notation structure. -/
theorem syn_cmp_trans_lt : ∀ (x y z : ONote),
    ONote.cmp x y = Ordering.lt → ONote.cmp y z = Ordering.lt → ONote.cmp x z = Ordering.lt
  | 0, 0, _, h₁, _ => Ordering.noConfusion h₁
  | oadd _ _ _, 0, _, h₁, _ => Ordering.noConfusion h₁
  | 0, oadd _ _ _, 0, _, h₂ => Ordering.noConfusion h₂
  | oadd _ _ _, oadd _ _ _, 0, _, h₂ => Ordering.noConfusion h₂
  | 0, oadd _ _ _, oadd _ _ _, _, _ => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, oadd e₃ n₃ a₃, h₁, h₂ => by
      rw [ONote.cmp, then_eq_lt_iff] at h₁ h₂
      rw [ONote.cmp, then_eq_lt_iff]
      rcases h₁ with he₁ | ⟨he₁, hr₁⟩ <;> rcases h₂ with he₂ | ⟨he₂, hr₂⟩
      · exact Or.inl (syn_cmp_trans_lt e₁ e₂ e₃ he₁ he₂)
      · obtain rfl := eq_of_cmp_eq he₂
        exact Or.inl he₁
      · obtain rfl := eq_of_cmp_eq he₁
        exact Or.inl he₂
      · obtain rfl := eq_of_cmp_eq he₁
        obtain rfl := eq_of_cmp_eq he₂
        refine Or.inr ⟨syn_cmp_refl _, ?_⟩
        rw [then_eq_lt_iff] at hr₁ hr₂
        rw [then_eq_lt_iff]
        rcases hr₁ with hn₁ | ⟨hn₁, ha₁⟩ <;> rcases hr₂ with hn₂ | ⟨hn₂, ha₂⟩
        · have p₁ : (n₁ : ℕ) < (n₂ : ℕ) := (cmp_eq_lt_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          have p₂ : (n₂ : ℕ) < (n₃ : ℕ) := (cmp_eq_lt_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          exact Or.inl ((cmp_eq_lt_iff (n₁ : ℕ) (n₃ : ℕ)).mpr (Nat.lt_trans p₁ p₂))
        · have hb : (n₂ : ℕ) = (n₃ : ℕ) := (cmp_eq_eq_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          refine Or.inl ?_
          rw [← hb]; exact hn₁
        · have ha : (n₁ : ℕ) = (n₂ : ℕ) := (cmp_eq_eq_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          refine Or.inl ?_
          rw [ha]; exact hn₂
        · have ha : (n₁ : ℕ) = (n₂ : ℕ) := (cmp_eq_eq_iff (n₁ : ℕ) (n₂ : ℕ)).mp hn₁
          have hb : (n₂ : ℕ) = (n₃ : ℕ) := (cmp_eq_eq_iff (n₂ : ℕ) (n₃ : ℕ)).mp hn₂
          refine Or.inr ⟨?_, syn_cmp_trans_lt a₁ a₂ a₃ ha₁ ha₂⟩
          rw [ha, hb]; exact cmp_self_eq_eq (n₃ : ℕ)

/-- Transitivity of the non-strict syntactic order. -/
theorem syn_cmp_trans_le {x y z : ONote} (h₁ : ONote.cmp x y ≠ Ordering.gt)
    (h₂ : ONote.cmp y z ≠ Ordering.gt) : ONote.cmp x z ≠ Ordering.gt := by
  cases hxy : ONote.cmp x y
  · cases hyz : ONote.cmp y z
    · rw [syn_cmp_trans_lt x y z hxy hyz]; decide
    · obtain rfl := eq_of_cmp_eq hyz
      rw [hxy]; decide
    · exact absurd hyz h₂
  · obtain rfl := eq_of_cmp_eq hxy
    exact h₂
  · exact absurd hxy h₁

/-! ### `SynONote`: the choice-free order on ordinal notations

A type synonym for `ONote` carrying the order *derived from the comparator* rather than Mathlib's
`repr`-based `Preorder`. This is what makes `Nucleus` typecheck on the notation side at all. -/

/-- `ONote` under the syntactic comparator order. A type synonym, so it does not pick up Mathlib's
`repr`-based (and therefore choice-carrying, and non-antisymmetric) `Preorder ONote`. -/
def SynONote : Type := ONote

/-- The identity map into the syntactically-ordered copy of `ONote`. -/
def toSyn (x : ONote) : SynONote := x

/-- The identity map out of the syntactically-ordered copy of `ONote`. -/
def ofSyn (x : SynONote) : ONote := x

@[simp] theorem ofSyn_toSyn (x : ONote) : ofSyn (toSyn x) = x := rfl
@[simp] theorem toSyn_ofSyn (x : SynONote) : toSyn (ofSyn x) = x := rfl

instance instPreorderSynONote : Preorder SynONote where
  le x y := ONote.cmp (ofSyn x) (ofSyn y) ≠ Ordering.gt
  lt x y := ONote.cmp (ofSyn x) (ofSyn y) = Ordering.lt
  le_refl x := by rw [syn_cmp_refl]; decide
  le_trans _ _ _ h₁ h₂ := syn_cmp_trans_le h₁ h₂
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      exact ⟨by rw [h]; decide, fun hc => hc ((syn_cmp_gt_iff_lt _ _).mpr h)⟩
    · rintro ⟨-, h2⟩
      cases hc : ONote.cmp (ofSyn y) (ofSyn x)
      · exact absurd (by rw [hc]; decide : ONote.cmp (ofSyn y) (ofSyn x) ≠ Ordering.gt) h2
      · exact absurd (by rw [hc]; decide : ONote.cmp (ofSyn y) (ofSyn x) ≠ Ordering.gt) h2
      · exact (syn_cmp_gt_iff_lt _ _).mp hc

/-- `SynONote` is linearly ordered by the syntactic comparator — choice-free, and computable. This is
the structure Mathlib's `Preorder ONote` cannot supply: that one is `repr`-based (choice) and not even
antisymmetric (distinct non-normal-form notations share a `repr`). -/
instance instLinearOrderSynONote : LinearOrder SynONote :=
  linearOrderOfCompares (fun x y => ONote.cmp (ofSyn x) (ofSyn y)) <| by
    intro a b
    show (ONote.cmp (ofSyn a) (ofSyn b)).Compares a b
    cases hc : ONote.cmp (ofSyn a) (ofSyn b)
    · exact hc
    · exact eq_of_cmp_eq hc
    · exact (syn_cmp_gt_iff_lt _ _).mp hc

/-! ### Why Mathlib's own order on `ONote` cannot be used here

Recorded separately from the constructive development above, because it is a statement *about* the
choice-carrying order rather than part of that development.

Mathlib declares `Preorder ONote` with `le x y := repr x ≤ repr y`, and declares it as a `Preorder`
and not a `PartialOrder` for a reason: antisymmetry genuinely fails, because notations that are not in
normal form can denote the same ordinal. `1 + ω` and `ω` are the smallest witness. Mathlib's positive
counterpart is `ONote.repr_inj`, and it requires `NF` on both arguments — the hypothesis this example
violates.

So Mathlib's order on `ONote` is unusable here on two independent counts: it routes through `repr`
into the choice-saturated `Ordinal`, and it is not a partial order, let alone a `SemilatticeInf`. That
is why `SynONote` above builds its order from `ONote.cmp` instead. -/

/-- **Mathlib's `repr`-based order on `ONote` is not antisymmetric.** Two distinct notations —
`1 + ω` and `ω` — denote the same ordinal, so each is `≤` the other without being equal.

This is the one theorem in the file that touches `Ordinal`, and it therefore carries
`Classical.choice`, as disclosed in the purity check. That is expected: it is a fact about the
choice-carrying structure, not a constructive result. -/
theorem mathlib_ONote_order_not_antisymm :
    ∃ x y : ONote, x ≠ y ∧ ONote.repr x = ONote.repr y := by
  refine ⟨oadd 0 1 (oadd 1 1 0), oadd 1 1 0, by decide, ?_⟩
  have h : ONote.repr (oadd (1 : ONote) 1 0) = Ordinal.omega0 := by simp
  rw [ONote.repr, h]
  simp

/-! ### The tower is cofinal: the carrier has no home for the closure

These are the positive results that make the obstruction precise. `synVal` and its monotonicity come
from `ZeroParadox/Ordinal/SyntacticCollapse.lean`. -/

/-- **Every notation is strictly below a tower stage.** If a notation's syntactic valuation is below
`m`, the notation itself is strictly `cmp`-below `tower m`. Structural induction; the leading exponent
of `tower m` strictly dominates, so coefficients never matter. -/
theorem cmp_lt_tower : ∀ (x : ONote) (m : ℕ), synVal x < m → ONote.cmp x (tower m) = Ordering.lt
  | 0, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, (_ + 1), _ => rfl
  | oadd _ _ _, 0, h => absurd h (Nat.not_lt_zero _)
  | oadd e n a, (m + 1), h => by
      have he : synVal e < m := Nat.lt_of_succ_lt_succ h
      have hrec := cmp_lt_tower e m he
      show ONote.cmp (oadd e n a) (oadd (tower m) 1 0) = Ordering.lt
      rw [ONote.cmp, hrec]
      rfl

/-- **The ω-tower is cofinal in the notations.** Every notation is strictly below some tower stage —
so the notation system is exactly "the ordinals below the tower's limit", with nothing left over
above. -/
theorem tower_cofinal (x : ONote) : ∃ n : ℕ, ONote.cmp x (tower n) = Ordering.lt :=
  ⟨synVal x + 1, cmp_lt_tower x _ (Nat.lt_succ_self _)⟩

/-- **No notation is an upper bound for the tower.** The supremum the snap-closure would have to land
on (ε₀) is absent from the carrier — this is a theorem about `ONote`, not a gap in a construction. -/
theorem tower_no_upper_bound (x : ONote) : ∃ n : ℕ, ONote.cmp (tower n) x = Ordering.gt := by
  obtain ⟨n, hn⟩ := tower_cofinal x
  exact ⟨n, (syn_cmp_gt_iff_lt _ _).mpr hn⟩

/-! ### The obstruction -/

/-- **`ω^·` moves every notation.** The equational form of ZP-N's `omegaPow_no_fixedpoint`. -/
theorem omegaPow_ne_self (x : ONote) : omegaPow x ≠ x := by
  intro h
  have := omegaPow_no_fixedpoint x
  rw [h, syn_cmp_refl] at this
  exact Ordering.noConfusion this

/-- **No idempotent endomap of `ONote` has ε-number closed points.**

This is the obstruction in its sharpest, order-free form: idempotence alone is enough. An idempotent
`j` fixes everything in its image, and `ONote` is inhabited, so `j` has at least one closed point. If
every closed point had to be a fixed point of `ω^·`, that would exhibit a fixed point of `ω^·` among
the notations — and `omegaPow_ne_self` says there is none.

Note how little is assumed: no order, no monotonicity, no meet-preservation, no inflationarity. Any
*closure operator whatsoever* on this carrier fails the snap property. -/
theorem no_snap_closure (j : ONote → ONote) (hidem : ∀ x, j (j x) = j x) :
    ¬ ∀ x : ONote, j x = x → omegaPow x = x := by
  intro h
  exact omegaPow_ne_self (j 0) (h (j 0) (hidem 0))

/-- The biconditional form: no idempotent endomap has closed points *exactly* the ε-numbers. -/
theorem no_snap_closure_iff (j : ONote → ONote) (hidem : ∀ x, j (j x) = j x) :
    ¬ ∀ x : ONote, j x = x ↔ omegaPow x = x :=
  fun h => no_snap_closure j hidem fun x hx => (h x).mp hx

/-- **No nucleus on `SynONote` has ε-number closed points.**

The `Nucleus`-typed corollary of `no_snap_closure`, on the choice-free `SemilatticeInf` built above.
This is the direct counterpart-statement for `snapNucleus`: on `Ordinal`, the snap nucleus's closed
points are exactly the ε-numbers (`snapNucleus_epsilon0`); on the constructive carrier, no nucleus can
have that property at all.

The statement is not vacuous — `Nucleus SynONote` is inhabited (`id` is a nucleus). What fails is the
snap property, not the existence of nuclei. -/
theorem no_snap_nucleus (j : Nucleus SynONote) :
    ¬ ∀ x : SynONote, j x = x → omegaPow (ofSyn x) = ofSyn x :=
  fun h => no_snap_closure (fun x => ofSyn (j (toSyn x)))
    (fun x => congrArg ofSyn
      (le_antisymm (j.idempotent' (toSyn x)) (j.le_apply' (j (toSyn x)))))
    (fun x hx => h (toSyn x) hx)

/-- `Nucleus SynONote` is inhabited, so `no_snap_nucleus` is a real constraint rather than a vacuous
quantification over an empty type. -/
def idNucleus : Nucleus SynONote where
  toFun x := x
  map_inf' _ _ := rfl
  idempotent' _ := le_refl _
  le_apply' _ := le_refl _

end ZeroParadox

/-! ## Axiom Purity Check

Target: `[propext]` or cleaner on everything, including the `LinearOrder`/`SemilatticeInf` structure.
Contrast the measured `[propext, Classical.choice, Quot.sound]` on `snapNucleus` in
`ZeroParadox/Ordinal/SnapNucleus.lean`, which is irreducible — `Classical.choice` is in the `Ordinal`
type itself, not in the proof. -/

section PurityCheck
open ZeroParadox
#print axioms then_eq_lt_iff
#print axioms swap_then
#print axioms syn_cmp_refl
#print axioms syn_cmp_swap
#print axioms syn_cmp_gt_iff_lt
#print axioms syn_cmp_trans_lt
#print axioms syn_cmp_trans_le
#print axioms instPreorderSynONote
#print axioms instLinearOrderSynONote
-- The single deliberate exception: a statement *about* Mathlib's choice-carrying `repr`-based order,
-- not part of the constructive development. Expected to report `Classical.choice`.
#print axioms mathlib_ONote_order_not_antisymm
#print axioms cmp_lt_tower
#print axioms tower_cofinal
#print axioms tower_no_upper_bound
#print axioms omegaPow_ne_self
#print axioms no_snap_closure
#print axioms no_snap_closure_iff
#print axioms no_snap_nucleus
#print axioms idNucleus
end PurityCheck
