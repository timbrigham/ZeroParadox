import ZeroParadox.Algebra.Wheel
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic

/-!
# The Wheel of Fractions `⊙_S A` (Carlström 2001:11, pp. 4-5, 10)

## Engineer's Take

A ZP-J wheel sub-file. See the Engineer's Take in `ZeroParadox/Algebra/Wheel.lean`.

---

Constructs the wheel of fractions of a commutative ring `A` with respect to a multiplicative
submonoid `S`, with the goal of proving it is a `Wheel` (from `ZeroParadox/Algebra/Wheel.lean`). This turns the
§VIII conjecture of `ZeroParadox/Algebra/Wheel.lean` into a theorem.

Construction (Carlström, source-verified): `⊙_S A = (A × A) / ≡_S`, where

  `(x,y) ≡_S (x',y')  ⟺  ∃ s s' ∈ S,  s·x = s'·x'  ∧  s·y = s'·y'`,

with `0 = [0,1]`, `1 = [1,1]`, `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`, `[x,y]·[x',y'] = [x·x', y·y']`,
and `/[x,y] = [y,x]`. Then `/0 = [1,0] = ∞`, `0·/0 = [0,0] = ⊥`, with `∞ ≠ ⊥` (the wheel, not the
meadow) — matching the ZP porthole.

**Status: complete.** Fully `sorry`-free: `≡_S` is an equivalence, the five operations are
well-defined on the quotient, all 14 fields of the ZP `Wheel` typeclass hold (a faithful encoding
of Carlström's 8-axiom Def 1.1, with his two commutative-monoid axioms unbundled), and `inf_ne_bot`
holds given `0 ∉ S`.
Both `instWheel` and `inf_ne_bot` are `Classical.choice`-free (`[propext, Quot.sound]`).
-/

namespace ZeroParadox

open ZeroParadox

set_option maxHeartbeats 400000

variable {A : Type*} [CommRing A] (S : Submonoid A)

/-- The wheel-of-fractions relation `≡_S` on `A × A`. -/
def rel (p q : A × A) : Prop :=
  ∃ s ∈ S, ∃ s' ∈ S, s * p.1 = s' * q.1 ∧ s * p.2 = s' * q.2

/-- `≡_S` is an equivalence relation (Carlström p.10; refl uses `1 ∈ S`, trans uses closure of `S`). -/
def srel : Setoid (A × A) where
  r := rel S
  iseqv := {
    refl := fun p => ⟨1, S.one_mem, 1, S.one_mem, rfl, rfl⟩
    symm := fun ⟨s, hs, s', hs', h1, h2⟩ => ⟨s', hs', s, hs, h1.symm, h2.symm⟩
    trans := fun ⟨s, hs, s', hs', a1, a2⟩ ⟨t, ht, t', ht', b1, b2⟩ =>
      ⟨t * s, S.mul_mem ht hs, t' * s', S.mul_mem ht' hs',
        by linear_combination t * a1 + s' * b1,
        by linear_combination t * a2 + s' * b2⟩
  }

/-- The wheel of fractions `⊙_S A = (A × A) / ≡_S`. -/
abbrev WheelFrac := Quotient (srel S)

/-- Class of a pair `[x, y]`. -/
def mk (p : A × A) : WheelFrac S := Quotient.mk (srel S) p

/-- Addition: `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`. -/
def waddF : WheelFrac S → WheelFrac S → WheelFrac S :=
  Quotient.lift₂ (fun p q => mk S (p.1 * q.2 + q.1 * p.2, p.2 * q.2)) (by
    rintro p q p' q' ⟨s, hs, s', hs', hp1, hp2⟩ ⟨t, ht, t', ht', hq1, hq2⟩
    refine Quotient.sound ⟨s * t, S.mul_mem hs ht, s' * t', S.mul_mem hs' ht', ?_, ?_⟩
    · calc (s * t) * (p.1 * q.2 + q.1 * p.2)
          = (s * p.1) * (t * q.2) + (t * q.1) * (s * p.2) := by ring
        _ = (s' * p'.1) * (t' * q'.2) + (t' * q'.1) * (s' * p'.2) := by rw [hp1, hp2, hq1, hq2]
        _ = (s' * t') * (p'.1 * q'.2 + q'.1 * p'.2) := by ring
    · calc (s * t) * (p.2 * q.2) = (s * p.2) * (t * q.2) := by ring
        _ = (s' * p'.2) * (t' * q'.2) := by rw [hp2, hq2]
        _ = (s' * t') * (p'.2 * q'.2) := by ring)

/-- Multiplication: `[x,y]·[x',y'] = [x·x', y·y']`. -/
def wmulF : WheelFrac S → WheelFrac S → WheelFrac S :=
  Quotient.lift₂ (fun p q => mk S (p.1 * q.1, p.2 * q.2)) (by
    rintro p q p' q' ⟨s, hs, s', hs', hp1, hp2⟩ ⟨t, ht, t', ht', hq1, hq2⟩
    refine Quotient.sound ⟨s * t, S.mul_mem hs ht, s' * t', S.mul_mem hs' ht', ?_, ?_⟩
    · calc (s * t) * (p.1 * q.1) = (s * p.1) * (t * q.1) := by ring
        _ = (s' * p'.1) * (t' * q'.1) := by rw [hp1, hq1]
        _ = (s' * t') * (p'.1 * q'.1) := by ring
    · calc (s * t) * (p.2 * q.2) = (s * p.2) * (t * q.2) := by ring
        _ = (s' * p'.2) * (t' * q'.2) := by rw [hp2, hq2]
        _ = (s' * t') * (p'.2 * q'.2) := by ring)

/-- Reciprocal / involution: `/[x,y] = [y,x]`. -/
def winvF : WheelFrac S → WheelFrac S :=
  Quotient.lift (fun p => mk S (p.2, p.1)) (by
    rintro p p' ⟨s, hs, s', hs', hp1, hp2⟩
    exact Quotient.sound ⟨s, hs, s', hs', hp2, hp1⟩)

/-- **Main result:** `⊙_S A` is a wheel (Carlström 2001:11, Def 1.1, pp. 4-5). All 14 fields of the
    ZP `Wheel` typeclass proved (Carlström's eight axioms, two commutative-monoid axioms unbundled). -/
instance instWheel : Wheel (WheelFrac S) where
  wadd := waddF S
  wmul := wmulF S
  winv := winvF S
  wzero := mk S (0, 1)
  wone := mk S (1, 1)
  wadd_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zero := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_one := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  winv_winv := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => rfl  -- `/(/[x,y]) = [x,y]` holds definitionally (swap twice)
  winv_wmul := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => rfl  -- `/(x·y) = /x · /y` holds definitionally (both reduce to `[bd, ac]`)
  weak_distrib := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wheel_id := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wzero_mul_wzero := by
    apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zeromul_mul := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  winv_add_zeromul := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zeroinv_absorb := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring

/-- Porthole: in `⊙_S A`, the infinity element `/0` and the bottom `0·/0` are distinct — the wheel
    (not meadow) behaviour, matching the ZP porthole `∞ ≠ ⊥`. -/
theorem inf_ne_bot (h0 : (0 : A) ∉ S) : wheelInf (W := WheelFrac S) ≠ wheelBot := by
  intro h
  obtain ⟨s, hs, s', hs', e1, _⟩ := Quotient.exact h
  have hs0 : s = 0 := by simpa using e1
  exact h0 (hs0 ▸ hs)

/-! ## § The involutive fork, and why it does NOT unify with the ordered μ/ν fork

**Promoted to a tracked file 2026-08-02.** These declarations lived only on the local-only branch
`private/physics-bridge`, while `ZeroParadox/Settheory/Wall.lean`'s NO-GO table cited
`fixed_pole_forces_collapse` as a witness — a citation no reader of the public repository could check.
The mathematics is unchanged from the original; only the namespace is (it is flat here).

The two forks are **different species**, and this section is the obstruction that says so:
* the **ordered** μ/ν fork (`fork_collapse_iff`, `ZeroParadox/Settheory/FixedPointFork.lean`) has poles
  that are FIXED POINTS of a monotone map;
* an **involutive** fork has poles forming a 2-CYCLE of an involution — swapped, and *not* fixed when
  the fork is open.
Imposing the ordered condition on an involutive fork therefore FORCES collapse: they coincide only at
the diagonal point. That much is the theorem below.

**Block conclusion (2026-06-25) — a reasoned judgement, NOT a theorem, and there is no witness for
it.** The only data common to both is "a self-map plus two elements" with no shared non-trivial
axiom, so a single non-vacuous lightweight typeclass over both forks appears not to exist. This is a
universal negative over all possible typeclasses; nothing in Lean states it, and
`fixed_pole_forces_collapse` does **not** — it proves the narrow implication in its own signature.
*(The label was dropped when this § was promoted on 2026-08-02, and `Wall.lean`'s NO-GO table
consequently carried the universal negative as an axiom-free machine-checked witness. Restored, and
the table row corrected, by the adversary gate the same day.)* Unifying them would need the
categorical machinery (both are ℤ/2ℤ actions, but `op` acts on the CATEGORY, dualizing μ↔ν, while
inversion acts on the ELEMENT set, swapping 0↔∞); that stays the horizon.

**Prior art — Carlström 2001 § 4 is closer than this § originally said, and proves MORE.** The
header already cites Carlström for the wheel axioms; the specific result is **Prop. 4.4**
(`.claude-local/papers/carlstrom_wheels_2001_11.pdf`, p. 27): *"If any two of the elements 0, 1, /0
and 0/0 are equal in a wheel H, then H is trivial."*

**State the relation precisely — "the case `0 = /0` IS `fixed_pole_forces_collapse`" was too strong,
and is corrected here.** The two share an **antecedent** and have **different consequents**. At
`wheelFork` the pole is `pole₁ = winv wzero`, so this theorem's hypothesis and conclusion are the
same equation up to `Eq.symm` — it says the poles coincide, which at that instance is nearly
tautological. Carlström takes the same antecedent to a substantive conclusion: **the entire wheel
degenerates.** So this is not a weaker form of one implication; it is a different, and much smaller,
statement off a shared hypothesis. Do not present the collapse as a framework finding.

His remark that *"0 can't be inverted unless 0 ∈ S, but if that is the case … S⊙A is trivial"*
(PDF p. 6, printed p. 4) motivates `wheelFrac_fork_open`'s `0 ∉ S` hypothesis. **Two cautions on that
quotation**, both corrected 2026-08-02: it is stated there of the *ordinary* ring of fractions
`A×S/≈_S`, with the corresponding **wheel** statement a separate sentence on printed p. 5; and
Carlström writes the wheel of fractions **`S⊙A`**, not `A⊙S`. The substance — `0 ∈ S` trivializes, so
exclude it — is his and is correctly transcribed; the placement and the notation were not.

**Standard names for what is written by hand here** (Trigger 0 — adopt the framing, keep the handle).
`Collapsed F` is equivalent to `Function.IsFixedPt F.dual F.pole₀` (defined at
`Mathlib/Logic/Function/Defs.lean`) — **equivalent via `swap` and `eq_comm`, not definitionally
equal**, so do not write "is". Note also that `pole₁` is **redundant data**, pinned by `swap` to
`dual pole₀`; it is retained because the two-pole presentation is what the framework's prose refers
to.

**⚠ `collapsed_iff_fixed` is NOT an instance of `Function.Involutive.eq_iff` — that claim stood here
and is retracted.** `eq_iff` reads `f x = y ↔ x = f y`, which instantiates to
`dual pole₀ = pole₁ ↔ pole₀ = dual pole₁` — a different statement. The actual proof is
`rw [F.swap]; exact eq_comm`, and **involutivity is never used**: delete `dual_invol` from the
hypothesis and it still compiles. The theorem's own docstring below already said this correctly, four
lines from the false claim — the sibling-failure pattern, where an appended correction leaves the
wrong sentence standing nearby.

In the wider literature the fixed point of an involution is **the center** (a *centered* Kleene
algebra), and the standard fix for the monotone/involutive clash is an order-**reversing** involution
(De Morgan negation, orthocomplementation) — a sharper diagnosis than "no shared axiom", and the
direction to look if this is ever revisited. **Attribution, stated honestly:** this lineage is taken
from San Martín, *Kleene algebras* (UNLP 2016, p. 2), which is the source actually read; it credits
Kalman 1958 and Cignoli 1986, **neither of which has been opened here**. Cite San Martín for the
lineage, or read the originals before citing them directly. Searched 2026-08-02: no prior art located
for the bare `InvolutiveFork` abstraction standing alone, nor for the μ/ν-versus-2-cycle contrast.

**Unstated adjacency — this abstraction already has at least four instances in-corpus, none wired
up.** `rInv_involutive` + `rInv_swaps` (`ZeroParadox/Valuation/RiemannSphere.lean`) is the Riemann
fork the docstring below calls "the motivating instance" and is never actually instantiated; also
`flipPoles_involutive`, `codeDataSwap_involutive`, and two `swap_involutive`. Wiring them is a
pointer exercise, not new declarations. -/

/-- An **involutive fork**: an involution `dual` together with two poles it swaps. The wheel / Riemann
    fork (`z ↦ 1/z` swapping `0 ↔ ∞`) is the motivating instance.

    ⚠ **Name collision — "fork" now carries three unrelated senses.** Mathlib's
    `CategoryTheory.Limits.Fork` is an equalizer diagram; the framework's own μ/ν *fixed-point* fork
    (`ZeroParadox/Settheory/FixedPointFork.lean`) is a third. Nothing here is an instance of either.
    The full name `InvolutiveFork` is load-bearing — do not shorten it to `Fork` at any use site, and
    read "the categorical machinery" in the § above as *categorical* in the loose sense, not as a
    reference to `Limits.Fork`. -/
structure InvolutiveFork (α : Type*) where
  dual : α → α
  dual_invol : Function.Involutive dual
  pole₀ : α
  pole₁ : α
  swap : dual pole₀ = pole₁

namespace InvolutiveFork

variable {α : Type*} (F : InvolutiveFork α)

/-- The fork is **collapsed** when its two poles coincide (the diagonal point). -/
def Collapsed : Prop := F.pole₀ = F.pole₁

/-- **Collapse criterion.** The poles coincide iff `pole₀` is a fixed point of the involution.
    Parallel to the ordered fork's `fork_collapse_iff` — but honestly shallower: this proof is
    `eq_comm` after the swap, where the ordered collapse is Knaster–Tarski-deep. -/
theorem collapsed_iff_fixed : F.Collapsed ↔ F.dual F.pole₀ = F.pole₀ := by
  unfold Collapsed
  rw [F.swap]
  exact eq_comm

end InvolutiveFork

/-- **The wheel is an involutive fork.** `Statement:` **INVERSION** — the involution `winv`
    (`z ↦ 1/z`) *exchanges* the poles `0` and `∞ = /0` (`wheelInf`), and is an involution. Both halves
    are in the definition below: `swap := rfl` gives `winv wzero = wheelInf`, and `dual_invol` is
    `Wheel.winv_winv` (W7). This is the 0↔∞ exchange, not a coincidence of two readings at one
    object — contrast `epsilon0_min_eq_max`. Reuses the ZP-custom `Wheel` class plus native
    `Function.Involutive`. -/
def wheelFork (W : Type*) [Wheel W] : InvolutiveFork W where
  dual := Wheel.winv
  dual_invol := Wheel.winv_winv
  pole₀ := Wheel.wzero
  pole₁ := wheelInf
  swap := rfl

/-- In the wheel of fractions the fork poles `0` and `∞` are distinct, given `0 ∉ S` — the same
    hypothesis as `inf_ne_bot`, but for the `{0, ∞}` involution 2-cycle (`inf_ne_bot` is the
    *different* `{∞, ⊥}` pair). Choice-free, mirroring `inf_ne_bot`'s proof. -/
theorem wheelFrac_fork_open (h0 : (0 : A) ∉ S) :
    (Wheel.wzero : WheelFrac S) ≠ (wheelInf : WheelFrac S) := by
  intro h
  obtain ⟨s, hs, s', hs', e1, _⟩ := Quotient.exact h
  have hs'0 : s' = 0 := by simpa using e1.symm
  exact h0 (hs'0 ▸ hs')

/-- Restated through the abstraction: the wheel-of-fractions `InvolutiveFork` is NOT collapsed. So
    `InvolutiveFork` is a non-vacuous abstraction with a concrete, provably-open, choice-free
    instance — it is not a gauge that everything satisfies. -/
theorem wheelFork_not_collapsed (h0 : (0 : A) ∉ S) :
    ¬ (wheelFork (WheelFrac S)).Collapsed :=
  wheelFrac_fork_open S h0

/-- **The obstruction, Lean-witnessed.** An involutive fork whose pole is a FIXED point of the
    involution — the ordered-fork condition — is necessarily COLLAPSED. Hence the involutive and
    ordered forks coincide only at the diagonal point: they are different species. This is the witness
    `ZeroParadox/Settheory/Wall.lean`'s NO-GO table cites, in the row whose condition-set is *an
    involutive fork whose pole is fixed by the involution*. **That row previously read "lightweight
    categorical typeclass / NO NON-VACUOUS UNIFIER" — a universal negative this theorem does not
    prove**; it was corrected 2026-08-02 to state this signature. -/
theorem fixed_pole_forces_collapse {α : Type*} (F : InvolutiveFork α)
    (h : F.dual F.pole₀ = F.pole₀) : F.Collapsed :=
  F.collapsed_iff_fixed.mpr h

/-! ## Purity check -/

section PurityCheck
#print axioms instWheel
#print axioms inf_ne_bot
#print axioms InvolutiveFork.collapsed_iff_fixed
#print axioms wheelFrac_fork_open
#print axioms wheelFork_not_collapsed
#print axioms fixed_pole_forces_collapse
end PurityCheck

end ZeroParadox
