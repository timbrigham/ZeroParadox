# Two forks that do not unify, and what Carlström proves instead

Construction, argument and prior art for `ZeroParadox/Algebra/WheelFrac.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The construction

The wheel of fractions of a commutative ring `A` with respect to a multiplicative submonoid `S`, built
to prove it is a `Wheel` (`ZeroParadox/Algebra/Wheel.lean`). This turns that file's §VIII conjecture
into a theorem.

Carlström, source-verified: `⊙_S A = (A × A) / ≡_S`, where

  `(x,y) ≡_S (x',y')  ⟺  ∃ s s' ∈ S,  s·x = s'·x'  ∧  s·y = s'·y'`,

with `0 = [0,1]`, `1 = [1,1]`, `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`, `[x,y]·[x',y'] = [x·x', y·y']`,
and `/[x,y] = [y,x]`. Then `/0 = [1,0] = ∞`, `0·/0 = [0,0] = ⊥`, with `∞ ≠ ⊥` (the wheel, not the
meadow) — matching the ZP porthole.

**Status: complete.** Fully `sorry`-free: `≡_S` is an equivalence, the five operations are well-defined
on the quotient, all 14 fields of the ZP `Wheel` typeclass hold (a faithful encoding of Carlström's
8-axiom Def 1.1, with his two commutative-monoid axioms unbundled), and `inf_ne_bot` holds given
`0 ∉ S`. Both `instWheel` and `inf_ne_bot` are `Classical.choice`-free (`[propext, Quot.sound]`).

## The involutive fork, and why it does NOT unify with the ordered μ/ν fork

`fixed_pole_forces_collapse` is the witness for the involutive-fork-with-a-fixed-pole row of the wall
taxonomy: **if the involution fixes the pole, the two poles coincide.**

The two forks are **different species**:

* the **ordered** μ/ν fork (`fork_collapse_iff`, `ZeroParadox/Settheory/FixedPointFork.lean`) has poles
  that are FIXED POINTS of a monotone map;
* an **involutive** fork has poles forming a 2-CYCLE of an involution — swapped, and *not* fixed when
  the fork is open.

Imposing the ordered condition on an involutive fork therefore FORCES collapse: they coincide only at
the diagonal point. That much is the theorem.

**Block conclusion (2026-06-25) — a reasoned judgement, NOT a theorem, and there is no witness for it.**
The only data common to both is "a self-map plus two elements" with no shared non-trivial axiom, so no
single non-vacuous lightweight typeclass over both forks was located as of 2026-08-02. **The underlying
judgement is a universal negative** — it quantifies over all possible typeclasses — which is why it is
bounded to a dated search rather than asserted. Nothing in Lean states it, and
`fixed_pole_forces_collapse` does **not**: it proves the narrow implication in its own signature.
Unifying the two forks would need the categorical machinery (both are ℤ/2ℤ actions, but `op` acts on the
CATEGORY, dualizing μ↔ν, while inversion acts on the ELEMENT set, swapping 0↔∞); that stays the horizon.

## Prior art — Carlström § 4 proves MORE

The specific result is **Prop. 4.4** (`.claude-local/papers/carlstrom_wheels_2001_11.pdf`, p. 27):
*"If any two of the elements 0, 1, /0 and 0/0 are equal in a wheel H, then H is trivial."*

**State the relation precisely.** The two share an **antecedent** and have **different consequents**. At
`wheelFork` the pole is `pole₁ = winv wzero`, so `fixed_pole_forces_collapse`'s hypothesis and
conclusion are the same equation up to `Eq.symm` — it says the poles coincide, which at that instance is
nearly tautological. Carlström takes the same antecedent to a substantive conclusion: **the entire wheel
degenerates.** So this is not a weaker form of one implication; it is a different, and much smaller,
statement off a shared hypothesis. Do not present the collapse as a framework finding.

His remark that *"0 can't be inverted unless 0 ∈ S, but if that is the case … S⊙A is trivial"* (PDF
p. 6, printed p. 4) motivates `wheelFrac_fork_open`'s `0 ∉ S` hypothesis. Two points on that quotation:
it is stated there of the *ordinary* ring of fractions `A×S/≈_S`, with the corresponding **wheel**
statement a separate sentence on printed p. 5; and Carlström writes the wheel of fractions **`S⊙A`**,
not `A⊙S`. The substance — `0 ∈ S` trivializes, so exclude it — is his.

## Standard names for what is written by hand

Trigger 0: adopt the framing, keep the handle. `Collapsed F` is equivalent to
`Function.IsFixedPt F.dual F.pole₀` (`Mathlib/Logic/Function/Defs.lean`) — **equivalent via `swap` and
`eq_comm`, not definitionally equal**, so do not write "is". Note also that `pole₁` is **redundant
data**, pinned by `swap` to `dual pole₀`; it is retained because the two-pole presentation is what the
framework's prose refers to.

⚠ **`collapsed_iff_fixed` is not an instance of `Function.Involutive.eq_iff`.** `eq_iff` reads
`f x = y ↔ x = f y`, which instantiates to `dual pole₀ = pole₁ ↔ pole₀ = dual pole₁` — a different
statement. The proof is `rw [F.swap]; exact eq_comm`, and **involutivity is never used**: delete
`dual_invol` from the hypothesis and it still compiles.

In the wider literature the fixed point of an involution is **the center** (a *centered* Kleene
algebra), and the standard fix for the monotone/involutive clash is an order-**reversing** involution
(De Morgan negation, orthocomplementation) — a sharper diagnosis than "no shared axiom", and the
direction to look if this is ever revisited. **Attribution, stated honestly:** this lineage is taken
from San Martín, *Kleene algebras with implication* (slides, UNLP/CONICET, September 2016, slide 2),
which is the source actually read; **the deck** credits Kalman 1958 (slide 3) and Cignoli 1986
(slide 5), **neither of which has been opened here**. Cite San Martín for the lineage, or read the
originals before citing them directly. Searched 2026-08-02: no prior art located for the bare
`InvolutiveFork` abstraction standing alone, nor for the μ/ν-versus-2-cycle contrast.

## Unstated adjacency — four in-corpus instances, none wired up

`rInv_involutive` + `rInv_swaps` (`ZeroParadox/Valuation/RiemannSphere.lean`) is the Riemann fork the
`InvolutiveFork` docstring calls "the motivating instance" and is never actually instantiated; also
`flipPoles_involutive`, `codeDataSwap_involutive`, and two `swap_involutive`. Wiring them is a pointer
exercise, not new declarations.
