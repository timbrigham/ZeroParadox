# Two forks that do not unify, and what Carlström proves instead

Construction, argument and prior art for `ZeroParadox/Algebra/WheelFrac.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The construction

The wheel of fractions of a commutative ring `A` with respect to a multiplicative submonoid `S`, built
to prove it is a `Wheel` (`ZeroParadox/Algebra/Wheel.lean`). `instWheel` proves the part of that
file's conjecture that starts from ring structure: for every commutative ring and submonoid, the wheel
axioms hold. Ring structure is an input, not derived; `ZeroParadox/Algebra/Wheel.lean` § VIII, a
documentation anchor with no theorem object, records what stays open.

Carlström, source-verified: `⊙_S A = (A × A) / ≡_S`, where

  `(x,y) ≡_S (x',y')  ⟺  ∃ s s' ∈ S,  s·x = s'·x'  ∧  s·y = s'·y'`,

with `0 = [0,1]`, `1 = [1,1]`, `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`, `[x,y]·[x',y'] = [x·x', y·y']`,
and `/[x,y] = [y,x]`. Then `/0 = [1,0] = ∞`, `0·/0 = [0,0] = ⊥`, with `∞ ≠ ⊥` (the wheel, not the
meadow) — matching the ZP porthole (the shorthand defined in
`ZeroParadox/Algebra/Wheel.lean`'s Formal Overview).

**Status: complete.** Fully `sorry`-free: `≡_S` is an equivalence, the five operations are well-defined
on the quotient, every axiom of the ZP `Wheel` typeclass holds (a faithful encoding of Carlström's
8-axiom Def 1.1, with his two commutative-monoid axioms unbundled), and `inf_ne_bot` holds given
`0 ∉ S`. Both `instWheel` and `inf_ne_bot` are `Classical.choice`-free (`[propext, Quot.sound]`).

## The involutive fork, and why it does NOT unify with the ordered μ/ν fork

`fixed_pole_forces_collapse` is the witness for the involutive-fork-with-a-fixed-pole row of the wall
taxonomy (`ZeroParadox/Settheory/Wall.md`, the failure-mode table): **if the involution fixes the pole,
the two poles coincide.**

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

Locators below are to J. Carlström, *Wheels — On Division by Zero*, Research Reports in Mathematics
No. 11, Department of Mathematics, Stockholm University, 2001 (cited here as Carlström 2001:11). The
later journal version, *Mathematical Structures in Computer Science* 14(1):143–184, 2004, paginates
differently, and these locators do not apply to it.

The specific result is **Prop. 4.4** (Carlström 2001:11, PDF p. 27, printed p. 25):
*"If any two of the elements 0, 1, /0 and 0/0 are equal in a wheel H, then H is trivial."*

**State the relation precisely.** The two share an **antecedent** and have **different consequents**. At
`wheelFork` the pole is `pole₁ = winv wzero`, so `fixed_pole_forces_collapse`'s hypothesis and
conclusion are the same equation up to `Eq.symm` — it says the poles coincide, which at that instance is
nearly tautological. Carlström takes the same antecedent to a substantive conclusion: **the entire wheel
degenerates.** So this is not a weaker form of one implication; it is a different, and much smaller,
statement off a shared hypothesis. Do not present the collapse as a framework finding.

His remark that *"Clearly, 0 can't be inverted unless 0 ∈ S, but if that is the case, then ∼_S is the
improper relation, so that `A × S/ ∼_S` is trivial"* (PDF p. 6, printed p. 4) motivates
`wheelFrac_fork_open`'s `0 ∉ S` hypothesis. Two points on that quotation. It is stated there of the
*ordinary* ring of fractions `A × S/∼_S` — the object named inside the quote — with the corresponding
**wheel** statement a separate sentence (PDF p. 7, printed p. 5): *"unless 0 ∈ S, but then ≡_S is
improper and `⊙_S A` is trivial"* — where what is improper is again a RELATION, the wheel congruence
`≡_S` on `A × A`, not the submonoid `S`. And the wheel of fractions is Carlström's **`⊙_S A`**: a PREFIX
operator with the submonoid SUBSCRIPTED, as in his `⊙_∅(ℤ/2ℤ)` and `⊙_{S₀}A`, which is the form this
corpus uses. The substance — `0 ∈ S` trivializes, so exclude it — is his.

⚠ **The construction's lineage runs through Setzer.** Carlström credits him for the name and the
construction at printed p. 3 and presents his own paper as a generalisation from integral domains to any
commutative semiring — so "Carlström's" here means that general form. This file formalizes the
commutative-ring case (`[CommRing A]` in `ZeroParadox/Algebra/WheelFrac.lean`), a special case of his semiring
generality. The quotations and the full credit chain are in `ZeroParadox/Algebra/Wheel.lean`
§ "Lineage" (the `Wheel` class docstring).

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

## The collapsed side, and why it needed an inhabitant (2026-09-13)

Until this date `InvolutiveFork` had a witness for exactly one of its two states. `wheelFork_not_collapsed`
inhabits the OPEN side; nothing inhabited the COLLAPSED one, so `fixed_pole_forces_collapse` had **no
witness for its own hypothesis** and could have been true vacuously for all the corpus showed. The
project's rule is to build a witness on both sides; the gap survived because the open side's docstring
defends non-vacuity convincingly and one pole reads as enough.

Mathlib supplies the missing one and no construction is needed. `inv_zero` — the junk-value convention
`(0 : G)⁻¹ = 0` on any `GroupWithZero` — **is** the fixed-pole condition, and `inv_inv` is the involution
law. So the example takes `dual := Inv.inv`, `pole₀ := 0`, and discharges `Collapsed` by `inv_zero`.

⚠ **`dual` and `pole₀` are pinned in the statement**, mirroring `Wheel.lean`'s `gauge_strong`. The bare
`∃ F, F.Collapsed` is satisfied on any inhabited type by the identity involution at a single point, so it
would witness nothing. Pinning is what makes the existential say something about *inversion* rather
than about *forks*.

**The reading.** This is what totalising division looks like when you adjoin nothing: the reciprocal of
zero lands on the zero already there, so the fork's two ends are the same point and there is no distinct
infinity. Bergstra, Hirshfeld & Tucker (arXiv:0901.0823, abstract) define a meadow as *"a commutative ring
with a total inverse operator satisfying two equations which imply `0⁻¹ = 0`"* and record that *"all fields
and products of fields can be viewed as meadows"* — so the convention Mathlib already uses is that
literature's, and the contrast needs no meadow to be built.

The wheel takes the other branch: it adjoins `∞` and `⊥`, keeps them distinct, and pays for it in
distributivity. `ZeroParadox/Algebra/Wheel.lean` § V carries both directions of why no carrier takes both
deals — the forward leg (identifying `∞` with `⊥` forces triviality) and the reverse (the meadow equation
`/0 = 0` forces triviality), each with controls showing the hypotheses are load-bearing on `ZPWheelElem`.

⚠ **Not a claim that a meadow is a collapsed wheel.** A wheel with `/0 = 0` is trivial (the reverse-leg
`example` in `ZeroParadox/Algebra/Wheel.lean` § V, Carlström's Prop. 4.4), so a meadow with more than
one element is never one; the one-element carrier is both, and that § V states the overlap. The shared
object is
the `InvolutiveFork` abstraction, which both instantiate with opposite verdicts. Bergstra and Ponse
(1406.6878, § 4 "Concluding Remarks", printed p. 14) write that *"we have not yet found a structural connection"* between wheels and **common** meadows — their
own first-person hedge, not a settled negative. Common meadows are non-involutive, with `0⁻¹` a
separate error element, so they are a different pair from the involutive meadow (`0⁻¹ = 0`,
BHT 0901.0823) this paragraph is built on. Common meadows are not the only non-involutive kind:
Bergstra & Middelburg (arXiv:1406.2092, p. 2) study "one-based non-involutive meadows", where the
inverse of zero is one, an element already present, so involutivity alone does not single out common
meadows. Nothing here supplies a connection on either pair.

## Unstated adjacency — involution declarations not wired up as of 2026-09-25

`rInv_involutive` + `rInv_swaps` (`ZeroParadox/Valuation/RiemannSphere.lean`) is the Riemann fork the
`InvolutiveFork` docstring calls "the motivating instance"; also `flipPoles_involutive`
(`ZeroParadox/Computability/Occurrence.lean` — stated pointwise rather than as `Function.Involutive`),
`codeDataSwap_involutive` (`ZeroParadox/Computability/CodeDataFrameChange.lean`), and `swap_involutive`
at two sites (`ZeroParadox/Valuation/PoleCorners.lean`, `ZeroParadox/Miniature.lean`). Searched
2026-09-25 over `ZeroParadox/**/*.lean` and the tracked `.md`: the only `InvolutiveFork` instances
located are `wheelFork` and the `GroupWithZero` example, both in `ZeroParadox/Algebra/WheelFrac.lean`,
so none of these is wired up. **Not a closed list of the corpus's involutions** — the same sweep for
`Function.Involutive` also returns `σ_involutive`
(`ZeroParadox/Computability/MarkovNuUniversal.lean`), an involution but not a pole exchange. Wiring any
of them is a pointer exercise, not new declarations. Since that search,
`ZeroParadox/Algebra/WheelFrac.lean` has also gained the identity-fork `example` after
`wheelFork_not_collapsed`: a generic witness on any inhabited type, and not one of the declarations
listed here.
