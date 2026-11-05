# Prior art for the sphere's group action, the loxodromic vocabulary, and the stabiliser fence

Long-form prior art and fences for `ZeroParadox/Valuation/RiemannSphere.lean`. Written 2026-09-04,
in response to a prior-art gate that found §§ V–VI restating Mathlib. Everything below was
elaborated, not recalled.

## § V is an INSTANTIATION of Mathlib, not an extension of it

`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean` (Kjos-Hanssen and Nash, 2024)
defines `OnePoint.equivProjectivization : OnePoint K ≃ ℙ K (K × K)` and, on top of it,

```
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K)
```

— the fractional-linear (Möbius) action, together with `smul_infty_eq_ite`, `smul_some_eq_ite` and
`smul_infty_eq_self_iff`. `Sphere` is `abbrev Sphere := OnePoint ℚ_[2]`, so it **is** the carrier
that instance acts on. There is no delta at the level of the group action.

The two anonymous `example`s at the end of § V are the identification, and they elaborate:

- `rScale n` is the action of the diagonal matrix `diag(2 ^ n, 1)`;
- `rInv` is the action of the Weyl element `!![0, 1; 1, 0]`, including the `0 ↦ ∞` branch that
  Mathlib's field inversion cannot supply (there `0⁻¹ = 0`);
- `rScale_add` is therefore `mul_smul` transported along that identification.

They are `example`s deliberately: an anonymous declaration owes no `#print axioms` entry and no
`ssot.json` row, and it stops compiling if the identification ever fails. That makes the prior-art
claim checkable rather than asserted, which is the whole point of stating it here.

## The topology: prior art, and what this file adds

That file's own TODO, at line 20, reads:

> Add the extension of this equivalence to a homeomorphism in the case `K = ℝ`, where `OnePoint ℝ`
> gets the topology of one-point compactification.

The equivalence it names is `equivProjectivization : OnePoint K ≃ ℙ K (K × K)`, so the TODO asks for a
topology on the projectivization and a homeomorphism to it. It does not ask for the inversion map, and
`onePointInvHomeo` does not fill it: that is a self-homeomorphism of `OnePoint K`.

Continuity of inversion on the one-point compactification of a proper normed field is a standard fact,
with prior art:

- **Mathlib at the pin:** not located as of 2026-11-05, searched as follows: the § 0 search record in
  `RiemannSphere.lean` (2026-11-04), and, on 2026-11-05, `infer_instance` and `exact?` on
  `ContinuousConstSMul (GL (Fin 2) ℝ) (OnePoint ℝ)`, both failing.
- **TauCeti** (github.com/TauCetiProject/TauCeti, commit 1e5cb7e8, 2026-10-23) formalized it
  independently: `OnePoint.invChart`, for proper nontrivially normed fields, and
  `OnePoint.instContinuousConstSMul : ContinuousConstSMul (GL (Fin 2) 𝕜) (OnePoint 𝕜)`, which makes
  every Möbius map a homeomorphism and so also covers the scaling maps (`rScaleHomeo`,
  `continuous_rScale`) and the inversions (`onePointInvHomeo`, `rInvHomeo`). Source read by the
  2026-11-05 prior-art gate; not elaborated here, being outside this project's dependency closure.
- **Algebraically**, `onePointInv` is the swap-matrix case `!![0, 1; 1, 0]` of Mathlib's
  `OnePoint.instGLAction`; the `example`s closing § V state this for `rInv`.
- **Informal source:** Forster, *Lectures on Riemann Surfaces* (GTM 81), §§ 1–2, as cited by TauCeti;
  not retrieved.

What this file adds is narrower: an elementary proof inside Mathlib alone, with no manifold structure,
under `[NormedField K] [ProperSpace K]` (`continuous_onePointInv`, `onePointInvHomeo`); the ℚ₂
application (`continuous_rInv`, `rInvHomeo` on `Sphere`); and the ℝ-against-ℚ₂ comparison
(`continuous_onePointInv_real`, `onePointInv_swaps_real`, and the `Reading: CARRIER` control after
them: the pole exchange holds in both carriers, and total disconnectedness separates them). The proof's
work is at the two special points: as `x → 0` the image leaves every compact set, which needs
`ProperSpace K` and `Metric.cobounded_eq_cocompact`.

## The pole stabiliser is much bigger than the scalings

`rScale_fixes_poles` says every `rScale n` fixes `0` and `∞` pointwise. It is tempting — and wrong —
to read that backwards, as though the scalings were *the* pole-fixing maps.

The pointwise stabiliser of `{0, ∞}` in the fractional-linear action is the full diagonal torus: every
`x ↦ u · x` with `u ≠ 0` fixes both, and that is an uncountable group. `rScale` is the image of
`n ↦ 2 ^ n`, an infinite cyclic subgroup isomorphic to `ℤ`. `stabiliser_is_bigger` is the NO-GO gauge
for exactly this misreading, stated over an arbitrary nonzero multiplier rather than one witness.

⚠ Relatedly, an earlier draft attributed `rScale_add` to "the diagonal subgroup is one-parameter".

`Statement:` `rScale_add` is `2 ^ (m + n) = 2 ^ m * 2 ^ n` — that `n ↦ 2 ^ n` is a group homomorphism
`ℤ → ℚ₂ˣ`, whose image is infinite cyclic.

`Reading:` **CARRIER** — *one-parameter subgroup* is archimedean-Lie vocabulary, presupposing a
continuous real parameter. It does not apply here, and the reason is a fact about the carrier rather
than about the map: `ℚ₂ˣ` is totally disconnected, so it has no one-parameter subgroups at all. The
correct description of the family is discrete.

## Standard vocabulary, and where the axis reading comes from

An element of `PGL(2, K)` over a non-archimedean field whose two eigenvalues have different valuation
is called **loxodromic**. It has a unique invariant geodesic in the Bruhat–Tits tree — its **axis** —
and it acts on that axis by translation, with **translation length** equal to the valuation of the
multiplier. Its **limit set** is the two fixed points.

Verified in the deposited PDF (Heydeman, Marcolli, Saberi and Stoica, arXiv:1605.07639v2): p. 20 for
the loxodromic definition and the axis, p. 58 for the limit set being `{0, ∞}` in `P¹(k)` and for the
translation length being `ord_k(q)`.

So `rScale_valuation` — the valuation shifts by exactly `n` — is translation length along the axis,
in that standard sense. § V's use of the word *axis* is borrowed from this literature, and the tree it
translates on is one import away in `ZeroParadox/Valuation/PadicTree.lean`.

## On the axiom footprint, which is easy to state wrongly

Everything in this file reports `[propext, Classical.choice, Quot.sound]`. Two things must not be
concluded from that.

**It is not introduced by anything p-adic.** `padicValNat p n` is defined as
`(Nat.maxPowDvdDiv p n).fst`, and `Nat.maxPowDvdDiv` — a generic natural-number division helper with
nothing p-adic about it — already reports `Classical.choice` at this pin. `Padic` and `PadicInt`
inherit the footprint rather than adding one. `ZeroParadox/Valuation/PricedPadicInterface.md` reaches
the same conclusion independently and notes that every footprint there is pin-relative.

**It does not establish that the footprint is forced.** `#print axioms` reports which axioms a
particular proof term used. It is silent about what some other proof of the same statement might use.
`ZeroParadox/Valuation/PricedPadicInterface.lean` proves the corresponding valuation shift on a
choice-free ℕ carrier (`v2_scale_nat`, `[propext, Quot.sound]`), which shows the *arithmetic* does
not require choice; whether the statement over `ℚ_[2]` does is not settled here, in either direction.

Note also that `hx : x ≠ 0` in `rScale_valuation` comes from the ℤ-valued `Padic.valuation`, which has
no value at `0`. `Padic.addValuation` is `WithTop ℤ`-valued and carries an unguarded `map_mul` with
`v 0 = ⊤`, so the guard is a consequence of the codomain rather than of the mathematics.
