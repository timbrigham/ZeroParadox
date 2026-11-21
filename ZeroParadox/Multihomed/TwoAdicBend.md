# TwoAdicBend — multiplier maps on `OnePoint ℚ_[2]` up to topological conjugacy

Ride-along companion to `ZeroParadox/Multihomed/TwoAdicBend.lean`, the 2-adic companion to
`ZeroParadox/Multihomed/BendDie.lean`. Experimental probe in the bottom-diagram mapping campaign,
**not a finalized layer**. Curated results are indexed in `ZeroParadox/MANIFEST.md` and
`ZeroParadox/DieCannotBe.lean` § XXXVIII.

## Formal Overview (AI-assisted)

A multiplier map (dilation) is `z ↦ c z`; on the one-point compactification `OnePoint K` it is
`lmScale c` (`ZeroParadox/Multihomed/LimitMotion.lean`), fixing `∞`. It is contracting if `‖c‖ < 1`,
expanding if `1 < ‖c‖`, and indifferent if `‖c‖ = 1`. `ScaleConj c d` says a homeomorphism of
`OnePoint K` conjugates `lmScale c` to `lmScale d` (topological conjugacy on the one-point
compactification, a global relation; it is not Jenkins–Spallone's local one, see Prior art);
`scaleConj_homeoIso` turns it into a `Motion.HomeoIso` of the limit motions
(`ZeroParadox/DieSameness.lean`). ℂ and `ℚ_[2]` are two carriers below; no statement equates a
point of one with a point of the other.

- § I. `ScaleConj` is an equivalence relation (`scaleConj_refl`, `scaleConj_symm`,
  `scaleConj_trans`); inversion gives `×c ~ ×c⁻¹` (`scaleConj_inv`); a homeomorphism of `K` with
  `e (c z) = d (e z)` extends to `OnePoint K` (`scaleConj_of_homeo`).
- § III. The discrete twist `dTwist u z = u ^ v(z) * z`, `v` the 2-adic valuation. For `‖u‖ = 1` it
  preserves the norm (`dTwist_norm`) and is a homeomorphism of `ℚ_[2]` (`dTwistHomeo`), and
  `dTwist_conj_mul` gives `×c ~ ×(u ^ v(c) * c)` (`dTwist_scaleConj`); `×2 ~ ×(2u)` is
  `dTwist_scaleConj_two`; `×2 ~ ×6` is `dTwist_scaleConj` at `u = 3`, and `dTwist_two_six` is the
  resulting `Motion.HomeoIso` of the limit motions. The control `dTwist_mult_valuation`: the
  twist never changes the valuation of the multiplier, so it never sends `×2` to `×4`
  (`dTwist_not_two_four`, with `dTwist_conj_mul`). `×2 ~ ×4` is § IV's `scaleConj_two_four`.
  `Reading:` that control is about the twist only.
- § IV. The step merge. For `v(c) = k + 1`, `stepHomeo c k` sends `2 ^ n * w` to `c ^ n * psiK k w`
  (`w` a unit), where `psiK k` sends the units into the shells `0 … k` and `rhoK k` back, each
  undoing the other there (`rho_psi`, `psi_rho`; continuity `psiK_continuous`, `rhoK_contAt`);
  `stepMap_conj` is the conjugacy equation. So `×2 ~ ×c` for every
  contracting `c` (`scaleConj_two_of_norm_lt_one`), every `c` with `‖c‖ ≠ 1`
  (`scaleConj_two_of_norm_ne_one`, an expanding `c` through `scaleConj_inv`), and any two such
  multipliers (`scaleConj_of_norm_ne_one`, `homeoIso_of_norm_ne_one`). The control
  `scaleConj_two_not_norm_one`: an indifferent `d` (`‖d‖ = 1`) is never conjugate to `×2`.
- § V. Four flips. `uFlip z = 4 ^ v(z) * z⁻¹` (the unit-inverse flip, `2 ^ v * w ↦ 2 ^ v * w⁻¹`)
  and group inversion give automorphisms `flipU`, `flipI` of `ℚ_[2]ˣ`, both continuous
  (`flipU_continuous`, `flipI_continuous`), with `flip_klein_units`: commuting involutions,
  four pairwise distinct elements. On `OnePoint ℚ_[2]`, `flipS` extends `uFlip` and
  `flipA = flipS ∘ onePointInv` (defined as `flipA`, unfolded by `flipA_apply`) is the amplitude
  flip `2 ^ v * w ↦ 2 ^ (-v) * w`: at `z ≠ 0` it gives `uFlip z⁻¹ = (uFlip z)⁻¹ = 4 ^ (-v(z)) * z`
  (`uFlip_inv`, `ampFlip_eq`); `flip_klein_onePoint` gives the involution, commutation and
  distinctness laws on `OnePoint ℚ_[2]`. `flipA` exchanges `0` of `ℚ_[2]` and `∞` of
  `OnePoint ℚ_[2]`, `flipS` fixes both (`flip_poles`); `flipA` fixes every point of the unit shell `‖z‖ = 1`
  (`flipA_fixes_shell`), while `rInv` (`ZeroParadox/Valuation/RiemannSphere.lean`) fixes a shell
  point iff it is `±1` (`rInv_shell`; the control `rInv_moves_three`). `flip_conj_scales`
  conjugates `×c` to the three flipped multipliers, `ampFlip_eq` computes the amplitude-flipped one.
  `Statement:` `flip_klein_units` exhibits a Klein four subgroup of the automorphisms of
  `ℚ_[2]ˣ`. `Reading:` it does not say these four are all of them.
- § VI. On `OnePoint ℂ`, `×c` is conjugate to `×conj c` (`bend_conj_conj`,
  `ZeroParadox/Multihomed/BendDie.lean`), to `×c⁻¹` and to `×(conj c)⁻¹` (`complex_four_conj`), so
  any two of the four give `Motion.HomeoIso`-related limit motions (`complex_four_homeoIso`).
  `z ↦ (conj z)⁻¹` fixes every point of the unit circle (`complex_ampFlip_fixes_circle`); inversion
  alone and conjugation alone each move `i` (`complex_flip_controls`).
- § VII. `IsAttractingFixedPt` and `IsRepellingFixedPt` are the topological notions; a topological
  conjugacy preserves both (`attracting_conj_iff`, `repelling_conj_iff`); an injective map
  cannot have a fixed point that is both, when that point is not an isolated point of the space
  (every neighbourhood of it holds another point; `not_attracting_and_repelling`); and on a
  Hausdorff space a fixed point `p` is repelling when every other orbit converges to one point
  `q ≠ p` (`repelling_of_tendsto`). On
  `OnePoint K`, `K` a nontrivially normed field with `ProperSpace K`: for `‖c‖ ≠ 1`, `0` of `K` is attracting iff `c` is
  contracting and repelling iff it is expanding (`scale_zero_classification`); `∞` the reverse,
  derived by transport through `onePointInvHomeo` (`scale_infty_classification`); for `‖c‖ = 1`,
  neither `0` of `K` (`tb_zero_not_attracting_of_norm_one`, `tb_zero_not_repelling_of_norm_one`)
  nor `∞` (`scale_infty_neither_of_norm_one`) is attracting or repelling. `conj_swaps_poles`:
  every homeomorphism conjugating an expanding multiplier to a contracting one exchanges `0` of `K` and `∞`. Instances, one per
  carrier: `×2` on `OnePoint ℂ` (`complex_two_poles`, `1 < ‖2‖`) and `×2` on `OnePoint ℚ_[2]`
  (`padic_two_poles`, `‖2‖ < 1` in `ℚ_[2]`), with the attracting and repelling roles of `0` and `∞`
  exchanged between the two. Controls: `scale_control_one` (`×1`) and `scale_control_rotation`
  (`×i`).

Axiom footprints: the `PurityCheck` section at the end of `TwoAdicBend.lean`.

## Prior art

- A. Jenkins and S. Spallone, "Lipeomorphic equivalence for p-adic analytic functions: a comparison
  between complex and p-adic dynamics", arXiv:1011.2451v1 (2010). Standard names adopted here:
  "multiplier map", "contracting / expanding / indifferent". Their "homeomorphically equivalent"
  is a different relation from `ScaleConj`: conjugacy by an invertible germ at `0` (abstract,
  p. 1), under which the contracting maps form one equivalence class and the expanding maps
  another (§ 1, p. 1); `ScaleConj` is topological conjugacy on the one-point compactification, and it joins them
  (`scaleConj_inv`), every such conjugacy exchanging `0` of `K` and `∞` (`conj_swaps_poles`).
  Proposition 7.1, p. 26: "For i = 1, 2, let p_i be primes,
  π_i ∈ p_i ℤ_{p_i} − {0} and write L_{π_i} : ℚ_{p_i} → ℚ_{p_i} for dilation by π_i. Then there is a
  homeomorphism h : ℚ_{p_1} → ℚ_{p_2} so that h ∘ L_{π_1} ∘ h⁻¹ = L_{π_2}. In fact, we may choose h
  and a constant C > 0 with the property that |h(x)| ≤ C|x|^{ord(π_1)/ord(π_2)}. This exponent cannot
  be improved." At `p_1 = p_2 = 2` (`π_2 = 2u`, `π_2 = 4`), `dTwist_scaleConj_two` and
  `scaleConj_two_four` recover the topological part of it on `OnePoint ℚ_[2]`, the existence of a
  conjugating homeomorphism, and not its growth bound; the first has an explicit closed-form
  conjugacy. Their proof builds `h` from a homeomorphism of fundamental domains `Δ_π = {|π| < |x| ≤ 1}` (Def. 3.6, p. 7),
  and for `π = 4` that domain is units plus twice units. Its § 7 opening (p. 26) also asserts, without proof there, that
  for `a` a primitive `k`-th root of unity, `L_a` and `L_a'` are homeomorphically equivalent iff
  `a'` is also a primitive `k`-th root of unity, so for a root of unity the order `k` is an
  invariant; the same paragraph states that any two irrational indifferent multiplier maps are
  homeomorphically equivalent (and Proposition 7.5, p. 27, for `a, a'` in `ℤ_p^×` not roots of
  unity).
- J. Bastos, D. Caprio and A. Messaoudi, "Shadowing and stability in p-adic dynamics",
  arXiv:2001.02737v1 (2020), Theorem 26, p. 14: "if ‖a‖_p ≠ 1, then f_{a,b} is Lipschitz
  structurally stable. Furthermore, the conjugation is an isometry and f_{a,b} is topologically
  conjugate to f_{1/p^k,0}, where ‖a‖_p = p^k". In the proof's Case 1 (`a = 1/p`, p. 16, (21)–(22))
  the conjugacy `h` with `f_{1/p} ∘ h = h ∘ g`, between the `a = 1/p` map and its perturbation
  `g = f_a + ψ`, is defined digit by digit, `h_i(x) = (g^i(x))_0`. This file proves, for ‖u‖ = 1, `dTwist u`
  norm-preserving (`dTwist_norm`) and an isometry (`dTwist_isometry`).
- The bi-Lipschitz level: `Motion.scale24_not_lip` (`ZeroParadox/DieSameness.lean`) separates `×2`
  and `×4` on ℝ (a `HomeoIso`, no `LipIso`); its docstring cites the p-adic counterpart in
  Jenkins–Spallone. No `LipIso` statement is made here; `dTwist_mult_valuation` records that the twist keeps the
  valuation of the multiplier, and § IV's step map does not.
- The complex side: `ZeroParadox/Multihomed/BendDie.md` (Rybalkina–Sergeichuk Lemma 2.1; Budnytska;
  Kuiper–Robbin as those papers cite it). Joining contracting and expanding multipliers through
  `z ↦ 1/z` on `OnePoint ℚ_[2]` follows their route on the Riemann sphere; a statement of it for
  `P¹(ℚ_p)` was not retrieved from either p-adic source above. Closer: Y. Wang and J. Yang, "On
  p-adic Möbius maps", arXiv:1512.01305v1 (2015), p. 11, Proposition 3.3(3) (a p-adic Möbius
  map g is "loxodromic if it is conjugate to z → kz for some k with |k| > 1"; the converse is
  used in the proof of Proposition 3.5, p. 11, which assumes without loss of generality that an
  elliptic or loxodromic g is g(z) = (a/d)z) and Proposition 3.4 (two
  non-identity p-adic Möbius maps "are conjugate if and only if trace(f) = trace(g)"). That is
  algebraic conjugacy by a Möbius map in `PSL(2, ℂ_p)` on `P¹(ℂ_p)`, not a topological
  classification on `OnePoint ℚ_[2]`.
- Corpus: `lmScale`, `lmHomeoIsoOfConj`, `lm_onePointInv_conj_scale`
  (`ZeroParadox/Multihomed/LimitMotion.lean`), `onePointInvHomeo`, `rInv`
  (`ZeroParadox/Valuation/RiemannSphere.lean`), `bend_conj_conj` (`BendDie.lean`). Mathlib:
  `Padic.valuation_mul`, `Padic.norm_eq_zpow_neg_valuation`, `PadicInt.exists_mem_range`,
  `Homeomorph.onePointCongr`, `Units.mapEquiv`, `MulEquiv.inv`.
- Search, 2026-11-19 (theoremsearch, three phrasings, one formal; LeanExplore; GitHub
  `extension:lean`; the open web): no conjugacy of p-adic
  multiplication maps was located in Mathlib as of that date; the null is uninformative.
