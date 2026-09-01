import ZeroParadox.Multihomed.TreeObstructions
import ZeroParadox.Order.MarkovPlacement
import ZeroParadox.Multihomed.RootCutObstruction
import ZeroParadox.Multihomed.WallSpanRobust
import ZeroParadox.Computability.MarkovNuUniversal
import ZeroParadox.Order.WellFoundedObstruct
import ZeroParadox.Valuation.NuRateEdge
import ZeroParadox.Category.SeamNotColimit
import ZeroParadox.Multihomed.FloorFactsCooccur
import ZeroParadox.Multihomed.TwoFacesBot
import ZeroParadox.Category.SeamUniqueness
import ZeroParadox.Category.RootCutDegeneracy
import ZeroParadox.Valuation.ContractionRate
import ZeroParadox.Category.RootCutBinary
import ZeroParadox.Multihomed.SeamConnectorFail
import ZeroParadox.Order.MarkovContractionDual
import ZeroParadox.Order.SeamSchema
import ZeroParadox.Valuation.NuRateMatch
import ZeroParadox.Computability.RootCutTrichotomy
import ZeroParadox.Computability.ChoicePurityInvariant
import ZeroParadox.Computability.NatListRegime
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Multihomed.SelfAppForkPlace
import ZeroParadox.Multihomed.SelfAppSeam
import ZeroParadox.Settheory.Wall
import ZeroParadox.Order.Snap
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Information.Surprisal
import ZeroParadox.Information.BottomMeasure
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Computability.Kleene
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Valuation.InversionValuation
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Category.Category
import ZeroParadox.Valuation.FloorWitness
import ZeroParadox.Ordinal.ProofFloorCanonical
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Valuation.PoleCornersBridge
import ZeroParadox.Multihomed.HilbertDiagonal
import ZeroParadox.Reals.MarkovSpectralGap
import ZeroParadox.Category.Node4Generation
import ZeroParadox.Multihomed.TwoFacesBot
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Order.BoundedOrder.Basic

/-!
# Index of declarations characterizing ⊥

Curated, not exhaustive. An INDEXED name is `#check`ed, so it cannot be dead; a name occurring only
inside a gloss is not. `Statement:` restates what a declaration proves; `Reading:` is interpretation,
not a claim about the theorem. Where a `Reading:` asserts strength, scope or genericity it should
carry an `example` that fails to compile if it is wrong; those are the only things proved here, and
not every such `Reading:` has one yet. Sections: what ⊥ cannot be, must be, and how it is reached.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

section CannotBeIndex

/-! ### ⊥-interpretations do not unify across the μ/ν root -/

-- Statement: no strictly monotone map ℝ → Ordinal exists.
-- Reading: supporting infrastructure, not a ⊥-exclusion on its own.
#check @ZeroParadox.no_strictMono_real_to_ordinal
-- Statement: `<` on ℝ is not well-founded.
#check @ZeroParadox.real_carrier_not_wellFounded
-- Statement: on the standard simplex, `p ≤ q` forces `p = q` — it is an antichain.
#check @ZeroParadox.simplex_antichain
-- Statement: `{0} ⊆ ℚ₂` as a `TopCat` object admits no initial-object structure.
#check @ZeroParadox.padic_bottom_not_initial
-- Statement: both the Kleisli and Hilbert floors are initial, and `Fin 0 ≃ StateSpace 0` is empty.
#check @ZeroParadox.split_kleisli_vs_hilbert
-- Statement: the Kleisli floor is initial, and `Fin 0 ≃ {0} ⊆ ℚ₂` is empty.
#check @ZeroParadox.split_kleisli_vs_padic
-- Statement: `Cofix → Fix` is empty for the identity polynomial functor.
#check @ZeroParadox.root_cut_no_map_nu_to_mu
-- Statement: that emptiness, plus any two maps `Fix → Cofix` being equal.
#check @ZeroParadox.root_cut_strict_asymmetric

/-! ### ⊥ cannot be reached by a structure-preserving (descending/ν) comparison -/

-- Statement: if `r` is not well-founded, no `f : S → Ordinal` is strictly increasing along `r`.
#check @ZeroParadox.no_faithful_span_to_ordinal_and_descending
-- Statement: the converse biconditional — such an `f` exists iff `r` is well-founded.
#check @ZeroParadox.faithful_iff_descending

-- Statement: the equivalences `{x // selfApp x = x} ≃ PUnit` form a subsingleton.
-- Reading: GENERIC — indexed to fence a misreading, not to carry one. `Subsingleton (α ≃ PUnit)`
-- holds of every type, so this says nothing about ⊥ on its own; the source calls it "the generic
-- singleton iso". The `example` below is the refutation of any stronger reading.
#check @ZeroParadox.faces_iso_unique
example (α : Type) : Subsingleton (α ≃ PUnit) := inferInstance
-- Statement: an equivalence `{x // selfApp x = x} ≃ PUnit`.
-- Reading: THIS is the declaration carrying the coincidence of the two faces as objects, and that
-- coincidence is real at ⊥. Its content comes from the assumed class fields `unique_fp` /
-- `fixed_bot`, not from the theorem above.
#check @ZeroParadox.selfApp_face_equiv_punit

/-! ### the Markov interpretation cannot be a single ordered or unique point -/

-- Statement: for `2 ≤ n` and EVERY chain `f`, some stationary distribution of `f` is neither least
-- nor greatest in the simplex.
#check @ZeroParadox.stationary_attractor_no_order_placement
-- Statement: a doubly-stochastic `Fin 4` chain other than the pure chain exists whose stationary
-- distribution is not unique.
#check @ZeroParadox.markov_node_no_universal_property
-- Statement: so stationarity under doubly-stochastic `Fin 4` chains is not subsingleton-valued.
#check @ZeroParadox.doublyStochastic_stationary_not_subsingleton

/-! ### the p-adic floor cannot be reached from within, nor matched to the Markov rate -/

-- Statement: for `x ≠ 0` in ℚ₂, `2ⁿ * x ≠ 0` at every finite `n` — the orbit never lands on 0.
#check @ZeroParadox.padic_orbit_never_reaches_zero
-- Statement: for `x ≠ 0`, no reindexing `φ : ℕ → ℕ` matches the p-adic rate to the Markov rate at
-- every step.
#check @ZeroParadox.no_rate_conjugacy
-- Statement: for `x ≠ 0`, indeed no single pair of indices makes the two rates agree.
#check @ZeroParadox.no_rate_orderIso

/-! ### categorical floor and seam exclusions -/

-- Statement: `fD_functor.obj 1` is not a zero object.
#check @ZeroParadox.leaf_not_isZero
-- Statement: `(0 : ℕ)` admits no terminal-object structure.
-- Reading: GENERIC — its own source calls this a poset triviality, not a framework-specific fact.
#check @ZeroParadox.nat_zero_not_terminal
-- Statement: the Kleisli floor `fC_functor.obj 0` is not a zero object.
#check @ZeroParadox.kleisli_bottom_not_zero
-- Statement: `{0} ⊆ ℚ₂` as a `TopCat` object is not a zero object.
#check @ZeroParadox.padic_bottom_not_zero
-- Statement: given no top, `bot ≤ x` for all `x` while `x ≤ bot` fails for some — least, not greatest.
#check @ZeroParadox.zpa_bot_not_greatest

/-! ### μ/ν fork: the least fixed point is empty, or does not match the greatest -/

-- Statement: `Fix ≃ Cofix` is empty for the identity polynomial functor.
#check @ZeroParadox.idPF_no_seam
-- Statement: and for the binary one.
#check @ZeroParadox.binPF_no_seam
-- Statement: the `W`-type of the trichotomy functor is empty.
#check @ZeroParadox.strict_fix_isEmpty
-- Statement: `Fix idPF_Coalgebra.Obj` is empty, proved choice-free (a tighter axiom footprint).
#check @ZeroParadox.fix_isEmpty_constructive
-- Statement: `fixToCofix` is not surjective.
#check @ZeroParadox.fixToCofix_not_surjective

/-! ### orbits that cannot reach ⊥, or cannot be matched -/

-- Statement: for `‖u‖ = 1` and `x ≠ 0`, the orbit `uⁿ * x` does not converge to 0.
#check @ZeroParadox.unit_orbit_not_tendsto_zero
-- Statement: the swap chain's orbit from `e0vec` converges to no limit.
#check @ZeroParadox.swap_orbit_not_convergent
-- Statement: for `x ≠ 0` and balanced `v₀`, the p-adic orbit stays norm-positive and the
-- `markovStep (1/4)` orbit stays balanced — that one chain, not Markov orbits generally.
#check @ZeroParadox.padic_markov_no_orbit_correspondence

/-! ### the seam and floor cannot be transported or cross-connected -/

-- Statement: the Hilbert floor is a zero object while the p-adic floor admits no initial structure.
#check @ZeroParadox.seam_role_not_transported
-- Statement: no binary cofan of `fD_functor.obj 1` with itself has `fD_functor.obj 0` as a colimit
-- apex.
#check @ZeroParadox.seam_not_mu_colimit_apex
-- Statement: the QPF seam is the canonical bijection, no `Fix ≃ Cofix` exists for the recursive
-- `idPF_Coalgebra`, the lattice seam is the identity equivalence, and the `selfApp` fixed points
-- are `{bot}`.
-- Reading: this records that no cross-setting map was EXHIBITED — an open "none given", not a no-go.
-- The `IsEmpty` conjunct above is about `Fix ≃ Cofix`, not about any cross-setting map type.
#check @ZeroParadox.no_cross_setting_map
-- Statement: `(1 : ℕ) ⟶ (0 : ℕ)` is empty.
#check @ZeroParadox.isEmpty_hom_one_to_zero
-- Statement: in a `ZPCategory`, an object not isomorphic to the initial admits no map into it.
-- Reading: this IS the class field AX-G2, a named structural commitment, not a consequence derived
-- from one — the `example` below closes it by `rfl`. Same fence as `unique_fp` below.
#check @ZeroParadox.t3_unreachability
example : @ZeroParadox.t3_unreachability = @ZeroParadox.ZPCategory.ax_g2 := rfl
-- Statement: rose trees over a partially-well-ordered preorder are partially well ordered.
-- Reading: this is the labeled Kruskal tree theorem (Kruskal 1960, after Higman 1952 and
-- Nash-Williams 1963); full attribution in `ZeroParadox/Ordinal/Kruskal.lean`. Indexed as a SCOPE
-- FENCE — a well-quasi-order is not a descent to a bottom, so the "canonical floor 0" claim does
-- not reach here.
#check @ZeroParadox.kruskal_is_wqo_not_descent

/-! ### POSITIVE — ⊥ as the fixed point where operation and result coincide -/

-- Statement: a FIELD of the `AbstractSelfApp` class — every `selfApp` fixed point equals `bot`,
-- assumed of the action, not derived.
-- Reading: the framework calls this coincidence of input and output "concurrency".
#check @ZeroParadox.AbstractSelfApp.unique_fp
-- Statement: `bot` is a fixed point of `selfApp`, AND is both below and above every fixed point.
-- Reading: only the GREATEST bound uses `unique_fp`. The least is `bot_le x`, which discards the
-- fixed-point hypothesis entirely — a bare `ZPSemilattice` fact. So the two-sided coincidence is one
-- triviality conjoined with one assumption, not two consequences. Same for the line below.
#check @ZeroParadox.selfApp_fixed_point_is_seam
-- Statement: the same two bounds WITHOUT the existence conjunct — every `selfApp` fixed point is
-- both `≥ bot` and `≤ bot`.
#check @ZeroParadox.selfApp_bot_is_both_extremal
-- Statement: `¬(p ↔ ¬p)` — logical negation has no fixed point.
-- Reading: RE-PROVED here, not imported — `ZeroParadox/Settheory/Wall.lean` gives a three-line term
-- proof. The standard name is Lean core's `iff_not_self`, and the two are the SAME type despite the
-- differing binder display; the equality `example` below settles that. Cite the core lemma and read
-- this one as a local restatement, not a distinct result.
-- The contrast that makes the coincidence above meaningful; the fixed-point-free map (Lawvere).
-- ⚠ Do NOT read it as "involutions have no fixed point" — the negation-on-ℤ `example` below is
-- one that does.
#check @ZeroParadox.negation_no_fixedpoint
-- Binder annotation is not part of a type, so the re-proof and the core lemma are one statement.
example : @ZeroParadox.negation_no_fixedpoint = @iff_not_self := rfl
-- Negation on ℤ carries BOTH conjuncts the ⚠ above needs: it is an involution, and it has a fixed
-- point. Exhibited rather than asserted, so neither half rests on the comment.
example (x : ℤ) : (fun y : ℤ => -y) ((fun y : ℤ => -y) x) = x := neg_neg x
example : (fun x : ℤ => -x) (0 : ℤ) = 0 := rfl

/-! ### POSITIVE — narrow uniqueness and infinite width, which coincide only at ⊥ -/

-- Statement: in ℚ₂, `q2SelfMem x` forces `x = 0` — at most one such point. [NARROW]
#check @ZeroParadox.q2_unique_fp
-- Statement: and `0` is one — `q2SelfMem 0`. Existence is this declaration, not the one above.
#check @ZeroParadox.q2_zero_is_fixed
-- Statement: the intersection of the nested balls is exactly `{0}`. [NARROW]
#check @ZeroParadox.fB_bottom_is_limit
-- Statement: the partial circulation exceeds every bound `M`. [WIDE, infinite measure]
#check @ZeroParadox.t2_diverges
-- Statement: surprisal exceeds every bound `M` — the same shape over a different function; this
-- declaration is literally `l_inf`. [WIDE, measure]
#check @ZeroParadox.info_bottom_diverges
-- Statement: for `‖c‖ < 1`, every orbit `cⁿ * x` converges to 0. [WIDE, infinite reach]
#check @ZeroParadox.contraction_orbit_tendsto_zero
-- Reading: narrow and reach hold of the SAME point 0 in ℚ₂ — `q2_unique_fp`'s unique point is
-- `contraction_orbit_tendsto_zero`'s limit. That pairing is the framework's 0=∞ signature. It is a
-- criterion, not a theorem, and the measure aspect lives in a different construction (ZPC), so the
-- three are assembled across carriers rather than proved of one.

-- Statement: `(∀ x, join S x = x) ↔ S = bot` — exactly one element plays the ⊥ role. [NARROW]
#check @ZeroParadox.da2_bottom_characterization
-- Statement: the initial object maps to every object by exactly one morphism. [NARROW]
#check @ZeroParadox.t2_universal_constituent
-- Statement: in any additively-valued ring, `v 0 = ⊤`. [WIDE, measure; subsumes the p-adic case]
-- Reading: CITED, not ZP-proved — the proof body is `v.map_zero`, i.e. Mathlib's
-- `AddValuation.map_zero`. Indexed for the ⊥-reading of `⊤`, not as a result of this framework.
#check @ZeroParadox.addVal_bot
-- Statement: the ε₀-tower encodings converge to 0 in ℤ_[2]. [WIDE, reach]
#check @ZeroParadox.tower_converges_to_zero

/-! ### INVERSION — the symmetry linking the narrow and wide poles -/

-- Statement: `(·⁻¹)` maps `{x ≠ 0 ∣ n ≤ v₂ x}` onto `{x ≠ 0 ∣ v₂ x ≤ -n}`.
-- Reading: the inversion symmetry of the tower. ⚠ It is ℤ-valued and carries NO literal 0=∞
-- content — 0 is the excluded centre, and the source file disclaims that reading.
#check @ZeroParadox.inversion_reverses_filtration
-- Statement: for rational `x ≠ 0`, the one orbit `2ⁿx` converges to 0 in ℚ₂ AND diverges to ∞ in ℝ.
-- Reading: this is where the literal 0=∞ content lives — one orbit, two place-views.
#check @ZeroParadox.doubling_place_dichotomy
-- Statement: `rInvHomeo` sends `0` to `∞` and `∞` to `0` on `OnePoint ℚ₂`.
#check @ZeroParadox.rInv_swaps
-- Statement: a conjunction whose first component is the DISEQUALITY of the floor pole and the
-- infinity pole; inversion exchanging them follows in the same declaration.
-- ⚠ `rInv_swaps` directly above states two equations and nothing else, so cite THIS one wherever the
-- distinctness is what a sentence leans on.
#check @ZeroParadox.point_and_field_at_the_poles
-- Statement: that inversion is a homeomorphism of the sphere.
#check @ZeroParadox.rInvHomeo
-- Statement: Mathlib's `IsInitial.op` — the opposite of an initial object is terminal.
-- Reading: CITED, not ZP-proved; attribution is the point. Passing to `Cᵒᵖ` is the categorical face
-- of inversion, swapping the μ-bottom to a terminal object.
#check @CategoryTheory.Limits.IsInitial.op
-- Statement: Mathlib's `hasZeroObject_op` — a zero object stays a zero object in the opposite.
-- Reading: the seam is self-dual under `op`, the fixed centre of the inversion.
#check @CategoryTheory.Limits.hasZeroObject_op
-- Reading: PRIOR-ART RECORD, do NOT rebuild. The abstract "order-reversal swaps ⊥ and ⊤" is already
-- Mathlib's, indexed below. The three inversions share no single buildable type, so their
-- "unification" is a schema, not a theorem.
-- Statement: over a bare `[Bot α]`, passing to the order dual sends ⊥ to ⊤ — by `rfl`, with no
-- lattice, complement or completeness in sight. This is the abstract fact; `compl_bot` and friends
-- are Boolean-algebra special cases of it.
#check @OrderDual.toDual_bot

/-! ### SELF-REFERENCE — the diagonal fixed point

The cross-field routing, and its Lawvere / Yanofsky attribution, live in
`ZeroParadox/DiagonalFixedPoint.lean`. This section indexes only the ⊥-facing declarations. -/

-- Statement: under `[KleeneStructure]`, any Quine atom `q` satisfies `q = bot`. The statement has no
-- Kleene clause; the quine-atom property is a hypothesis, and what the class supplies is the
-- inherited `AFAStructure.bot_self_mem`.
-- Reading: the self-EXECUTING reading is the framework's, carried by the class commitment rather
-- than by this theorem. See ZP-K § II and § III.
#check @ZeroParadox.kleene_quine_is_bot
-- Statement: some code `c` is a computational quine.
#check @ZeroParadox.computational_quine_exists
-- Statement: for a computational quine `c`, `eval c n = eval c (encode c + n)` — the Gödel number is
-- *a* period of the evaluation.
-- Reading: ⚠ not *the* period. It is not shown least, and a constant code is periodic with every
-- period, so this does not tie index to function. A periodicity fact, not a diagonal identity.
#check @ZeroParadox.quine_period_is_goedel
-- Statement: a Kleene-periodic code exists AND a least ordinal with `ω^α = α` exists.
-- Reading: the two diagonalization fixed points coexist; the conjunction is not an identification.
#check @ZeroParadox.both_fixed_points_exist
-- Statement: a finite-dimensional `X : ModuleCat ℂ` with `X ≅ X ⊞ X` is the zero object.
-- Reading: the OTHER sub-sense of self — self-similarity under the biproduct diagonal, as opposed to
-- the Kleene sense of a code applied to its own index.
#check @ZeroParadox.biprod_diagonal_only_zero
-- Statement: the free ℂ-module on ℕ is self-similar under that diagonal — `X ≅ X ⊞ X` — because
-- ℵ₀ + ℵ₀ = ℵ₀. Standard name: the Eilenberg–Mazur swindle.
#check @ZeroParadox.freeNat_biprod_self
-- Statement: and it is not finite over ℂ, so it sits outside the theorem above. The exclusion is
-- proved, not asserted in a docstring.
#check @ZeroParadox.freeNat_not_finite
-- Statement: and it is NOT the zero object. So the finiteness hypothesis carries the theorem rather
-- than decorating it — the counterexample is exhibited, not asserted.
#check @ZeroParadox.freeNat_not_isZero
-- Statement: the seam satisfies `seam ≅ seam ⊞ seam` and is a zero object.
#check @ZeroParadox.seam_is_diagonal_fixpoint

/-! ### GENERATION — the floor generates its first step -/

-- Statement: `epsilonZero = nfp (ω^·) 0` — the least ordinal closed under `ω^·` above 0.
-- Reading: CITED, not ZP-proved — a one-line wrapper on Mathlib's `Ordinal.epsilon_zero_eq_nfp`
-- (`SetTheory/Ordinal/Veblen.lean`). `epsilonZero_le_fixedPoint` and `epsilonZero_eq_iSup` below
-- are wrappers in the same sense.
#check @ZeroParadox.epsilonZero_eq_nfp
-- Statement: `ω^b = b → epsilonZero ≤ b` — ε₀ is below every fixed point of `ω^·`. Wraps Mathlib's
-- `Ordinal.epsilon_zero_le_of_omega0_opow_le`, which assumes the weaker `ω^b ≤ b`.
#check @ZeroParadox.epsilonZero_le_fixedPoint
-- Statement: Mathlib's Kleene fixed-point theorem: for ωScott-continuous `f`, `lfp f = ⨆ₙ fⁿ(⊥)`.
-- Reading: CITED prior art for generation, do NOT rebuild. ⚠ `Ordinal` is NOT an instance of it —
-- the theorem needs `[CompleteLattice α]`, which `Ordinal` does not carry. A shared SHAPE across
-- structures, never an instance-of relation. (Monotonicity is NOT the obstruction: `Ordinal →o
-- Ordinal` is inhabited, below.)
#check @fixedPoints.lfp_eq_sSup_iterate
noncomputable example : Ordinal.{0} →o Ordinal.{0} :=
  ⟨fun a => Ordinal.omega0 ^ a, fun _ _ h => Ordinal.opow_le_opow_right Ordinal.omega0_pos h⟩
-- Statement: the ordinal form that does hold — `⨆ n, f^[n] a = nfp f a`.
#check @Ordinal.iSup_iterate_eq_nfp
-- Statement: and ε₀ as that supremum — `epsilonZero = ⨆ n, fundamentalSeq n`.
#check @ZeroParadox.epsilonZero_eq_iSup
-- Reading: generation pairs with the μ side (build up from ⊥) and its dual is reach on the ν side
-- (flow down to ⊥). So generation being absent on the ν-bottoms is the μ/ν fork, not a gap — they
-- carry reach instead.
-- Statement: given a compatible family `f : (n : ℕ) → Fin n → P`, there is a UNIQUE `g : ℕ → P`
-- agreeing with every stage.
-- Reading: that universal property is what makes ℕ the colimit of the `Fin`-chain.
#check @ZeroParadox.node4_generates_nat
-- Reading: Adámek's initial-algebra colimit is not located in Mathlib as of 2026-08-08; what is
-- there is Lambek's lemma, indexed below.
-- Statement: the structure map of an initial algebra is an isomorphism (Lambek).
#check @CategoryTheory.Endofunctor.Algebra.Initial.str_isIso

/-! ### DYNAMICS — how ⊥ is approached and departed -/

-- Statement: `c₀ ≠ c₁`, `c₁ ≠ c₀`, and `join c₀ c₁ = c₁`.
-- Reading: the state advance off the floor. The statement constrains the SHAPE of a transition, not
-- that one occurs.
#check @ZeroParadox.t_snap_derived
-- Statement: for `x ≼ y` with `x ≠ y`, no join returns `y` to `x`.
-- Reading: a GENERIC semilattice no-return lemma. It mentions neither ⊥ nor the snap; the snap
-- instantiates it. The irreversibility reading is the application, not the statement.
#check @ZeroParadox.t_snap_irreversible
-- Statement: for `0 < n`, `fC_functor.obj n ⟶ fC_functor.obj 0` is empty.
#check @ZeroParadox.fC_no_return
-- Statement: the predecessor orbit from any `n` reaches the floor in finitely many steps. [μ]
#check @ZeroParadox.pred_orbit_reaches_floor
-- Statement: the doubling orbit converges to 0 in the 2-adic metric. [ν]
#check @ZeroParadox.doubling_orbit_tendsto_zero
-- Statement: for `X` not isomorphic to the initial, and given `⊥ ⟶ X`, the hom `X ⟶ ⊥` is still
-- empty.
-- Reading: a one-line consequence of `t3_unreachability` — the same no-incoming fact under the
-- irreversibility reading rather than the unreachability one. Not new content. ⚠ NOT definitionally
-- equal: `t4` carries an extra unused `⊥ ⟶ X` binder, so `@t4 = @t3 := rfl` does not typecheck.
#check @ZeroParadox.t4_chains_forward_only
-- Statement: the relaxation operator of `fullMix` is not injective.
-- Reading: information is lost, so the relaxation cannot be reversed. ⚠ FENCE: mixing-specific, NOT
-- universal — permutation chains do not mix (`swap_orbit_not_convergent`, which exhibits one
-- non-convergent orbit and says nothing about eigenvalues).
#check @ZeroParadox.fullMix_not_injective
-- Statement: an eigenmode with `|λ| < 1` has `‖(T f)^[m] v‖ → 0`.
#check @ZeroParadox.tendsto_norm_iterate_zero

end CannotBeIndex
