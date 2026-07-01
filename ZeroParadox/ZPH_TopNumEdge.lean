import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPN_B6_CanonicalCNF
import ZeroParadox.ZPK_PadicBridge
import ZeroParadox.ZPC
import Mathlib.NumberTheory.Padics.PadicNumbers

set_option maxHeartbeats 400000

/-!
# Web edge: topology ↔ number theory (the valuation generates the ball topology)

**Proves** `q2Ball_eq_addValuation_sublevel`: the clopen ball `q2Ball n = B(0, 2⁻ⁿ) ⊆ ℚ₂` IS the 2-adic addValuation sublevel set
`{x | n ≤ v₂(x)}` (in `WithTop ℤ`, where `v₂(0) = ⊤`, so `0` is included precisely because `⊤ ≥ n` — the
framework's `v₂(0)=∞` doing the work at the floor). This is the genuine topology↔number-theory edge: the
topological object (the ball) characterized by the number-theoretic invariant (the valuation), connecting
the Topology and Number-theory nodes at the p-adic hub.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.WebEdges

open ZeroParadox.ZPB ZeroParadox.ZPH_TopFunctor

/-- EDGE topology↔number-theory: the ball `B(0,2⁻ⁿ)` equals the addValuation sublevel `{x | n ≤ v₂(x)}`. -/
theorem q2Ball_eq_addValuation_sublevel (n : ℕ) :
    q2Ball n = {x : Q₂ | ((n : ℤ) : WithTop ℤ) ≤ Padic.addValuation x} := by
  ext x
  simp only [q2Ball, Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, Padic.addValuation.map_zero, le_top, iff_true]
    positivity
  · rw [Padic.addValuation.apply hx, Padic.norm_eq_zpow_neg_valuation hx, WithTop.coe_le_coe,
      show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
      zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    omega

/-- EDGE proof-theory → topology (the path via the floor): the ordinal tower's 2-adic encodings (B6,
    `cnf_encode_tower_tendsto_zero`) eventually enter EVERY closed ball around `0` in `ℤ₂`. So the
    proof-theory tower topologically approaches the snap floor that the balls shrink to — the composite of
    B6 (tower → 0) with the ball-neighborhood structure. Proof-theory reaches topology through the p-adic
    floor; it is the formalized 2-hop path, not a new direct transform. -/
theorem tower_enters_every_ball (n : ℕ) :
    ∀ᶠ k in Filter.atTop,
      ZeroParadox.P8.cnf_encode (ZeroParadox.P8.towerOrd k)
        ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) :=
  ZeroParadox.P8.cnf_encode_tower_tendsto_zero.eventually
    (Metric.closedBall_mem_nhds 0 (by positivity))

/-- EDGE computation → topology (the path via the floor): the computational quine family (B2,
    `quine_encodings_approach_bot`) enters EVERY closed ball around `0` in `ℤ₂` — for each `n` there is a
    quine whose 2-adic encoding lands in ball `n`. Computation reaches topology through the p-adic floor,
    the analogue of E2 for the computation domain (existential, since the quines are an unbounded family
    rather than a single sequence). -/
theorem quines_enter_every_ball (n : ℕ) :
    ∃ c, ZeroParadox.ZPK.IsComputationalQuine c ∧
      (2 : ℤ_[2]) ^ (Encodable.encode c) ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) := by
  obtain ⟨c, hc, hlt⟩ :=
    ZeroParadox.ZPK.quine_encodings_approach_bot ((2 : ℝ) ^ (-(n : ℤ))) (by positivity)
  refine ⟨c, hc, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt hlt

/-- EDGE information → topology (path via the floor): the information depth points `2ᵏ` (B3: surprisal-depth
    = 2-adic depth) eventually enter every ball around `0` in `ℤ₂`. Information reaches topology through the
    p-adic floor — the analogue of E2/E3 for the information domain. -/
theorem info_points_enter_every_ball (n : ℕ) :
    ∀ᶠ k in Filter.atTop, (2 : ℤ_[2]) ^ k ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) :=
  ZeroParadox.P8.two_pow_tendsto_zero.eventually (Metric.closedBall_mem_nhds 0 (by positivity))

/-- CORRESPONDENCE — co-location at the shared floor. Proof-theory (tower, B6), computation (quines, B2),
    and information (depth points, B3) ALL enter every ball around the single floor `0 ∈ ℤ₂`, via their real
    structural encodings. With E1 (ball = valuation sublevel) and `fB_bottom_is_limit` (⋂ balls = {0}), all
    of {proof, computation, information, topology, number-theory} co-locate at the one floor — the p-adic
    cluster as a COMPLETE correspondence subgraph (every pair meets at the floor). This is CORRESPONDENCE
    (agreement under the shared 2-adic encoding), NOT the identity claim "they are literally one object"
    (which stays the modeling commitment — the dotted ring on the map). The encodings are not designed to
    hit 0; they hit it because the bottoms are genuinely floors, so the co-location has content. -/
theorem padic_cluster_colocates_at_floor (n : ℕ) :
    (∀ᶠ k in Filter.atTop,
        ZeroParadox.P8.cnf_encode (ZeroParadox.P8.towerOrd k)
          ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ)))) ∧
    (∃ c, ZeroParadox.ZPK.IsComputationalQuine c ∧
        (2 : ℤ_[2]) ^ (Encodable.encode c) ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ)))) ∧
    (∀ᶠ k in Filter.atTop,
        (2 : ℤ_[2]) ^ k ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ)))) :=
  ⟨tower_enters_every_ball n, quines_enter_every_ball n, info_points_enter_every_ball n⟩

/-- CORRESPONDENCE information ↔ number-theory (strengthened B3): the 2-adic VALUATION of the depth-`n`
    information point `2ⁿ` equals its information SURPRISAL. A genuine cross-domain equation — a
    number-theoretic quantity (the valuation) and an information quantity (the surprisal) coincide — not two
    separate "= n" facts. (Still thin, since ZPC defines surprisal as the depth index; but it is an honest
    correspondence equation relating the two domains' measures, the info-side of the p-adic cluster.) -/
theorem info_valuation_eq_surprisal (n : ℕ) :
    (((2 : ℚ_[2]) ^ n).valuation : ℝ) = ZeroParadox.ZPC.surprisal n := by
  have hv : ((2 : ℚ_[2]) ^ n).valuation = (n : ℤ) := by
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_cast, Padic.valuation_pow, Padic.valuation_p,
      mul_one]
  rw [hv]
  simp [ZeroParadox.ZPC.surprisal]

/-- CORRESPONDENCE category-theory ↔ {topology, information, Hilbert}: each of those domains has a genuine
    categorical REALIZATION, and its snap bottom is a proven categorical object — the information and Hilbert
    bottoms are INITIAL objects (`fC_zero_isInitial`, `fD_zero_isInitial`), and the topology bottom is the
    inverse LIMIT of the ball system (`fB_bottom_is_limit`, `⋂ = {0}`). This is the MC-1 *correspondence*
    half (derived, not the identity commitment): category-theory connects DIRECTLY to the three realized
    domains, making it a second hub alongside the p-adic floor. Bundles existing witnesses. -/
theorem category_realizes_bottoms :
    Nonempty (CategoryTheory.Limits.IsInitial (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)) ∧
      Nonempty (CategoryTheory.Limits.IsInitial (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)) ∧
      (⋂ n, ZeroParadox.ZPH_TopFunctor.q2Ball n) = {(0 : Q₂)} :=
  ⟨⟨ZeroParadox.ZPH_InfoFunctor.fC_zero_isInitial⟩,
    ⟨ZeroParadox.ZPH_HilbFunctor.fD_zero_isInitial⟩,
    ZeroParadox.ZPH_TopFunctor.fB_bottom_is_limit⟩

end ZeroParadox.WebEdges

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.WebEdges
#print axioms q2Ball_eq_addValuation_sublevel
#print axioms tower_enters_every_ball
#print axioms quines_enter_every_ball
#print axioms info_points_enter_every_ball
#print axioms padic_cluster_colocates_at_floor
#print axioms info_valuation_eq_surprisal
#print axioms category_realizes_bottoms
end PurityCheck
