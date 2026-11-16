# The categorical bridge: key results, functor witnesses and the OQ-G3 status

Moved from `ZeroParadox/Multihomed/CategoricalBridge.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

Connects ZP-G (Category Theory) to ZP-A through ZP-E. Every cross-framework claim
is traced to a theorem in ZP-G or ZP-A through ZP-E, plus an explicit bridge axiom
where required. No floating connections.

Key results:
- T-H1: each instantiation has a domain fact stated beside it (`th1_fa` … `th1_fd`); initiality
  is a separate definition per Lean functor (`fb/fc/fd_preserves_initial`) that uses none of them.
  - F_A (ZPA/ZPE): no functor term. `th1_fa` is `bot_le` (⊥ of a ZPSemilattice lies below every
    element; no category is built on it). Separately, ℕ with max/0 is a concrete ZPCategory
    instance whose 0 is initial in `natOrderCat`, built from ℕ's ≤ (`natSLat_initial_grounding`,
    NatSLat appendix).
  - F_B: Q₂BallDepth appendix — concrete Functor ℕ → Q₂BallDepth (fb_functor); its image of 0
    is initial in that stand-in (`fb_preserves_initial`, `IsInitial.ofUnique 0`), beside C3. In
    `TopCat` the floor is terminal and not initial (`padic_bottom_not_initial`).
  - F_C: InfoDepth appendix — concrete Functor ℕ → InfoDepth (fc_functor); its image of 0 is
    initial in that stand-in (`fc_preserves_initial`), beside T1b (JSD = log 2).
  - F_D: HilbDimDepth appendix — concrete Functor ℕ → HilbDimDepth (fd_functor); its image of 0
    is initial in that stand-in (`fd_preserves_initial`), beside T4 (orthogonality).
  OQ-G3 status: each F_B/F_C/F_D has a concrete depth-index witness here (a ZPCategory on an
  ℕ-indexed newtype whose initial object is depth 0). The full functors into the REAL domain categories are now
  built in the sibling files — fB_functor : ℕᵒᵖ ⥤ TopCat (ZeroParadox/Valuation/TopFunctor.lean), fD_functor :
  ℕ ⥤ ModuleCat ℂ (ZeroParadox/State/HilbFunctor.lean), fC_functor : ℕ ⥤ KleisliCat PMF (ZeroParadox/Multihomed/InfoFunctor.lean), bundled
  as mc1_correspondence (ZeroParadox/Multihomed/MC1Bridge.lean). Those supersede the ℕ-shaped depth proxies in this file.
  MC-1's correspondence half is thereby formal; the literal cross-category identity is retired as
  ill-typed (object equality across categories does not typecheck and is not invariant under equivalence); what
  separates the members is proved property by property (seam_unique_among_named, for the named bottoms, in a lattice with no top).
- T-H2: Categorical singularity (domain-absent) and ZPC singularity (divergent
  accumulation) hold together: `th2_singularity_compatibility` pairs ZP-G Lemma T3
  (`t3_unreachability`) with ZP-C Theorem T2 (`t2_diverges`) and uses neither to prove the other (OQ-G4 closed in
  that sense).
- T-H3: `th3_snap_all_functors` conjoins four separately proved domain facts, of which only the
  first (`join c₀ c₁ = c₁`) mentions the snap; its type names no functor and relates no conjunct
  to another.
