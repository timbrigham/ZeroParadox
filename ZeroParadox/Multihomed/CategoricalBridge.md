# The categorical bridge: key results, functor witnesses and the OQ-G3 status

Moved from `ZeroParadox/Multihomed/CategoricalBridge.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

Connects ZP-G (Category Theory) to ZP-A through ZP-E. Every cross-framework claim
is traced to a theorem in ZP-G or ZP-A through ZP-E, plus an explicit bridge axiom
where required. No floating connections.

Key results:
- T-H1: For each domain, the canonical initial element satisfies the relevant
  domain-specific extremality property.
  - F_A (ZPA/ZPE): fully categorical — ℕ with max/0 is a concrete ZPCategory instance
    (see NatSLat appendix); ⊥ satisfies the universal property of an initial object.
  - F_B: Q₂BallDepth appendix — concrete Functor ℕ → Q₂BallDepth (fb_functor),
    preserves initial object, snap grounded in C3. Concrete witness for F_B.
  - F_C: InfoDepth appendix — concrete Functor ℕ → InfoDepth (fc_functor),
    preserves initial object, snap grounded in T1b (JSD = log 2). Concrete witness for F_C.
  - F_D: HilbDimDepth appendix — concrete Functor ℕ → HilbDimDepth (fd_functor),
    preserves initial object, snap grounded in T4 (orthogonal shift). Concrete witness for F_D.
  OQ-G3 status: each F_B/F_C/F_D has a concrete depth-index witness here (a ZPCategory whose
  initial object is the snap floor). The full functors into the REAL domain categories are now
  built in the sibling files — fB_functor : ℕᵒᵖ ⥤ TopCat (ZeroParadox/Valuation/TopFunctor.lean), fD_functor :
  ℕ ⥤ ModuleCat ℂ (ZeroParadox/State/HilbFunctor.lean), fC_functor : ℕ ⥤ KleisliCat PMF (ZeroParadox/Multihomed/InfoFunctor.lean), bundled
  as mc1_correspondence (ZeroParadox/Multihomed/MC1Bridge.lean). Those supersede the ℕ-shaped depth proxies in this file.
  MC-1's correspondence half is thereby formal; the literal cross-category identity is retired as
  ill-typed (object equality across categories does not typecheck and is not invariant under equivalence); what
  separates the members is proved property by property (seam_unique_among_named, for the named bottoms).
- T-H2: Categorical singularity (domain-absent) and ZPC singularity (divergent
  accumulation) are compatible — jointly derivable (OQ-G4 closed).
- T-H3: Binary Snap described consistently under all four functors. Fully proved
  by assembling independently proved domain theorems.
