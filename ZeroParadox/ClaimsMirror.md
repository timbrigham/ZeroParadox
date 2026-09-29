# Claims that are not theorems: the faithful non-representation

Moved from `ZeroParadox/ClaimsMirror.lean` § VI. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## § VI. Claims that are NOT theorems (the faithful non-representation)

Three claim-graph nodes are, by their own recorded status, not Lean theorems. Representing them faithfully
means writing no theorem for them — the absence is the representation, and each absence is itself a checked
fact about the claim's status.

- `Lawvere-unification` (conj): "The diagonal fixed point keystone is a manifestation of Lawvere's
  fixed-point theorem." A conjectural cross-domain *connection*, not a single provable proposition (the
  claim graph marks it `conj`). Stated, never asserted; no theorem here.

- `Lawvere-set-comp` (conj): "the set-theoretic and computational diagonal fixed points are two faces of
  one Lawvere fixed point." Conjecture only — and the Set face is provably *not* a Lawvere instance (the
  Cantor obstruction), so this edge stays unbuilt. A theorem asserting it would be false; hence none.

- `MC-1-identity` (retired): "the four domain bottoms are numerically one object." Retired 2026-07-15 as
  ill-typed (object equality across categories does not typecheck and is not invariant under equivalence), so it
  cannot be stated in Lean at all. The non-representability *is* the finding: what separates the members is proved
  property by property (`seam_unique_among_named`, for the named bottoms, in a lattice with no top); only the shared diagonal shape survives, apophatically. No theorem here, by type.
