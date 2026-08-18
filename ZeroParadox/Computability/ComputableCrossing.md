# Where the obstruction is absent: the universal machine as a reflexive object

Argument, prior art and fence for `ZeroParadox/Computability/ComputableCrossing.lean`. The Lean file
holds the declarations, the Engineer's Take and the per-declaration glosses.

**Experimental probe** in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in `ZeroParadox/MANIFEST.md`.

## The setup

Sourcing ⊥ as a genuine Lawvere fixed point needs a **reflexive object** — a point-surjection onto a
function space — and Set refutes it (`reflexive_object_refuted`,
`ZeroParadox/Settheory/LawvereBridge.lean`), because Set has fixed-point-free maps (negation). The
escape is any regime with *no* fixed-point-free endomap. The monotone/domain regime is one
(Knaster–Tarski). This records the OTHER, which the framework already contains: the **computable**
regime.

## Why the computable regime crosses it

The universal machine `eval : Code → (ℕ →. ℕ)` is point-surjective onto the computable functions
(`Nat.Partrec.Code.exists_code`) — the reflexive object. And the computable world has **no
fixed-point-free total computable endomap**: Rogers' fixed-point theorem (`Nat.Partrec.Code.fixed_point`)
gives every total computable `f : Code → Code` a fixed point up to `eval`. That is exactly the
obstruction, absent — the dual of `reflexive_object_refuted`.

So Lawvere fires in the computable category, and the self-referential fixed point *exists* there:
Kleene's second recursion theorem (`fixed_point₂`), which is the framework's own Kleene fixed point
(`kleene_fixed_point_exists`, ZP-K).

## Prior art

That Kleene's recursion theorem is an instance of Lawvere's fixed-point theorem is standard — Lawvere
(1969) derives the recursion theorem; Yanofsky (2003) gives the unified treatment. The reflexive
structure of the computable category is studied as *Turing categories* / partial combinatory algebras —
Cockett–Hofstra; Longley.

## The crossing, stated honestly

The framework's Kleene fixed point IS the Lawvere fixed point in the reflexive computable structure
`eval` — the ν-side existence that Set (`reflexive_object_refuted`) forbids, realized where the
obstruction is absent.

This does **not** claim ⊥-*at-bottom* or uniqueness; those are the framework's separate identifications
(T-EXEC and the fork collapse). It crosses one specific inch, and the framework expedites that crossing
by already carrying the computable reflexive object. A Scott `D∞` domain would be a second route to the
same crossing; Mathlib lacks `D∞`, so that one is unbuilt and no longer needed.
