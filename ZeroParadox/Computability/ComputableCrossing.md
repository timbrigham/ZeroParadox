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
(`Nat.Partrec.Code.exists_code`) — the reflexive object. And Rogers' fixed-point theorem
(`Nat.Partrec.Code.fixed_point`) gives every total computable `f : Code → Code` a fixed point **up to
`eval`**: `∃ c, (f c).eval = c.eval`.

⚠ **THAT IS WEAKER THAN "no fixed-point-free total computable endomap", AND THE STRONG FORM IS FALSE.**
`fun c => Code.pair c c` is total, computable, and has no fixed point anywhere — pairing a code with
itself always makes it structurally larger. Rogers is an equality **under the `eval` quotient**: two
different programs computing the same function.

⚠ **So this is NOT the exact dual of `reflexive_object_refuted`**, which consumes *literal* `f x ≠ x` —
a precondition the witness above satisfies. The conclusion (Lawvere fires in the computable category)
still holds, for a reason about **which maps exist**, not about which types they land in:
`no_computable_evalFixedPointFree` shows no computable self-map on codes is eval-fixed-point-free, so
the diagonal that would refute the witness has no computable representative and the obstruction cannot
fire. The obstruction is absent **at the level of `eval`**, which is the level the reflexive object
lives at.

⚠ **NOT because `eval` lands in a different codomain.** That reading is refuted in one line —
`example : ¬ HasLawvereWitness (ℕ →. ℕ) := no_witness_of_nontrivial ...` elaborates, since the
partial-function type is nontrivial too. `eval_point_surjective` carries `Nat.Partrec f`: the
point-surjection reaches the *computable* partial functions only, never all of `ℕ →. ℕ`.

So Lawvere fires in the computable category, and the self-referential fixed point *exists* there:
Kleene's second recursion theorem (`fixed_point₂`), which is the framework's own Kleene fixed point
(`kleene_fixed_point_exists`, ZP-K).

## Prior art

That Kleene's recursion theorem is an instance of Lawvere's fixed-point theorem is standard — the
derivation is **Yanofsky (2003) Theorem 5 (The Recursion Theorem), printed p. 18**, within his unified
treatment. ⚠ **Lawvere (1969) does NOT derive it**, and should not be cited as doing so: his § 2 p. 9
raises it as an open question — *"Experts on recursive functions … may also wish to consider whether
the fixed-point theorem of section one has any applications in those cases."* Lawvere supplies the
engine; Yanofsky runs it at this face. The reflexive
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
