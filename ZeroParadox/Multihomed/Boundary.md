# Two poles of the floor, two sources of choice, and what the toy carrier models

Argument, measured footprints and fences for `ZeroParadox/Multihomed/Boundary.lean`. The Lean file
holds the declarations, the Engineer's Take and the per-declaration commentary.

## Status and scope

**CORE (promoted 2026-07-29, Tim's call).** Formerly a probe; promoted because its results are cited
from `ZeroParadox/Settheory/Wall.lean` as the adoption site for the descending-chain characterization,
and the infinite-pole declarations are machine-verified with measured footprints. Rung A of the
iterative A→B plan (`.claude-local/notes/wellfounded_coalgebra_foray_2026-06-23.md`) — Rung C, the full
Taylor coalgebraic statement, remains open and is **not** claimed.

Conjecture (Taylor/AMM framing): the snap ⊥→ε₀ crosses the **well-foundedness boundary** — from the
non-well-founded floor (⊥ is the self-loop / back edge, where recursion cannot reach, Taylor Prop 111)
to the well-founded ascent (the ε₀ ordinal tower, recursively generated).

**Rung A is the RELATION-LEVEL form.** Mathlib has `WellFounded` and ordinal well-foundedness but NOT
Taylor's coalgebraic well-founded coalgebras — so this is the faithful relation-level *shadow* of the
Taylor boundary, not the full coalgebraic statement. Honest scope: it proves "the self-application floor
is non-well-founded; the ordinal ascent is well-founded; the snap crosses between," at the level of
relations.

## The INFINITE-POLE reading of the same floor

The floor's non-well-foundedness stated as a **self-loop** (`r x x`) is the EMPTY-pole form: nothing
below ⊥, the loop goes nowhere. The two-pole hard rule (`CLAUDE.md`) asks where the zero that runs to
infinity is, and the library supplies the answer: well-foundedness is equivalent to the absence of an
**infinite descending chain**, so the same fact reads as *"an infinite descent issues from the floor."*
That is the INFINITE pole of ⊥ in this face, and the one the self-loop form hides.

Standard form, read at source in the pinned Mathlib (`v4.30.0-rc2`) — `Mathlib/Order/WellFounded.lean`:
* `wellFounded_iff_isEmpty_descending_chain` — `WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n+1)) (f n) }`.
* `not_acc_iff_exists_descending_chain` — `¬ Acc r x ↔ ∃ f, f 0 = x ∧ ∀ n, r (f (n+1)) (f n)`; the
  **pointwise** version, which is what "at the floor" needs.

**Purity — measured, and the measurement overturned the expectation. Read this before adopting the
standard form anywhere else.** Mathlib's *extract-a-chain* direction builds the sequence with
`.choose_spec`, so it carries `Classical.choice`. The natural inference — "supply the witness yourself
and use only the other direction, and you stay choice-free" — is **FALSE**, and was measured false here:
citing the *biconditional at all* pulls in the choice used by the direction you did not take. Measured
footprints:

* `floor_descent_from_bot` — **does not depend on any axioms.** The explicit descent at ⊥ is free.
* `bot_not_acc` — **axiom-free**, but only because it is proved BY HAND from `fixed_bot`. The one-line
  version via `not_acc_iff_exists_descending_chain.mpr` measured `[propext, Classical.choice, Quot.sound]`.
* `floor_not_wellFounded_via_descent` — `[propext, Classical.choice, Quot.sound]`, inherited from
  `wellFounded_iff_isEmpty_descending_chain`. The self-loop form `floor_not_wellFounded` is
  **axiom-free** and remains the load-bearing statement.

So this follows the `CovBy` precedent exactly: **keep the hand proof, cite the standard name.** The DCC
route is retained for the citation and the reading, not as the cheapest proof — and the framework's own
rule applies: inert-in-the-proof and absent-from-the-footprint are different properties; measure, never
infer.

**FENCE — the constant chain is the DEGENERATE descent.** The witness is `fun _ => bot`, the self-loop
re-read as a chain; it is the *smallest* infinite descent, not a rich one. A genuine non-constant descent
is strictly more, and does **not** follow from a self-loop — infinite descent through distinct states has
no self-loop, which `ZeroParadox/Computability/Occurrence.md` records under the bridge to
well-foundedness. So this converts the empty-pole form into the infinite-pole form at ⊥; it does not
claim the floor hosts a non-degenerate descent.

## The descent route, choice-free — and TWO separate sources of `Classical.choice`

**No novelty is claimed for the mathematics; the delta is generality and purity.**

*Prior art, one-directional forms included.* Mathlib has the equivalences as *biconditionals* —
`not_acc_iff_exists_descending_chain`, `acc_iff_isEmpty_descending_chain`,
`wellFounded_iff_isEmpty_descending_chain` (all `Mathlib/Order/WellFounded.lean`) — **and it also has
one-directional forms**: `RelEmbedding.natGT` (`Mathlib/Order/OrderIsoNat.lean`) takes the same
hypothesis, with `RelEmbedding.not_acc` and `RelEmbedding.not_wellFounded` the closest named prior art.
Two deltas remain, and the second is the substantive one:

* *Purity.* Those forms all measure `[propext, Classical.choice, Quot.sound]`. The biconditional's `mp`
  builds the chain by `Nat.rec` over `{a // ¬ Acc r a}` with `.choose_spec`, and a biconditional is
  **one constant whose proof term carries both directions** — so citing it at all pays for the direction
  you did not take. (Not "`#print axioms` follows the statement"; that rule is real but it is not the
  mechanism here.)
* *Generality.* `RelEmbedding.not_acc` / `not_wellFounded` sit under `[IsStrictOrder α r]`, which
  **`floorRel` provably fails** — `floorRel bot bot` holds by `fixed_bot`, so the relation is not
  irreflexive. The Lean file's lemmas carry no order hypothesis at all, which is exactly what the floor
  needs. Same verdict as the `CovBy` and `bot_not_acc` precedents: **keep the hand proof, cite the
  standard name.**

*Live adjacency in this corpus.* `real_carrier_not_wellFounded`
(`ZeroParadox/Multihomed/TreeObstructions.lean`) already builds the non-constant descent
`fun n : ℕ => -(n : ℝ)` — the ℝ twin of the ℤ chain measured below. It can be re-proved by
`not_wf_of_descent`.

**The measurement (2026-08-03).** The infinite-pole section fences the constant witness: *"a genuine
non-constant descent is strictly more."* It is strictly more — **and it is still free.** On an explicit
non-constant chain (`f n = -n` on `ℤ` under `<`, every value distinct), the chain, its strict decrease,
its injectivity and the resulting `¬ WellFounded` are all `[propext, Quot.sound]`, no choice.
(Injectivity is choice-free via `omega`; the `neg_inj`/`Int.natCast_inj` route picks up choice through
instance resolution — the instance hazard, again.) **This does NOT settle whether the *floor* hosts a
non-degenerate descent**; that remains open. What it settles is only that non-constancy as such is not
what costs.

### Two sources of choice, and they must not be conflated

Every row below is measured. `M.children`'s dependency path is
`M.children → Approx.head_succ' → Classical.byContradiction → Classical.propDecidable`, i.e. the same
library-decidability node the towers reach; its index `i` is an **explicit argument**, so nothing is
extracted there.

| case | successor nameable? | carrier clean? | cost | source |
|---|---|---|---|---|
| `f n = -n` on `ℤ` under `<` | yes | yes | **free** | — |
| `towerOrd k` (`ZeroParadox/Ordinal/B6_CanonicalCNF.lean`) | yes | no | choice | **library** |
| `ordinal_wf_padic_descent_clash` | yes | no | choice | **library** |
| `PFunctor.M.children` | yes — `i` is an explicit argument | no | choice | **library** |
| `not_acc_iff_exists_descending_chain.mp` | **no — the successor is only known to EXIST** | — | choice | **SELECTION** |

So naming the successor is *necessary but not sufficient*: this corpus names its successors explicitly
everywhere (`towerOrd k` → `towerOrd (k+1)`; `ordinalSuccession.seq k = Ordinal.epsilon k` in
`ZeroParadox/Multihomed/SeparatedSuccession.lean`) and those still carry choice — **from the library,
not from any selection**. Rows 2-4 all reach `Classical.choice` through the *same* node,
`Classical.propDecidable`, which is why they are one source and not three.

**The one genuine SELECTION is the biconditional's own `mp`.** `not_acc_iff_exists_descending_chain.mp`
builds its chain by `Nat.rec` over `{a // ¬ Acc r a}` using `(exists_not_acc_lt_of_not_acc a.2).choose_spec`
— at each step a smaller inaccessible element is known only to **exist**, and one must be picked. Its
`mpr` is `acc.rec` and needs nothing. That contrast — same theorem, one direction selecting and one not
— is the cleanest exhibit of the distinction.

⚠ For `ordinal_wf_padic_descent_clash` (`ZeroParadox/Multihomed/CrossRootCompleteness.lean`) the carrier
is `Ordinal` and `ℝ`, **not the p-adics** — its statement is
`WellFounded (· < ·) ∧ StrictAnti (fun n : ℕ => (2:ℝ)^(-(n:ℤ)))`, p-adic in name only. Both conjuncts
contribute: `Ordinal.lt_wf` carries choice, and so does the `ℝ` side by itself. `padicValNat` does not
occur in that theorem's transitive closure at all.

`Reading:` (framework interpretation, not a theorem) — the cost is not in *having* infinitely many
distinct bottoms. Where a successor can be written down on a clean carrier, the infinitude is free;
where it can only be *extracted* from an existence proof, the selection is unavoidable and that is what
the axiom licenses. On this reading the framework's ordinal and analytic footprints are carrier
inheritance — the position `CLAIMS.md` has always taken about the realization layers — rather than a
price paid for the bottom being many.

## Oscillation — excluded on the ascent, MANDATORY at the floor

**This states no new mathematics.** It instantiates `wf_no_cycle` (`ZeroParadox/Settheory/Wall.lean`) at
the two ends of the boundary and records the fence, which is the only non-obvious part. A **2-cycle
`x → y → x` is an oscillation**, so cycle-freeness is exactly the exclusion of liar-type flip-flop.

**The fence, and it is load-bearing.** `wf_no_cycle` needs **well-foundedness**, and the floor provably
does not have it (`floor_not_wellFounded`). So the exclusion holds on the ascent and **fails at the
floor, where a cycle is not merely permitted but present**: ⊥'s self-loop *is* a 1-cycle. So "the snap
does not oscillate" is true **above** the floor and false **at** it. Do not state it unqualified.

That is the μ/ν split once more: cycles excluded where the order is well-founded, cycles mandatory where
it is not. Prior art for the direct 2-cycle form is Mathlib's **`WellFounded.asymmetric`**
(`Mathlib/Order/RelClasses.lean`, `r a b → ¬ r b a`, with `asymmetric₃` beside it) — strictly stronger
than the self-loop form this corpus usually reaches for.

**Purity, measured 2026-07-30 (not predicted).** `floor_has_cycle` is **axiom-free** — the cycle at the
floor is exhibited by `fixed_bot` and needs nothing. `ascent_no_oscillation` and `oscillation_split`
carry `[propext, Classical.choice, Quot.sound]`, inherited from Mathlib's `Ordinal`, not from anything
done here. Note the direction that asymmetry runs: **exhibiting the floor's cycle is free; excluding
cycles on the ascent costs the ordinal library.**

## Rung B — what the single carrier models

Gluing the self-looping floor and the ordinal ascent into one carrier `Phase` shows the
non-well-foundedness is localized entirely at the floor: every post-snap state is accessible, the floor
alone is not. The snap is the irreversible exit `floor ↦ up 0`.

**MODELING NOTE (honest):** the carrier and relation are a *modeling choice* — how the floor, the
ascent, and the irreversible snap are represented. Given that model the theorems are proven, B2
nontrivially, by ordinal well-founded induction. So "the snap is one crossing" is a faithful, coherent
MODEL whose content is the two proven endpoints plus an identification — and that identification is NOT
a new commitment: it is the framework's existing ⊥/ε₀ identification (MC-1, plus the ε₀ identity already
open under OQ-E2). The floor endpoint is tied to ZP's real ⊥ (`floor_not_wellFounded`, axiom-free); the
abstract `Phase` carrier is the illustrative toy form, with non-well-foundedness localized at the floor
by construction. No new commitment is introduced.
