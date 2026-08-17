import ZeroParadox.Computability.SelfApp
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic

/-!
# ZPJ — The well-foundedness boundary (keystone snap-as-boundary probe)

## Engineer's Take

Continuing to look at the shape of ZPJ, we pivoted from Lawvere to Taylor / AMM coalgebra. This was
mostly due to a gut reaction about the three failing cases, the original assessment, that they were
really the larger and more specific case for our framework. And if so, it gives the structure of our
binary snap an official home as a boundary crossing.

---

**Status: CORE (promoted 2026-07-29, Tim's call).** Formerly a probe; promoted because its results are
cited from `Settheory/Wall.lean` as the adoption site for the descending-chain characterization, and § I-b's
declarations are machine-verified with measured footprints. Rung A of the iterative A→B plan (see
`.claude-local/notes/wellfounded_coalgebra_foray_2026-06-23.md`) — Rung C, the full Taylor coalgebraic
statement, remains open and is **not** claimed here.

Conjecture (Taylor/AMM framing): the snap ⊥→ε₀ crosses the **well-foundedness boundary** —
from the non-well-founded floor (⊥ is the self-loop / back edge, where recursion cannot reach,
Taylor Prop 111) to the well-founded ascent (the ε₀ ordinal tower, recursively generated).

**Rung A (this file): the RELATION-LEVEL form.** Mathlib has `WellFounded` and ordinal well-foundedness
but NOT Taylor's coalgebraic well-founded coalgebras — so this is the faithful relation-level *shadow*
of the Taylor boundary, not the full coalgebraic statement (that is Rung C, deferred). Honest scope: this
proves "the self-application floor is non-well-founded; the ordinal ascent is well-founded; the snap
crosses between," at the level of relations.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice ZeroParadox

set_option maxHeartbeats 400000

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-! ## § I. The floor is non-well-founded (the back edge)

    `selfApp` has ⊥ as a fixed point (`fixed_bot`): ⊥ self-loops. The relation "a is the selfApp-image
    of b" therefore has a self-loop at ⊥, so it cannot be well-founded. -/

/-- The descent relation induced by `selfApp`: `a` is the self-application image of `b`. -/
def floorRel (a b : L) : Prop := AbstractSelfApp.selfApp b = a

/-- An accessible point cannot have a self-loop (well-founded relations are irreflexive). -/
private theorem acc_irrefl {α : Type*} {r : α → α → Prop} : ∀ {a : α}, Acc r a → ¬ r a a := by
  intro a h
  induction h with
  | intro x _ ih => intro hself; exact ih x hself hself

/-- **The floor is non-well-founded.** ⊥ self-loops under `selfApp` (`fixed_bot`), so `floorRel` has a
    self-loop at ⊥ and cannot be well-founded — the back edge. -/
theorem floor_not_wellFounded : ¬ WellFounded (floorRel (L := L)) := fun hwf =>
  acc_irrefl (hwf.apply bot) AbstractSelfApp.fixed_bot

/-! ## § I-b. The INFINITE-POLE reading of the same floor — an infinite descent, not merely a loop

§ I states the floor's non-well-foundedness as a **self-loop** (`r x x`) — the EMPTY-pole form: nothing
below ⊥, the loop goes nowhere. The two-pole hard rule (`CLAUDE.md`) asks where the zero that runs to
infinity is, and the library already supplies the answer: well-foundedness is equivalent to the absence of
an **infinite descending chain** (the descending-chain condition), so the same fact reads as *"an infinite
descent issues from the floor."* That is the INFINITE pole of ⊥ in this face, and it is the one § I hides.

Standard form, read at source in the pinned Mathlib (`v4.30.0-rc2`):
* `wellFounded_iff_isEmpty_descending_chain` (`Mathlib/Order/WellFounded.lean:51`) —
  `WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n+1)) (f n) }`.
* `not_acc_iff_exists_descending_chain` (`:34`) — `¬ Acc r x ↔ ∃ f, f 0 = x ∧ ∀ n, r (f (n+1)) (f n)`;
  the **pointwise** version, which is what "at the floor" needs.

**Purity — MEASURED 2026-07-29, and the measurement overturned the expectation. Read this before
adopting the standard form anywhere else.** Mathlib's *extract-a-chain* direction (`:36-38`) builds the
sequence with `.choose_spec`, so it carries `Classical.choice`. The natural inference — "supply the witness
yourself and use only the other direction, and you stay choice-free" — is **FALSE**, and was measured false
here: `#print axioms` follows the **statement**, so citing the *biconditional at all* pulls in the choice
used by the direction you did not take. Measured footprints:

* `floor_descent_from_bot` — **does not depend on any axioms.** The explicit descent at ⊥ is free.
* `bot_not_acc` — **axiom-free**, but only because it is proved BY HAND from `fixed_bot`. The one-line
  version via `not_acc_iff_exists_descending_chain.mpr` measured `[propext, Classical.choice, Quot.sound]`.
* `floor_not_wellFounded_via_descent` — `[propext, Classical.choice, Quot.sound]`, inherited from
  `wellFounded_iff_isEmpty_descending_chain`. § I's `floor_not_wellFounded` is **axiom-free** and remains
  the load-bearing statement.

So this follows the `CovBy` precedent exactly: **keep the hand proof, cite the standard name.** The DCC
route is retained below for the citation and the reading, not as the cheapest proof — and the framework's
own rule applies (`CLAUDE.md`): inert-in-the-proof and absent-from-the-footprint are different properties;
measure, never infer.

**FENCE — the constant chain is the DEGENERATE descent.** The witness here is `fun _ => bot`, i.e. the
self-loop re-read as a chain; it is the *smallest* infinite descent, not a rich one. A genuine
non-constant descent is strictly more, and does **not** follow from a self-loop — `Occurrence.lean`'s
§ IV-b table already records the non-implication ("infinite descent through distinct states has no
self-loop"). So this section converts the empty-pole form into the infinite-pole form at ⊥; it does not
claim the floor hosts a non-degenerate descent. -/

/-- The floor's descending chain: the constant sequence at ⊥. Explicit (no choice), and a descending
    chain for `floorRel` precisely because ⊥ is a fixed point of `selfApp` (`fixed_bot`). -/
def floorDescent : ℕ → L := fun _ => bot

/-- **The floor hosts an infinite descent FROM ⊥** — the infinite-pole reading, pointwise at the bottom.
    `Statement:` there is a sequence starting at ⊥ that descends under `floorRel` at every step. The
    witness is `floorDescent`, so this is choice-free.
    `Reading:` the bottom is not a still point with nothing under it; the same configuration is an
    unending descent. Empty pole and infinite pole, one object. -/
theorem floor_descent_from_bot :
    ∃ f : ℕ → L, f 0 = bot ∧ ∀ n, floorRel (f (n + 1)) (f n) :=
  ⟨floorDescent, rfl, fun _ => AbstractSelfApp.fixed_bot⟩

/-- **⊥ is not accessible** — the empty pole stated as inaccessibility. Proved by hand from `fixed_bot`
    (via this file's `acc_irrefl`), **axiom-free**.
    That this is *equivalent* to the descent above is Mathlib's `not_acc_iff_exists_descending_chain`
    (`Order/WellFounded.lean:34`) — cited, deliberately **not** used: routing through that biconditional
    puts `Classical.choice` in the footprint (measured — see the purity note in § I-b). So "unreachable
    from below" and "an infinite descent issues from it" are the same fact about ⊥ in the two charts, and
    both halves are available here without choice. -/
theorem bot_not_acc : ¬ Acc (floorRel (L := L)) bot :=
  fun h => acc_irrefl h AbstractSelfApp.fixed_bot

/-- **§ I's conclusion, re-derived by the infinite-descent route.** Same statement as
    `floor_not_wellFounded`; different witness — there the self-loop contradicts accessibility, here an
    explicit infinite chain contradicts the descending-chain condition. Kept as a distinct declaration
    because the *route* is the content: it is the citation to the standard DCC characterization. -/
theorem floor_not_wellFounded_via_descent : ¬ WellFounded (floorRel (L := L)) := by
  rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff]
  exact ⟨⟨floorDescent, fun _ => AbstractSelfApp.fixed_bot⟩⟩

/-! ### § I-c. The descent route, choice-free — and TWO separate sources of `Classical.choice`

    **No novelty is claimed for the mathematics; the delta is generality and purity.**

    *Prior art, one-directional forms included.* Mathlib has the equivalences as *biconditionals* —
    `not_acc_iff_exists_descending_chain` (`Order/WellFounded.lean:34`),
    `acc_iff_isEmpty_descending_chain` (`:42`), `wellFounded_iff_isEmpty_descending_chain` (`:51`) —
    **and it also has one-directional forms**: `RelEmbedding.natGT` (`Order/OrderIsoNat.lean:47`)
    takes the same hypothesis, with `RelEmbedding.not_acc` (`:64`) and
    `RelEmbedding.not_wellFounded` (`:76`) the closest named prior art. Two deltas remain, and the
    second is the substantive one:
    * *Purity.* Those forms all measure `[propext, Classical.choice, Quot.sound]`. The biconditional's
      `mp` builds the chain by `Nat.rec` over `{a // ¬ Acc r a}` with `.choose_spec` (`:36-38`), and
      a biconditional is **one constant whose proof term carries both directions** — so citing it at
      all pays for the direction you did not take. (Not "`#print axioms` follows the statement"; that
      rule is real but it is not the mechanism here.)
    * *Generality.* `RelEmbedding.not_acc` / `not_wellFounded` sit under `[IsStrictOrder α r]`, which
      **`floorRel` provably fails** — `floorRel bot bot` holds by `fixed_bot`, so the relation is not
      irreflexive. The lemmas below carry no order hypothesis at all, which is exactly what the floor
      needs. Same verdict as the `CovBy` and `bot_not_acc` precedents: **keep the hand proof, cite
      the standard name.**

    *Live adjacency in this corpus.* `real_carrier_not_wellFounded`
    (`ZeroParadox/Multihomed/TreeObstructions.lean`) already builds the non-constant descent
    `fun n : ℕ => -(n : ℝ)` — the ℝ twin of the ℤ chain measured below. It can now be re-proved by
    `not_wf_of_descent`.

    **The measurement (2026-08-03).** § I-b fences the constant witness: *"a genuine non-constant
    descent is strictly more."* It is strictly more — **and it is still free.** On an explicit
    non-constant chain (`f n = -n` on `ℤ` under `<`, every value distinct), the chain, its strict
    decrease, its injectivity and the resulting `¬ WellFounded` are all `[propext, Quot.sound]`, no
    choice. (Injectivity is choice-free via `omega`; the `neg_inj`/`Int.natCast_inj` route picks up
    choice through instance resolution — the instance hazard, again.) **This does NOT settle § I-b's
    own open question**, which is whether the *floor* hosts a non-degenerate descent; that remains
    open. What it settles is only that non-constancy as such is not what costs.

    **TWO SOURCES OF CHOICE, and they must not be conflated. The table below has been wrong twice;
    every row is now measured** — the first version collapsed the two into one, the second labelled
    `M.children` a *selection* when its dependency path is
    `M.children → Approx.head_succ' → Classical.byContradiction → Classical.propDecidable`, i.e. the
    same library-decidability node the towers reach. Its index `i` is an **explicit argument**, so
    nothing is extracted there:

    | case | successor nameable? | carrier clean? | cost | source |
    |---|---|---|---|---|
    | `f n = -n` on `ℤ` under `<` | yes | yes | **free** | — |
    | `towerOrd k` (`ZeroParadox/Ordinal/B6_CanonicalCNF.lean`) | yes | no | choice | **library** |
    | `ordinal_wf_padic_descent_clash` | yes | no | choice | **library** |
    | `PFunctor.M.children` | yes — `i` is an explicit argument | no | choice | **library** |
    | `not_acc_iff_exists_descending_chain.mp` | **no — the successor is only known to EXIST** | — | choice | **SELECTION** |

    So naming the successor is *necessary but not sufficient*: this corpus names its successors
    explicitly everywhere (`towerOrd k` → `towerOrd (k+1)`; `ordinalSuccession.seq k = Ordinal.epsilon k`
    in `ZeroParadox/Multihomed/SeparatedSuccession.lean`) and those still carry choice — **from the
    library, not from any selection**. Rows 2-4 all reach `Classical.choice` through the *same* node,
    `Classical.propDecidable`, which is why they are one source and not three.

    **The one genuine SELECTION is the biconditional's own `mp`, and it is already cited above.**
    `not_acc_iff_exists_descending_chain.mp` (`Mathlib/Order/WellFounded.lean:36-38`) builds its chain
    by `Nat.rec` over `{a // ¬ Acc r a}` using `(exists_not_acc_lt_of_not_acc a.2).choose_spec` — at
    each step a smaller inaccessible element is known only to **exist**, and one must be picked. Its
    `mpr` (`:39-40`) is `acc.rec` and needs nothing. That contrast — same theorem, one direction
    selecting and one not — is the cleanest exhibit of the distinction this section draws.

    ⚠ For `ordinal_wf_padic_descent_clash` (`ZeroParadox/Multihomed/CrossRootCompleteness.lean`) the
    carrier is `Ordinal` and `ℝ`, **not the p-adics** — its statement is
    `WellFounded (· < ·) ∧ StrictAnti (fun n : ℕ => (2:ℝ)^(-(n:ℤ)))`, p-adic in name only. Both
    conjuncts contribute: `Ordinal.lt_wf` carries choice, and so does the `ℝ` side by itself. An
    earlier version of this note cited `padicValNat`, which does not occur in that theorem's
    transitive closure at all.

    `Reading:` (framework interpretation, not a theorem) — the cost is not in *having* infinitely many
    distinct bottoms. Where a successor can be written down on a clean carrier, the infinitude is
    free; where it can only be *extracted* from an existence proof, the selection is unavoidable and
    that is what the axiom licenses. On this reading the framework's ordinal and analytic footprints
    are carrier inheritance — the position `CLAIMS.md` has always taken about the realization
    layers — rather than a price paid for the bottom being many. -/

/-- **Generic, axiom-free: no member of an explicit descending chain is accessible.**
    `Statement:` given any `f : ℕ → α` descending under `r` at every step, no `f n` is `Acc r`.
    The one-directional, choice-free half of Mathlib's `not_acc_iff_exists_descending_chain`. -/
theorem not_acc_of_descent {α : Type*} {r : α → α → Prop} (f : ℕ → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : ∀ x, Acc r x → ∀ n, x ≠ f n := by
  intro x hx
  induction hx with
  | intro y _ ih =>
    intro n hn
    subst hn
    exact ih (f (n + 1)) (hf n) (n + 1) rfl

/-- **Generic, axiom-free: an explicit descending chain refutes well-foundedness.**
    `Statement:` any explicitly given `f : ℕ → α` descending under `r` witnesses `¬ WellFounded r`.
    The choice-free half of `wellFounded_iff_isEmpty_descending_chain`; use this rather than the
    biconditional wherever the chain is written down, and the footprint stays clean. -/
theorem not_wf_of_descent {α : Type*} {r : α → α → Prop} (f : ℕ → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : ¬ WellFounded r := fun hwf =>
  not_acc_of_descent f hf (f 0) (hwf.apply (f 0)) 0 rfl

/-- **§ I's conclusion by the descent route, now CHOICE-FREE.**
    `Statement:` `¬ WellFounded floorRel` — the same statement as `floor_not_wellFounded_via_descent`
    and the same witness (`floorDescent`), but routed through `not_wf_of_descent` instead of the
    biconditional, so the descending-chain reading of the floor is available without paying for the
    direction not taken. Measured axiom-free, against that one's
    `[propext, Classical.choice, Quot.sound]`.
    `Reading:` the pair is kept deliberately — the choice-carrying version is retained because its
    *citation* of the standard characterization is its content, and the two side by side are the
    cleanest exhibit that the footprint here is a property of the ROUTE, not of the statement. -/
theorem floor_not_wellFounded_via_descent' : ¬ WellFounded (floorRel (L := L)) :=
  not_wf_of_descent floorDescent (fun _ => AbstractSelfApp.fixed_bot)

/-! ## § II. The ascent is well-founded (the ε₀ tower)

    The ordinal order is well-founded (ordinals are well-ordered); ε₀ and the snap ascent live inside it.
    This is the recursively-generated side — Taylor: well-founded ⟹ recursive. -/

/-- **The ascent is well-founded.** The strict order on ordinals is well-founded; the ε₀ tower (ZP-L)
    is an initial segment of it. -/
theorem ascent_wellFounded : WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  Ordinal.lt_wf

/-! ## § III. The boundary (Rung A statement)

    The snap crosses from the non-well-founded floor to the well-founded ascent. -/

/-- **Rung A — the well-foundedness boundary (relation level).** The floor relation is non-well-founded;
    the ascent relation is well-founded. The snap ⊥→ε₀ crosses between them. -/
theorem snap_crosses_boundary :
    ¬ WellFounded (floorRel (L := L)) ∧ WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  ⟨floor_not_wellFounded, ascent_wellFounded⟩

/-! ## § III-b. Oscillation — excluded on the ascent, MANDATORY at the floor

**This section states no new mathematics.** It instantiates `Settheory/Wall.lean`'s `wf_no_cycle`
(*"a well-founded relation has no cycle of ANY length … this also rules out 2-cycles"*) at the two ends of
§ III's boundary, and records the fence, which is the only non-obvious part. A **2-cycle `x → y → x` is an
oscillation**, so cycle-freeness is exactly the exclusion of liar-type flip-flop.

**The fence, and it is load-bearing.** `wf_no_cycle` needs **well-foundedness**, and the floor provably
does not have it (`floor_not_wellFounded`). So the exclusion holds on the ascent and **fails at the floor,
where a cycle is not merely permitted but present**: ⊥'s self-loop *is* a 1-cycle. So "the snap does not
oscillate" is true **above** the floor and false **at** it. Do not state it unqualified.

That is the μ/ν split once more: cycles excluded where the order is well-founded, cycles mandatory where it
is not. Prior art for the direct 2-cycle form is Mathlib's **`WellFounded.asymmetric`**
(`Mathlib/Order/RelClasses.lean:225`, `r a b → ¬ r b a`, with `asymmetric₃` at `:229`) — strictly stronger
than the self-loop form this corpus usually reaches for, and previously uncited here.

**Purity, measured 2026-07-30 (not predicted).** `floor_has_cycle` is **axiom-free** — the cycle at the
floor is exhibited by `fixed_bot` and needs nothing. `ascent_no_oscillation` and `oscillation_split` carry
`[propext, Classical.choice, Quot.sound]`, inherited from Mathlib's `Ordinal`, not from anything done here.
Note the direction that asymmetry runs: **exhibiting the floor's cycle is free; excluding cycles on the
ascent costs the ordinal library.** -/

/-- **No oscillation on the ascent.** No ordinal is reachable from itself by one-or-more `<`-steps, so the
    ε₀ ascent admits no cycle of any length — in particular no 2-cycle, i.e. no flip-flop between two
    ordinals. `Statement:` cycle-freeness of `<` on `Ordinal`, which is `wf_no_cycle` at
    `ascent_wellFounded`; proved directly here since `<` on ordinals is already transitive.

    **Prior art (cited, not reproved).** The inner step below — `TransGen (· < ·) a b → a < b` — is
    the forward direction of Mathlib's `Relation.transGen_eq_self` (`Mathlib/Logic/Relation.lean:594`,
    `[IsTrans α r] : TransGen r = r`), which `Ordinal` satisfies. The hand proof is kept per the
    `CovBy` precedent (keep the proof, cite the standard name); the footprint here is already
    `[propext, Classical.choice, Quot.sound]` from `Ordinal`, not from anything done here.
    The asymmetry route is `WellFounded.asymmetric` (`Mathlib/Order/RelClasses.lean`), whose
    `Std.Asymm` instance is registered for `IsWellFounded`. -/
theorem ascent_no_oscillation (o : Ordinal) :
    ¬ Relation.TransGen ((· < ·) : Ordinal → Ordinal → Prop) o o := by
  intro h
  have key : ∀ a b : Ordinal, Relation.TransGen (· < ·) a b → a < b := by
    intro a b hab
    induction hab with
    | single hlt => exact hlt
    | tail _ hlt ih => exact lt_trans ih hlt
  exact lt_irrefl o (key o o h)

/-- **A cycle at the floor — present, not merely permitted.** ⊥ is a fixed point of `selfApp`
    (`fixed_bot`), so `floorRel` relates ⊥ to itself and ⊥ lies on a 1-cycle. This is why
    `ascent_no_oscillation` cannot be extended downward: the hypothesis it needs is exactly what
    `floor_not_wellFounded` denies. -/
theorem floor_has_cycle :
    Relation.TransGen (floorRel (L := L)) ZPSemilattice.bot ZPSemilattice.bot :=
  Relation.TransGen.single AbstractSelfApp.fixed_bot

/-- **The oscillation split, in one statement.** Above the floor no cycle exists; at the floor one does.
    `Statement:` a conjunction of the two facts above, at two different relations on two different carriers.
    `Reading:` the framework's "the snap fires once and does not flip back" is the FIRST conjunct only — a
    statement about the ascent. The second conjunct is the floor's self-reference, and it is a cycle by
    construction. No cross-carrier identity is asserted; `Ordinal` and `L` are distinct types. -/
theorem oscillation_split (o : Ordinal) :
    ¬ Relation.TransGen ((· < ·) : Ordinal → Ordinal → Prop) o o
      ∧ Relation.TransGen (floorRel (L := L)) ZPSemilattice.bot ZPSemilattice.bot :=
  ⟨ascent_no_oscillation o, floor_has_cycle⟩

/-! ## § IV. Rung B — the snap as ONE crossing on a single carrier

    Glue the self-looping floor and the ordinal ascent into one carrier `Phase`, and show the
    non-well-foundedness is localized entirely at the floor: every post-snap state is accessible, the
    floor alone is not. The snap is the irreversible exit `floor ↦ up 0`.

    MODELING NOTE (honest): the carrier + relation are a *modeling choice* (how the floor, the ascent,
    and the irreversible snap are represented). Given that model the theorems below are proven — B2
    nontrivially, by ordinal well-founded induction. So "the snap is one crossing" is a faithful,
    coherent MODEL whose content is the two proven endpoints + an identification — and that
    identification is NOT a new commitment: it is the framework's existing ⊥/ε₀ identification (MC-1,
    plus the ε₀ identity already open under OQ-E2). The floor endpoint is tied to ZP's real ⊥
    (`floor_not_wellFounded`, axiom-free); the abstract `Phase` carrier is the illustrative toy form
    (non-well-foundedness localized at the floor by construction). No new commitment is introduced. -/

/-- The combined carrier: the self-looping floor, and the ordinal-indexed ascent. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Illustrative single-carrier model for the well-foundedness boundary — floor (self-looping ⊥) + up : Ordinal → Phase (ε₀ ascent); phaseRel self-loops at the floor, follows ordinal < above it, snap := up 0 is the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent. A modeling choice (content = two proven endpoints + the existing ⊥/ε₀ identification MC-1/OQ-E2, no new commitment); the real-⊥ endpoint (floorRel/floor_not_wellFounded) is axiom-free on the actual lattice.
inductive Phase where
  | floor : Phase
  | up : Ordinal → Phase

/-- The combined descent relation: the floor self-loops (non-well-founded); the ascent follows ordinal
    `<` (well-founded); no cross edges — the snap is irreversible, not a descent edge. -/
def phaseRel : Phase → Phase → Prop
  | Phase.floor, Phase.floor => True
  | Phase.up a, Phase.up b => a < b
  | _, _ => False

/-- The snap: the irreversible exit from the floor to the first ascent state. -/
def snap : Phase := Phase.up 0

/-- **B1 — the whole carrier is non-well-founded** (floor self-loop). -/
theorem phase_not_wellFounded : ¬ WellFounded phaseRel := fun hwf =>
  acc_irrefl (hwf.apply Phase.floor) trivial

/-- **B2 — every post-snap state is accessible** (the ascent is well-founded; non-wf localized off the
    ascent), by ordinal well-founded induction. -/
theorem phase_acc_of_up (o : Ordinal) : Acc phaseRel (Phase.up o) := by
  induction o using Ordinal.lt_wf.induction with
  | _ o ih =>
    refine Acc.intro _ (fun y hy => ?_)
    cases y with
    | floor => simp only [phaseRel] at hy
    | up a => exact ih a hy

/-- **B3 — the crossing.** The floor is the sole non-accessible point; every post-snap state is
    accessible. The snap exits the unique non-well-founded point into the well-founded ascent. -/
theorem snap_crossing :
    ¬ Acc phaseRel Phase.floor ∧ ∀ o : Ordinal, Acc phaseRel (Phase.up o) :=
  ⟨fun hacc => acc_irrefl hacc trivial, phase_acc_of_up⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms floor_not_wellFounded
#print axioms floor_descent_from_bot
#print axioms bot_not_acc
#print axioms floor_not_wellFounded_via_descent
-- § I-c: the same route WITHOUT the biconditional's inherited choice. Expected axiom-free.
#print axioms not_acc_of_descent
#print axioms not_wf_of_descent
#print axioms floor_not_wellFounded_via_descent'
#print axioms ascent_wellFounded
#print axioms ascent_no_oscillation
#print axioms floor_has_cycle
#print axioms oscillation_split
#print axioms phase_not_wellFounded
#print axioms phase_acc_of_up
#print axioms snap_crossing
end PurityCheck
