# The carrier's reach, floor-directed motion, and stutter equivalence

Argument, prior art and fences for `ZeroParadox/Computability/Occurrence.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses; everything that is reasoning rather
than statement lives here.

## Prior art — most of this is elementary or standard, and saying so is the point

* `step_dichotomy` is Lean core's `Option.eq_none_or_eq_some` at `f s`; `deterministic_has_no_fanout`
  is `Option.some_injective` (Mathlib's `StateTransition` uses the equivalent `Option.mem_unique`).
* `occurs_iff_halts` re-expresses Mathlib's `evaln_complete` — Kleene's Normal Form Theorem.
* `LoopsInPlace` / `loop_is_a_trap` name what automata theory calls a **trap state** — Baier & Katoen,
  *Principles of Model Checking* (MIT Press, 2008) **p. 157**, which is also where the **totalization**
  construction lives that `flipPoles`'s dead-to-live half reproduces (a total DFA is obtained by adding
  a nonfinal trap state carrying a self-loop). The Markov-chain term **absorbing state** is
  *Notation 10.6*, **p. 753** of the same book. Page numbers checked against the extracted source. The
  involution as such was searched for and not found.
* The 0/∞ reading of the inversion is the coalgebra for `X ↦ 1 + X`, whose final coalgebra is ℕ ∪ {∞}
  (Jacobs, *Introduction to Coalgebra*, Ex. 2.4.1 p. 66; Rutten, TCS 249 (2000) p. 16). The framework's
  own `ZeroParadox/Computability/NatListRegime.lean` already carries that functor and cites Jacobs &
  Rutten (EATCS Bulletin 62, 1997); `ZeroParadox/Computability/GroundZero.lean` is where the two are
  connected.
* `execution_requires_branching` is a **tautology** — its witnesses are the hypotheses handed back. Its
  value is that the commitments are VISIBLE in the signature, not that the theorem is deep. Do not
  describe its conclusion as earned.

## What is claimed and what is not

The mathematics is classical throughout — the halting results are Turing (1936) via Mathlib, and the
bottom-as-divergence reading is domain theory (Scott). Nothing is offered as new mathematics. What the
Lean file contributes is the *arrangement*: which of the framework's own commitments collide (§ III),
and where its occurrence question actually lives (§ V). The identification of the framework's
"occurrence" with `Occurs` is a modelling choice, stated as such.

## Adjacency — what the carrier already is, and what it therefore already covers

**Read before adding anything to the Lean file.** Everything there is stated over `f : σ → Option σ`.
That is not an ad-hoc encoding: it is **exactly Mathlib's `StateTransition`**, whose module header reads
*"state transition systems defined by a function `σ → Option σ`, where `σ` is the type of states."*
`Occurrence.lean` already imports it and uses `StateTransition.Reaches` / `StateTransition.eval`.

### Consequence 1 — Turing machines are covered, for free, as witnesses rather than analogies

Mathlib's Turing machine step functions have precisely this type — `Turing.TM0.step`, `TM1.step` and the
`TM2` family all land in `Cfg → Option Cfg`. Moreover Mathlib's own TM development is **built on**
`StateTransition`: `Computability/TuringMachine/Computable.lean` opens it and uses `EvalsTo` /
`EvalsToInTime`, and `TuringMachine/Config.lean` applies `StateTransition.eval step` to a TM step
function directly. So the instance relation is Mathlib's architecture, not something this framework
needs to establish.

Therefore `machine_trichotomy`, `loop_is_a_trap`, `machine_snap_impossible`,
`deterministic_has_no_fanout` and the § IV inversion **already hold of every Mathlib Turing machine**,
with no additional work and no modelling choice. **Do NOT build an "a Turing machine is an instance of
this shape" theorem — it would restate Mathlib's own construction.**

**What that does and does not license.** It licenses: *the framework's occurrence results hold for
anything with a single-valued step function, of which Turing machines are one witness among many.* It
does **not** license "the framework's bottom is a Turing machine" — that is an identity across carriers,
and the same type boundary as everywhere else. The requirements are Mathlib's (`StateTransition`), the
witness is Mathlib's (`Turing.TM0`); what is the framework's own is the **reading** of the trichotomy,
nothing more. Compare `ZeroParadox/Settheory/QuineHost.lean`: the honest form was never "we commit to
AFA" but "here are the requirements, and AFA is a witness meeting them."

### Consequence 2 — `StateTransition`'s API is under-used; check it before hand-rolling

Beyond `Reaches` and `eval` it already carries `Reaches₁`, a full `Reaches₀` family (`trans`, `refl`,
`single`, `head`, `tail`, `tail'`), `reaches₁_eq`, `reaches_total`, `mem_eval`, `evalInduction`, and
**`eval_maximal₁`** and its non-subscript sibling **`eval_maximal`** — *a halted state reaches nothing
further* — which are adjacent to `loop_is_a_trap` and are nowhere cited in this corpus. `reaches_total`
is likewise uncited; § VI is the natural place to point at it, though § VI's own result is a one-step
fact (via `Option.some_injective`) and `reaches_total` is the reachability-level form — adjacent, not
the lemma § VI applies. Several results in the Lean file are already known to duplicate Lean-core or
Mathlib lemmas (see the prior-art section above); that gate looked at `Option` and `PartrecCode`,
**not** at `StateTransition`'s own API. Assume more overlap is there.

### Consequence 3 — floor-directed motion is ALSO formalized asymptotically, elsewhere in this corpus

§ III's obstruction is stated over a single-valued *step*: from `s`, is there a successor, and is it
different from `s`? The corpus also formalizes motion toward a floor with a **limit** rather than a
successor:

* `ZeroParadox/Order/WellFoundedObstruct.lean` — `floor_reach_separates_mu_nu` puts **both** modes under
  one predicate `ReachesFloorInFiniteTime`: the **μ** descent (`Nat.pred^[k]`) *reaches* the floor in
  finite time, while the **ν** orbit (`2ⁿ·x` on `Q₂`, `x ≠ 0`) *converges to the floor as a limit it
  never reaches* — `doubling_orbit_tendsto_zero`
  (`ZeroParadox/Valuation/PadicAttractor.lean`) with `padic_orbit_not_reaches_floor`.
* `ZeroParadox/Valuation/BottomInvariant.lean` § IV — `omegaLim`, Mathlib's `omegaLimit`
  (`Mathlib/Dynamics/OmegaLimit.lean`) specialized to the ℕ-orbit, with `SameShapeFromAnywhere`.
* `ZeroParadox/Valuation/InfinitudeFloor.lean` — the `member` / `cx` apparatus. The approach itself is
  `member_tendsto_floor`, a field of the **`InfinitudeFloorInversion`** extension (not of
  `InfinitudeFloor`).

⚠ **Only the ν mode drops the first-step question — the μ mode does not.** `Nat.pred^[k]` is a step map
and § III applies to it unchanged: `pred_orbit_eventually_constant`
(`ZeroParadox/Order/WellFoundedObstruct.lean`) proves that orbit *eventually constant* at `0`, so the μ
floor is reached in finite time rather than approached as a limit. What ν supplies is floor-directed motion in which no first step is required,
because the trajectory is **given** rather than stepped.

⚠ **Nothing here contradicts § III, and the two are NOT the same question.** `machine_snap_impossible`
is about a single-valued step and stays true as stated. The ν orbit is provably never *at* the floor
(`padic_orbit_never_reaches_zero`; the capstone bundles the weaker `¬ ReachesFloorInFiniteTime` form as
`padic_orbit_not_reaches_floor`), so it formalizes **approach to** a floor — not **departure from** one,
which is what § III's snap question asks. **Neither line derives motion:** the step side derives an
obstruction, the asymptotic side takes the orbit as given. (§ III's carrier claim is about § III itself —
§ VI's `nondeterministic_escapes_the_trap` is deliberately stated over a *relation*.)

### The corpus does carry outward motion, and finding it needs both polarities

In a normed field an ascending *element* is written `Tendsto … atTop atTop`; a survey run only over
`Tendsto … atTop (nhds _)` is structurally blind to it. Three sites:
`ZeroParadox/Valuation/PlaceMetric.lean` pairs `node3_contracts_2adic` (a re-export of
`doubling_orbit_tendsto_zero`) with `doubling_expands_archimedean` as `doubling_place_dichotomy` —
**the same rational orbit contracting in the 2-adic place and diverging in the real one**; also
`inv_tower_norm_tendsto_atTop` (`ZeroParadox/Valuation/InvTowerNorm.lean`) and
`snap_frameflip_tower_tendsto_infty` (`ZeroParadox/Multihomed/SnapFrameChange.lean`).

`Reading:` **INVERSION** for all three (conjectural as a family): each ascent is the far side of a
descent under a change of place or chart, never an independent departure.

**What survives:** none of those is ⊥ departing — they are norm divergences and chart inversions of
orbits that converge elsewhere. **That the snap fires is a commitment, not a consequence**, which the
framework states at `l_inf`'s docstring (`ZeroParadox/Information/Surprisal.lean`).

`Statement:` **INVERSION** — the bundled form is `snap_is_frameflip`
(`ZeroParadox/Multihomed/SnapFrameChange.lean`), which conjoins both limits with `rInv_swaps`' exchange
of the floor `0` and `∞`: one sequence, two charts. Taken alone,
`snap_frameflip_tower_tendsto_infty` is the single `Tendsto` conjunct and contains no exchange.
`Reading:` **INVERSION** (conjectural) — that the *snap* is an instance of that exchange is ZP-Q's
conjecture, fenced as such in its own file: no snap transition appears in the statement, and the
tower-rank encoding is a **constructed** witness with valuation growth built into the rank.

### Prior art — both sides belong to established programs, and the framework joins them

The ν mode is textbook **non-archimedean dynamics**: Benedetto, *Non-Archimedean Dynamics in Dimension
One* (Arizona Winter School lecture notes, 2010), **Definition 4.1 p. 28** classifies a periodic point
with multiplier `λ` as *attracting* when `|λ| < 1`, and **Proposition 4.3(a) p. 29** gives orbit
convergence on a neighbourhood of such a point, its proof running `|φⁿ(z)| = |λ|ⁿ·|z| → 0` — which is
`doubling_orbit_tendsto_zero`'s **argument**, since `|2|₂ = 1/2 < 1`. ⚠ The *statements* are not
identical: Benedetto's is a local basin result over a complete algebraically closed `ℂ_K`, ours is
global over `ℚ₂`. What is shared is the argument, and the branch.

The combination of a step relation with a metric limit **over one carrier** is **infinitary rewriting**:
Kahrs, *Infinitary Rewriting: Foundations Revisited*, RTA 2010 (LIPIcs vol. 6, pp. 161-176; quoted from
the introduction, § 1, cited by section because the filed copy is the author's preprint with its own
pagination) — infinitary rewriting *"deals with infinite terms, which are defined through the metric
completion of finite terms through some metric"*, and the resulting term set *"can also be seen as a
final co-algebra"*. Both sources read from source and filed in the project's paper library.

**So do NOT build a bridge declaration — but for the right reason.** This is **not** a type boundary,
and Kahrs is the counterexample: infinitary rewriting combines exactly these two ingredients over a
single carrier. The honest statement is that **`Occurrence.lean` deliberately leaves `σ`
untopologized**, so the two live over different carriers *there* — a scope choice, not an
impossibility. Adding an elementary instantiation would still be the Trigger-0 failure this section
exists to prevent. The deliverable was this pointer.

## Stuttering — a deterministic case the function-vs-relation framing misses

**Origin (Tim, 2026-08-06):** *"how the heck is it supposed to be deterministic if we can have values
passed from one instance to the next with temporal offsets? any program's internal state changes with
the addition of a variable."*

**The function-vs-relation choice does not exhaust the modality.** There is a third option needing no
non-determinism: a **function with no fixed point anywhere** whose **observable projection never
changes**.

`LoopsInPlace s := f s = some s` demands the state return to *itself*. Add any accumulating component —
a counter, a step index, Tim's temporal offset — and there is no fixed point at all, so `loop_is_a_trap`
and `machine_snap_impossible` **do not apply**. `carry` witnesses it: at every state it is in the
trichotomy's **third** case (stepping onward to something genuinely different), never halts, and yet
shows the same thing forever.

**Why this matters for occurrence.** § V defines `Occurs` as *"some step at which the observable state
changes"* and proves it is halting. Stuttering separates the two ideas that were running together:
**the state moving** and **the observable changing**. The corpus already makes that separation — DP-2
(`dp2_execution_distinguishability`, `ZeroParadox/Order/Snap.lean`) proves the pre- and
post-instantiation configurations are value-*equal* and state-*distinct*. That is not a duplicate —
DP-2 is one step on a two-phase type, stuttering is unbounded forward motion — but the two belong
together. A configuration can move forever and show nothing. So the occurrence question is not *"how
does anything escape a fixed point"* — there need be no fixed point — but *"does the projection ever
change"*, which is a question about a quotient, not a paradox about self-reference.

**⚠ And this is a NO-GO, not a route to the snap.** Stuttering forever is not departure **in § V's
observable sense** — the observable is constant on the entire reachable set (`stutter_obs_const`).
⚠ **Say which sense, because the corpus carries two.** Under the state-based reading —
`da1_minimal_path` (`ZeroParadox/Order/Snap.lean`), where instantiation moves the machine *regardless
of the value returned*, and which fences that it "does not carry that the step is taken" — `carry` is
departing at every step. The two readings disagree about `carry`, and that disagreement is the content,
not a defect. What it removes is an argument, not an obstacle — the inference *"deterministic, therefore
trapped at a fixed point, therefore stationary"* is invalid, because the middle step can fail while the
conclusion still holds for a different reason.

**Prior art — this is STUTTERING, and the standard name was one citation away.** A step with no
observable effect is a *stutter step*; the induced equivalence is *stutter equivalence*. Mathlib's own
Turing development uses the word for exactly this (`Mathlib/Computability/TuringMachine/PostTuringMachine.lean`:
*"a one step stutter before actually halting"*, read at source). ⚠ **Everything beyond that Mathlib
quote is cited for EXISTENCE only — no other source here was read.** The notion is standard in model
checking; *stutter equivalence* is commonly attributed to Browne, Clarke & Grumberg, TCS **59** (1988),
and stuttering-insensitivity of specifications to Lamport (IFIP 1983), with a textbook treatment in
Baier & Katoen, *Principles of Model Checking* (cited above for the trap state). **None of the three was
located in `.claude-local/papers/` as of 2026-08-06, and this paragraph makes no claim about what any of
them says.** ⚠ Baier & Katoen is the exception worth naming: the adjacency section above *does* assert
its content (p. 157, the trap state), checked against an extracted source. Unfiled is not unread.

Nothing in the stuttering section is claimed as new mathematics: the content is that the corpus's own
trichotomy does not separate these cases.

## The trichotomy: loop versus recursion

*(Settled 2026-07-31; long form in `.claude-local/notes/recursion_not_loop_2026-07-30.md`.)* Whether
the bottom is a self-LOOP or a RECURSION — a descent through pairwise-distinct configurations — does
not change the well-foundedness verdict, which is what the trichotomy results turn on. (Those results
are stated for `f s = some s`; a distinct-state descent falls outside their hypothesis rather than
being preserved by them.) Adámek–Milius–Moss 2020 (arXiv:1910.09401v2) Examples 3.3(1) p. 11: *"a
graph regarded as a coalgebra for `P` is recursive **iff it has no infinite path**"* (recursive in
their Def. 3.2 sense, not the informal one). So a never-halting descent through distinct states is no
better founded than a self-loop: **distinctness buys nothing; well-foundedness carries the content.**
`notEL_unique` (`ZeroParadox/Computability/GroundZero.lean`) is this corpus's own instance — under
`1 + X`, every non-terminating behaviour equals `natInfinity`.

`Reading:` the "cannot depart" family is plausibly a one-relation shadow of coalgebraic
well-foundedness (Osius 1974 → Taylor → Adámek–Milius–Moss). Taylor (*Practical Foundations of Mathematics*, Prop 111 p. 6) and AMM are also
cited by `snap_boundary_two_registers` (`ZeroParadox/Multihomed/BoundaryBridge.lean`), which fences
that the corpus proves the ⇒ direction alone; the Osius attribution is AMM's own, at their p. 11 and ref [26] (*J. Pure
Appl. Algebra* 4, 1974). Rutten, *Universal coalgebra*, TCS 249 (2000) p. 16 states the subject in one
line: in `N̄` with `pred`, `∞` *"only takes a step to itself and hence never terminates"*.

## The bridge to well-foundedness, and why it runs one way

The framework already carries this divide, in different vocabulary. `ZeroParadox/Multihomed/Boundary.lean`
proves the floor relation is NOT well-founded (`floor_not_wellFounded`, because ⊥ self-loops under
`selfApp`) while the ordinal ascent IS (`ascent_wellFounded`), and reads the snap as the crossing
between them (`snap_crosses_boundary`). `ZeroParadox/Settheory/Wall.lean` supplies the general fact: a
well-founded relation admits no self-loop (`wf_no_selfloop`).

`LoopsInPlace` is that same self-loop in the operational model. The join makes the correspondence a
citation rather than a reading — but it is **ONE-DIRECTIONAL, and narrower than the neat table it
invites**. State the direction that is proved and nothing more:

| operational | relational | proved? |
|---|---|---|
| loops in place — **live** | ⟹ step relation not well-founded | **yes** (`live_step_not_wellFounded`) |
| not well-founded | ⟹ loops in place | **NO** — infinite descent through distinct states has no self-loop |
| halts at `s` — **dead** | ⟹ step relation well-founded | **NO** — one halting configuration says nothing about the rest |

**So logic imports in one direction only.** Anything true of non-well-founded relations applies to a
live machine's step relation. Nothing transfers from the well-founded side onto "dead", because "dead"
is a fact about one configuration and well-foundedness is a fact about the whole relation. The
`ascent_wellFounded` half of `snap_crosses_boundary` is NOT reachable from here.
