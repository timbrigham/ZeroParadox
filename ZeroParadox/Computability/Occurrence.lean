import ZeroParadox.Settheory.Wall
import Mathlib.Computability.StateTransition
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Tactic

/-!
# Occurrence — what it takes for the bottom to move, in the computational face

## Engineer's Take

My initial statement was that existence itself is a Turing machine. The active case here is
that claim, and we had not covered the others. We worked with the premise of the bottom being
empty, and the other reading is infinity. Anytime there is confusion like this we need to work
both concurrently, the bottom being empty and the bottom being infinity. Three possible routes
turns out to be binary, because the third is a self-referential object. What we end up with is
a version with continuing forward motion, the live one, along with a halted dead version. The
computability face takes the whole concept of the bottom and gives both, and that sounds very
familiar.

---

## Formal Overview (AI-assisted)

The framework's transition needs something to make it *happen*, and ZP-K does not supply it:
`da1_closed_concrete` proves `IsQuineAtom (bot : MachinePhase)` and mentions no `Code` and no
execution, while `l_inf`'s docstring states that the step from unbounded surprisal to forced
execution is an ontological bridge rather than a mathematical consequence. This file asks what
*can* be established about occurrence, and answers in the operational model.

The move that opens it is the two-pole test (CLAUDE.md): ZP-K models the computational bottom
as a **phase** (`MachinePhase.initial`, commented "machine exists; no instruction fetched") —
the EMPTY pole only. The INFINITE pole in computability is divergence. Modelled operationally
as `f : σ → Option σ` (`none` = halted, `some s'` = next configuration), both poles appear.

- § I   No "not yet started" state — it is absent from the type, not ruled out by argument
- § II  The trichotomy, and the third case IS the bottom (a fixed point of the step)
- § III The loop is a trap — and the resulting NO-GO
- § IV  The inversion: the dead bottom yields, the live bottom withholds
- § V   Occurrence is halting, hence undecidable; non-occurrence is not even semi-decidable

**Prior art (added 2026-07-27, from the review of this file).** Most of what follows is
elementary or standard, and saying so is the point:
* `step_dichotomy` is Lean core's `Option.eq_none_or_eq_some` at `f s`;
  `deterministic_has_no_fanout` is `Option.some_injective` (Mathlib's `StateTransition` uses the
  equivalent `Option.mem_unique` for this).
* `occurs_iff_halts` re-expresses Mathlib's `evaln_complete` — Kleene's Normal Form Theorem.
* `LoopsInPlace` / `loop_is_a_trap` name what automata theory calls a **trap state** — Baier &
  Katoen, *Principles of Model Checking* (MIT Press, 2008) **p. 157**, which is also where the
  **totalization** construction lives that `flipPoles`'s dead-to-live half reproduces (a total DFA
  is obtained by adding a nonfinal trap state carrying a self-loop). The Markov-chain term
  **absorbing state** is *Notation 10.6*, **p. 753** of the same book. (Page numbers corrected
  2026-07-29 against the extracted source: an earlier revision cited p. 157 for the absorbing
  state and p. 97 for totalization; both were wrong.) The involution as such was searched for and
  not found.
* § IV's 0/∞ reading is the coalgebra for `X ↦ 1 + X`, whose final coalgebra is ℕ ∪ {∞}
  (Jacobs, *Introduction to Coalgebra*, Ex. 2.4.1 p. 66; Rutten, TCS 249 (2000) p. 16). The
  framework's own `NatListRegime.lean` already carries that functor and cites Jacobs & Rutten
  (EATCS Bulletin 62, 1997); `GroundZero.lean` is where the two are finally connected.
* `execution_requires_branching` is a **tautology** — its witnesses are the hypotheses handed
  back. Its value is that the commitments are VISIBLE in the signature, not that the theorem is
  deep. Do not describe its conclusion as earned.

**What is claimed and what is not.** The mathematics is classical throughout — the halting
results are Turing (1936) via Mathlib, and the bottom-as-divergence reading is domain theory
(Scott). Nothing here is offered as new mathematics. What this file contributes is the
*arrangement*: which of the framework's own commitments collide (§ III), and where its
occurrence question actually lives (§ V). The identification of the framework's "occurrence"
with `Occurs` is a modelling choice, stated as such.
-/

namespace ZeroParadox

/-! ## § 0. ADJACENCY — what this file's carrier already is, and what it therefore already covers

**Read before adding anything to this file.** Everything below is stated over `f : σ → Option σ`. That is
not an ad-hoc encoding: it is **exactly Mathlib's `StateTransition`**, whose module header reads *"state
transition systems defined by a function `σ → Option σ`, where `σ` is the type of states."* This file
already imports it and uses `StateTransition.Reaches` / `StateTransition.eval`.

**Consequence 1 — Turing machines are covered, for free, as witnesses rather than analogies.** Mathlib's
Turing machine step functions have precisely this type:
`Turing.TM0.step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ)`
(`Mathlib/Computability/TuringMachine/PostTuringMachine.lean:159`), likewise `TM1.step` (`:349`) and the
`TM2` family. Moreover Mathlib's own TM development is **built on** `StateTransition` — `TuringMachine/
Computable.lean:38` opens it and uses `EvalsTo` / `EvalsToInTime`; `TuringMachine/Config.lean:566,576`
applies `StateTransition.eval step` to a TM step function directly. So the instance relation is Mathlib's
architecture, not something this framework needs to establish.

Therefore `machine_trichotomy`, `loop_is_a_trap`, `machine_snap_impossible`,
`deterministic_has_no_fanout` and the § IV inversion **already hold of every Mathlib Turing machine**, with
no additional work and no modelling choice. **Do NOT build an "a Turing machine is an instance of this
shape" theorem — it would restate Mathlib's own construction.**

**What that does and does not license.** It licenses: *the framework's occurrence results hold for anything
with a single-valued step function, of which Turing machines are one witness among many.* It does **not**
license "the framework's bottom is a Turing machine" — that is an identity across carriers, and the same
type boundary as everywhere else. The requirements are Mathlib's (`StateTransition`), the witness is
Mathlib's (`Turing.TM0`); what is this file's own is the **reading** of the trichotomy, nothing more.
Compare `Settheory/QuineHost.lean`: the honest form was never "we commit to AFA" but "here are the
requirements, and AFA is a witness meeting them."

**Consequence 2 — `StateTransition`'s API is under-used here; check it before hand-rolling.** Beyond
`Reaches` and `eval` it already carries `Reaches₁`, a full `Reaches₀` family (`trans`, `refl`, `single`,
`head`, `tail`, `tail'`), `reaches₁_eq`, `reaches_total`, `mem_eval`, `evalInduction`, and
**`eval_maximal₁`** and its non-subscript sibling **`eval_maximal`** — *a halted state reaches nothing
further* — which are adjacent to `loop_is_a_trap` and are nowhere cited in this corpus. `reaches_total`
is likewise uncited; § VI is the natural place to point at it, though § VI's own result is a
one-step fact (via `Option.some_injective`) and `reaches_total` is the reachability-level form —
adjacent, not the lemma § VI applies. Several results in this file are already known to
duplicate Lean-core or Mathlib lemmas (see the header's prior-art block); that gate looked at `Option` and
`PartrecCode`, **not** at `StateTransition`'s own API. Assume more overlap is there. -/

/-! ## § I. A machine is never "not yet started" -/

variable {σ : Type*} (f : σ → Option σ)

/-- From any configuration a machine has either halted or has a next configuration. There is
    no third case, and in particular no "exists but has not begun". A fact about the type
    `σ → Option σ`, not an assumption added to it. -/
theorem step_dichotomy (s : σ) : f s = none ∨ ∃ s', f s = some s' := by
  cases h : f s
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- A machine that has not halted is, right now, taking a step. "Already running" is not an
    interpretation laid over the model; it is what not-halted means here. -/
theorem not_halted_means_stepping (s : σ) (h : f s ≠ none) : ∃ s', f s = some s' :=
  (step_dichotomy f s).resolve_left h

/-- There is no unstarted state: not-halted and no-next-configuration cannot both hold.
    This is the case DA-1 rejects when it says ⊥ is not a static description awaiting an
    external executor — here it is not rejected by argument, it is absent from the type. -/
theorem no_unstarted_state (s : σ) : ¬ (f s ≠ none ∧ ¬ ∃ s', f s = some s') := by
  rintro ⟨hne, hnex⟩
  exact hnex (not_halted_means_stepping f s hne)

/-! ## § II. The trichotomy — and the third case is the bottom

*(Settled 2026-07-31; long form in `.claude-local/notes/recursion_not_loop_2026-07-30.md`.)* Whether
the bottom is a self-LOOP or a RECURSION — a descent through pairwise-distinct configurations — does
not change the well-foundedness verdict, which is what the results below turn on. (Those results are
stated for `f s = some s`; a distinct-state descent falls outside their hypothesis rather than being
preserved by them.) Adámek–Milius–Moss 2020 (arXiv:1910.09401v2) Examples 3.3(1) p. 11: *"a
graph regarded as a coalgebra for `P` is recursive **iff it has no infinite path**"* (recursive in
their Def. 3.2 sense, not the informal one). So a never-halting descent through distinct states is no
better founded than a self-loop: **distinctness buys nothing; well-foundedness carries the content.**
`notEL_unique` (`ZeroParadox/Computability/GroundZero.lean`) is this corpus's own instance — under
`1 + X`, every non-terminating behaviour equals `natInfinity`.

`Reading:` the "cannot depart" family below is plausibly a one-relation shadow of coalgebraic
well-foundedness (Osius 1974 → Taylor → Adámek–Milius–Moss). Taylor and AMM are already cited at
`ZeroParadox/Multihomed/BoundaryBridge.lean` (§ "Scope fence — why this is NOT the full Taylor
coalgebraic statement"); the Osius attribution is AMM's own, at their
p. 11 and ref [26] (*J. Pure Appl. Algebra* 4, 1974). Rutten, *Universal coalgebra*,
TCS 249 (2000) p. 16 states this file's subject in one line: in `N̄` with `pred`, `∞` *"only takes a
step to itself and hence never terminates"*. -/

/-- Running in place: a self-looping configuration. Never halts, never changes.
    Note this is `s` being a **fixed point of the step function** — the same shape as
    `AbstractSelfApp.fixed_bot`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: names the self-looping configuration of a state-transition function as a first-class predicate, so the trichotomy below and the trap result can be stated about it. Mathlib has `Reaches`/`eval` but no name for "steps to itself".
def LoopsInPlace (s : σ) : Prop := f s = some s

/-- The exhaustive cases at a single configuration: halted, looping in place, or stepping
    onward. The middle case is not a third route — it is the self-referential object itself.

    **Read this before asking how the first two cases differ — it is the question this file gets asked
    most, and the answer lives five sections away in § VI.**

    All three are distinct **as states**: `f s = none`, `f s = some s`, and `f s = some s'` with
    `s' ≠ s` are different facts under any dynamics. But under a **FUNCTION** the first two share a
    **FATE**: `loop_is_a_trap` and `eval_of_halted` each give a *singleton* reachable set, so halted
    and self-looping both go nowhere and are terminal alike. Only under a **RELATION** can the
    self-loop retain the possibility of moving — `nondeterministic_escapes_the_trap` exhibits a
    relation where `s` loops **and** reaches something else.

    So "could this still move?" is a **modal** question, and within this trichotomy the framework
    encodes that modality as the **function-vs-relation choice**.

    ⚠ **But "nothing else" would be too strong, and an earlier version of this line said it.** § VI-c
    exhibits a deterministic case: a function with **no fixed point anywhere** whose observable
    projection never changes (`carry`). `LoopsInPlace` demands the state return to *itself*; add any
    accumulating component and there is no fixed point, so § III's results do not apply. Such a state
    is in the THIRD case at every step and still shows nothing forever. The trichotomy sorts states,
    not observables. That is why § III's NO-GO is powered by
    determinism rather than by the self-loop (§ VI states it: *"the obstruction of § III is the absence
    of fan-out, not the presence of a fixed point"*), and why the trichotomy is genuinely three-valued
    **only** in the non-deterministic setting — make the step single-valued and the **self-loop** is
    a relabelled trap. ⚠ **Not the third case** — § VI-c's `carry` is in the third case at every
    state, under a function, with an infinite reachable set. Cases 1 and 2 share a fate under a
    function; case 3 does not. -/
theorem machine_trichotomy (s : σ) :
    f s = none ∨ LoopsInPlace f s ∨ ∃ s', f s = some s' ∧ s' ≠ s := by
  unfold LoopsInPlace
  rcases step_dichotomy f s with h | ⟨s', h⟩
  · exact Or.inl h
  · by_cases hs : s' = s
    · subst hs; exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨s', h, hs⟩)

/-! ## § III. The loop is a trap — and the NO-GO that follows -/

/-- A self-looping configuration can never be left: everything reachable from it is it. -/
theorem loop_is_a_trap {s t : σ} (hloop : LoopsInPlace f s)
    (h : StateTransition.Reaches f s t) : t = s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      rw [hloop] at hstep
      exact (Option.mem_some_iff.mp hstep).symm

/-- The requirements ZP-K places on the computational bottom, stated over one machine: it is
    the fixed point of its own step (the live, self-referential reading), and the snap departs
    from it. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: bundles the framework's own two requirements on the computational bottom so their joint satisfiability can be decided. Framework-specific by construction; no Mathlib notion corresponds.
structure IsComputationalBottom (s : σ) : Prop where
  /-- The live reading: `s` is a fixed point of the dynamics. -/
  fixed : f s = some s
  /-- The snap: something reachable from `s` is not `s`. -/
  departs : ∃ t, StateTransition.Reaches f s t ∧ t ≠ s

/-- **NO-GO.** The two requirements are jointly unsatisfiable: no single deterministic machine
    hosts a bottom that is both its own fixed point and departed from. The same shape as
    `f_snap_impossible` (no snap in an ordered field), now for machines.

    This says which commitment has to give, not that the framework is wrong. Its own answer
    lies elsewhere — the arc returns to a *different instantiation* (DA-2), which denies the
    single-machine premise rather than either of the two requirements. -/
theorem machine_snap_impossible (s : σ) : ¬ IsComputationalBottom f s := by
  rintro ⟨hfix, t, hreach, hne⟩
  exact hne (loop_is_a_trap f hfix hreach)

/-! ## § IV. The inversion — the dead bottom yields, the live bottom withholds -/

/-- A halted configuration evaluates, to itself. The DEAD bottom yields a value. -/
theorem eval_of_halted (s : σ) (h : f s = none) : s ∈ StateTransition.eval f s :=
  StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h⟩

/-- A self-looping configuration has an empty evaluation. The LIVE bottom yields nothing. -/
theorem eval_of_loop_is_empty (s : σ) (hloop : LoopsInPlace f s) :
    ∀ b, b ∉ StateTransition.eval f s := by
  intro b hb
  obtain ⟨hreach, hnone⟩ := StateTransition.mem_eval.mp hb
  have hbs : b = s := loop_is_a_trap f hloop hreach
  subst hbs
  rw [hloop] at hnone
  exact absurd hnone (by simp)

/-- The inversion in one statement: the bottom that has stopped gives you something; the
    bottom that never stops gives you nothing. Halting and looping are the 0 and ∞ readings of
    the computational bottom, and what each *yields* is the opposite of what it *is*.

    **Fence:** a shared shape, not a Lean identity. Nothing here equates a machine
    configuration with a 2-adic point; the type boundary is not crossed. -/
theorem dead_yields_live_withholds (s : σ) :
    (f s = none → s ∈ StateTransition.eval f s) ∧
    (LoopsInPlace f s → ∀ b, b ∉ StateTransition.eval f s) :=
  ⟨eval_of_halted f s, eval_of_loop_is_empty f s⟩

/-- What survives when the departure requirement is dropped: a coherent object. The bottom is
    the live fixed point, it is a trap, and it yields nothing. It simply never snaps. -/
theorem the_live_bottom_is_coherent (s : σ) (hfix : f s = some s) :
    LoopsInPlace f s ∧ (∀ t, StateTransition.Reaches f s t → t = s)
      ∧ (∀ b, b ∉ StateTransition.eval f s) :=
  ⟨hfix, fun _ h => loop_is_a_trap f hfix h, eval_of_loop_is_empty f s hfix⟩

/-- **BOTH POLES AT ONCE — across charts, at the self-referential point.**

    A self-looping configuration is simultaneously **ZERO** in the output chart (its evaluation
    is empty: it yields nothing) and **INFINITY** in the step chart (it never halts: it runs
    forever). The readings do not conflict, because they are different measurements of one
    object.

    This is the computability face's version of the framework's pole coincidence. The
    valuation face's is `pole_inversion` (`Valuation/InfinitudeFloor.lean`): one sequence
    converging to the floor while its complexity ascends to `⊤`.

    **Note what this does NOT contradict.** Halted and looping are exclusive *within the step
    chart* — `f s` is single-valued, and no amount of non-determinism changes that (halting
    means no successor, looping means a successor). The coincidence is across charts, never
    inside one. -/
theorem selfloop_is_zero_and_infinity (s : σ) (h : LoopsInPlace f s) :
    (∀ b, b ∉ StateTransition.eval f s) ∧ (f s ≠ none) := by
  refine ⟨eval_of_loop_is_empty f s h, ?_⟩
  rw [h]; simp

/-! ## § IV-b. The bridge — live/dead has the SHAPE of the well-foundedness divide (one direction)

The framework already carries this divide, in different vocabulary. `Multihomed/Boundary.lean`
proves the floor relation is NOT well-founded (`floor_not_wellFounded`, because ⊥ self-loops
under `selfApp`) while the ordinal ascent IS (`ascent_wellFounded`), and reads the snap as the
crossing between them (`snap_crosses_boundary`). `Settheory/Wall.lean` supplies the general
fact: a well-founded relation admits no self-loop (`wf_no_selfloop`).

`LoopsInPlace` is that same self-loop in the operational model. The join below makes the
correspondence a citation rather than a reading — but it is **ONE-DIRECTIONAL, and narrower
than the neat table it invites**. State the direction that is proved and nothing more:

| operational (here) | relational | proved? |
|---|---|---|
| loops in place — **live** | ⟹ step relation not well-founded | **yes** (`live_step_not_wellFounded`) |
| not well-founded | ⟹ loops in place | **NO** — infinite descent through distinct states has no self-loop |
| halts at `s` — **dead** | ⟹ step relation well-founded | **NO** — one halting configuration says nothing about the rest |

**So logic imports in one direction only.** Anything true of non-well-founded relations applies
to a live machine's step relation. Nothing transfers from the well-founded side onto "dead",
because "dead" is a fact about one configuration and well-foundedness is a fact about the whole
relation. The `ascent_wellFounded` half of `snap_crosses_boundary` is NOT reachable from here. -/

/-- **The bridge — ONE DIRECTION ONLY.** A live (self-looping) configuration makes the machine's
    step relation non-well-founded — the same obstruction `floor_not_wellFounded` records for
    `selfApp`.

    **That single implication is all that is proved.** The converse fails, and "dead" does NOT
    yield a well-founded relation: `eval_of_halted` is about ONE configuration while
    well-foundedness is a property of the whole relation, and the `ascent_wellFounded` half of
    `snap_crosses_boundary` is not reachable from here (see the note above). So this is the same
    SHAPE as the framework's ν/μ divide seen at a different level — never an identity between
    them, and never a licence to run a ν/μ argument on the step relation. -/
theorem live_step_not_wellFounded (s : σ) (hloop : LoopsInPlace f s) :
    ¬ WellFounded (fun a b : σ => b ∈ f a) := by
  intro hwf
  exact wf_no_selfloop hwf s (by rw [hloop]; rfl)

/-- The inversion of § IV, read through the bridge — stated at the level where the vocabulary
    actually applies. The live branch is relational: a self-loop makes the **whole step
    relation** non-well-founded (the ν / corecursion side), and such a configuration yields
    nothing. The dead branch is only that a halted configuration yields its value — **not** a
    claim that the relation is well-founded, which one halting configuration cannot establish
    (see the § IV-b note; "recursive"/"corecursive" are properties of the coalgebra, never of a
    single state). So this is the one proved direction of the recursion/corecursion divide
    (Taylor; Adámek-Milius-Moss, cited in the CLAIMS convergence ledger), and it is why the dead
    bottom gives something while the live one withholds. -/
theorem inversion_is_the_wf_divide (s : σ) :
    (f s = none → s ∈ StateTransition.eval f s) ∧
    (LoopsInPlace f s → ¬ WellFounded (fun a b : σ => b ∈ f a)
        ∧ ∀ b, b ∉ StateTransition.eval f s) :=
  ⟨eval_of_halted f s, fun h => ⟨live_step_not_wellFounded f s h, eval_of_loop_is_empty f s h⟩⟩

/-- **A second limit on what the bridge carries: self-loops need NOT be unique.** A machine can
    fix two distinct configurations, so its step relation is not a `QuineHost`-shaped object —
    the uniqueness clause fails. Non-well-foundedness transfers; Quine-atom *uniqueness* does
    not, and no argument from ZP-J's uniqueness may be run on a machine's step relation. -/
theorem loops_not_unique : ∃ g : Bool → Option Bool, ∃ a b : Bool,
    LoopsInPlace g a ∧ LoopsInPlace g b ∧ a ≠ b :=
  ⟨fun x => some x, true, false, rfl, rfl, by decide⟩

/-! ## § IV-c. The pole swap — the inversion, at the level of machines

`Miniature.lean` § IV carries `swap_involutive` and `collapse_irreversible` over the
two-element pole. The computational pole (halted / loops-in-place) carries the same pair. The
involution below has `rInv`'s full signature: it fixes an interior, preserves the pole as a
set, and exchanges its two elements.

**Level fence (load-bearing).** `rInv` is an automorphism *of the sphere* — one object moved
within itself. `flipPoles` is an automorphism *of the space of machines*: a halting machine
and its flip behave differently and are not one machine seen twice. So this is the same
**shape** at a different **level**, a further member of the family (MC-1), never an identity.
No cross-type `=` is asserted or available. -/

section PoleSwap

variable [DecidableEq σ]

/-- A configuration is EXTREMAL when it sits at one of the two poles: halted, or looping in
    place. Everything else makes progress. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: names the two-element computational pole (halted or self-looping) as a predicate so the swap below can be shown to preserve it as a set. Mathlib has no notion of "at one of the two extremes of a state-transition function".
def Extremal (s : σ) : Prop := f s = none ∨ LoopsInPlace f s

/-- Exchange the poles: halted becomes a self-loop, a self-loop becomes halted, and a
    configuration that steps onward is left alone. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the computational analogue of `rInv` / `swap` — an involution on step functions exchanging the halted and self-looping poles while fixing the interior. Mathlib has no such operation on `σ → Option σ`.
def flipPoles (g : σ → Option σ) : σ → Option σ := fun s =>
  if g s = none then some s else if g s = some s then none else g s

/-- Doing it twice is the identity — the same property `swap_involutive` records for the
    four-corner pole. -/
theorem flipPoles_involutive (g : σ → Option σ) (s : σ) :
    flipPoles (flipPoles g) s = g s := by
  unfold flipPoles
  by_cases h0 : g s = none
  · simp [h0]
  · by_cases h1 : g s = some s
    · simp [h0, h1]
    · simp [h0, h1]

/-- Dead becomes live. -/
theorem flip_dead_to_live (g : σ → Option σ) (s : σ) (h : g s = none) :
    LoopsInPlace (flipPoles g) s := by
  unfold LoopsInPlace flipPoles; simp [h]

/-- Live becomes dead. -/
theorem flip_live_to_dead (g : σ → Option σ) (s : σ) (h : LoopsInPlace g s) :
    flipPoles g s = none := by
  unfold flipPoles; rw [h]; simp

/-- **The interior is fixed.** A configuration stepping onward to something else is untouched
    — the analogue of the unit circle being fixed under `rInv`. -/
theorem flipPoles_fixes_progress (g : σ → Option σ) (s t : σ)
    (h : g s = some t) (hne : t ≠ s) : flipPoles g s = g s := by
  unfold flipPoles; rw [h]; simp [hne, Option.some_ne_none]

/-- **The pole is preserved as a set.** Extremal stays extremal: the swap permutes the two
    poles rather than entering or leaving the pole. -/
theorem flipPoles_preserves_extremal (g : σ → Option σ) (s : σ) :
    Extremal g s ↔ Extremal (flipPoles g) s := by
  unfold Extremal LoopsInPlace flipPoles
  by_cases h0 : g s = none
  · simp [h0]
  · by_cases h1 : g s = some s
    · simp [h0, h1]
    · simp [h0, h1]

end PoleSwap

/-! ## § VI. The fan-out — and what actually blocks the snap

`Miniature.lean` § VI carries `fan_out` (three incomparable successors) alongside
`pole_cannot_fan : Fintype.card Pole = 2`: **the two-element pole cannot hold the branching
field.** The computational face as modelled here lives entirely at that pole — halted or
looping — and the two theorems below say why that matters.

The reading this section supports: `machine_snap_impossible` (§ III) is powered by
DETERMINISM, not by the self-loop. It is `pole_cannot_fan` in machine vocabulary. -/

/-- A deterministic step admits at most one successor: there is no fan-out to be had. -/
theorem deterministic_has_no_fanout (s t u : σ)
    (ht : f s = some t) (hu : f s = some u) : t = u := by
  rw [ht] at hu; exact Option.some_injective _ hu

/-- **The escape.** Drop determinism and a configuration may self-loop AND reach something
    else. So the obstruction of § III is the absence of fan-out, not the presence of a fixed
    point — and the branching field is where a departure could come from. -/
theorem nondeterministic_escapes_the_trap :
    ∃ R : Bool → Bool → Prop, ∃ s t : Bool, R s s ∧ R s t ∧ t ≠ s :=
  ⟨fun _ _ => True, true, false, trivial, trivial, by decide⟩

/-! ## § V. Occurrence is halting — hence undecidable -/

open Nat.Partrec Nat.Partrec.Code

/-- Occurrence in the computational face: some step at which the observable state changes.
    **This identification is a modelling choice, not a theorem.** -/
-- [ZP-CUSTOM] no Mathlib analog | reason: names the framework's "the transition fires" as a step-indexed predicate on codes, so the classical halting results can be applied to it. The identification is the framework's; Mathlib has the halting predicate but not this reading of it.
def Occurs (c : Code) (n : ℕ) : Prop := ∃ k, evaln k c n ≠ Option.none

/-- Occurrence is halting: the step where `none` becomes `some` exists exactly when the
    computation is defined. -/
theorem occurs_iff_halts (c : Code) (n : ℕ) : Occurs c n ↔ (eval c n).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hk
    exact Part.dom_iff_mem.mpr ⟨x, evaln_sound (by rw [hx]; rfl)⟩
  · intro hdom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := evaln_complete.mp hx
    exact ⟨k, by intro hnone; rw [hnone] at hk; exact absurd hk (by simp)⟩

/-- **Whether the snap occurs is undecidable.** No algorithm decides, of an arbitrary
    computation, whether it ever changes observable state. Turing (1936), via Mathlib's
    `ComputablePred.halting_problem`; the reduction is the identification above. -/
theorem occurrence_undecidable (n : ℕ) :
    ¬ ComputablePred (fun c : Code => Occurs c n) := by
  intro h
  apply ComputablePred.halting_problem n
  have hEq : (fun c : Code => Occurs c n) = (fun c : Code => (eval c n).Dom) := by
    funext c; exact propext (occurs_iff_halts c n)
  rwa [hEq] at h

/-- The asymmetry, mirroring the snap's own one-wayness: occurrence is semi-decidable — if it
    fires you will eventually see it — while non-occurrence is not even semi-decidable. What
    can be witnessed runs one way only. -/
theorem occurrence_semidecidable_nonoccurrence_not (n : ℕ) :
    REPred (fun c : Code => Occurs c n) ∧ ¬ REPred (fun c : Code => ¬ Occurs c n) := by
  have hEq : (fun c : Code => Occurs c n) = (fun c : Code => (eval c n).Dom) := by
    funext c; exact propext (occurs_iff_halts c n)
  refine ⟨by rw [hEq]; exact ComputablePred.halting_problem_re n, ?_⟩
  intro h
  apply ComputablePred.halting_problem_not_re n
  have hNeg : (fun c : Code => ¬ Occurs c n) = (fun c : Code => ¬ (eval c n).Dom) := by
    funext c; exact propext (not_congr (occurs_iff_halts c n))
  rwa [hNeg] at h

/-! ## § VI-b. THE REQUIREMENTS — what must hold IF execution occurs

Everything above is unconditional: an obstruction, an escape, a classification. This section
states the conditional form, which is what the framework actually needs. It does not claim the
snap fires. It says **what has to be true of the model if it does.**

The framework's own commitments are the two hypotheses: the bottom is a fixed point of its own
self-application (`AbstractSelfApp.fixed_bot`), and the snap departs from it (DA-1/DA-2). Hold
both and the conclusions below follow — they are not further assumptions. -/

/-- **THE REQUIREMENT.** If the bottom is a fixed point of its own dynamics AND execution
    occurs from it, then the dynamics **branches at the bottom**: `s` has two distinct
    successors. Stated over a relation so that multi-valuedness is available rather than
    assumed away.

    This is the positive form of `machine_snap_impossible`: not "the snap cannot happen" but
    "if it happens, the bottom is a branch point." -/
theorem execution_requires_branching {σ : Type*} (R : σ → σ → Prop) (s : σ)
    (hfix : R s s) (hdep : ∃ t, R s t ∧ t ≠ s) :
    ∃ t u, R s t ∧ R s u ∧ t ≠ u := by
  obtain ⟨t, hRt, hne⟩ := hdep
  exact ⟨t, s, hRt, hfix, hne⟩

/-- **AND THEREFORE THE DYNAMICS IS NOT A FUNCTION.** No single-valued step relation can meet
    the requirement. This is `machine_snap_impossible` restated as a condition on the MODEL
    rather than as an obstruction to the framework: a step function is the wrong shape for a
    bottom that both is its own fixed point and departs. -/
theorem execution_requires_nondeterminism (s : σ)
    (hfix : LoopsInPlace f s) (hdep : ∃ t, StateTransition.Reaches f s t ∧ t ≠ s) :
    False := by
  obtain ⟨t, hreach, hne⟩ := hdep
  exact hne (loop_is_a_trap f hfix hreach)

/-! **The full requirement list, for the record.** Given the framework's two commitments — the
bottom is its own fixed point, and execution occurs from it — the model must satisfy:

1. **Branching at the bottom**, arity ≥ 2 (`execution_requires_branching`).
2. **A non-functional dynamics** — no `σ → Option σ` will do (`execution_requires_nondeterminism`).
3. **Undecidability of the firing** — no algorithm certifies that it occurred
   (`occurrence_undecidable`), and non-occurrence is not even semi-decidable
   (`occurrence_semidecidable_nonoccurrence_not`).
4. **Both poles at the bottom, across charts** — zero output, infinite duration
   (`selfloop_is_zero_and_infinity`).

Items 1 and 2 are requirements on the carrier; 3 and 4 hold regardless. None of them asserts
that execution occurs — that remains the framework's commitment, and `l_inf`'s docstring is
the honest statement of where the argument for it stops. -/

/-! ## § VI-c. STUTTERING — a deterministic case the function-vs-relation framing misses

**Origin (Tim, 2026-08-06):** *"how the heck is it supposed to be deterministic if we can have
values passed from one instance to the next with temporal offsets? any program's internal state
changes with the addition of a variable."*

**The objection is correct and it corrects this file.** § II's docstring says *"could this still
move?" is a modal question, and this framework encodes that modality as the function-vs-relation
choice, nothing else.* **That is too strong.** There is a third option, and it needs no
non-determinism: a **function with no fixed point anywhere** whose **observable projection never
changes**.

`LoopsInPlace s := f s = some s` demands the state return to *itself*. Add any accumulating
component — a counter, a step index, Tim's temporal offset — and there is no fixed point at all, so
`loop_is_a_trap` and `machine_snap_impossible` **do not apply**. `carry` below witnesses it: at every
state it is in the trichotomy's **third** case (stepping onward to something genuinely different),
never halts, and yet shows the same thing forever.

**Why this matters for occurrence.** § V defines `Occurs` as *"some step at which the observable
state changes"* and proves it is halting. This section separates the two ideas that were running
together: **the state moving** and **the observable changing**. ⚠ **The corpus already makes that
separation and this section did not cite it:** DP-2 (`dp2_execution_distinguishability`,
`ZeroParadox/Order/Snap.lean`) proves the pre- and post-instantiation configurations are
value-*equal* and state-*distinct*. This is not a duplicate — DP-2 is one step on a two-phase type,
§ VI-c is unbounded forward motion — but the pointer belongs here. A configuration can move forever and
show nothing. So the occurrence question is not *"how does anything escape a fixed point"* — there
need be no fixed point — but *"does the projection ever change"*, which is a question about a
quotient, not a paradox about self-reference.

**⚠ And this is a NO-GO, not a route to the snap.** Stuttering forever is not departure **in § V's
observable sense** — the observable is constant on the entire reachable set (`stutter_obs_const`).
⚠ **Say which sense, because the corpus carries two.** Under the state-based reading — `da1_minimal_path`
(`ZeroParadox/Order/Snap.lean`), where instantiation moves the machine *regardless of the value
returned*, and which fences that it "does not carry that the step is taken" — `carry` is departing at
every step. The two readings disagree about `carry`, and that disagreement is the content, not a defect. What it removes is an
argument, not an obstacle — the inference *"deterministic, therefore trapped at a fixed point,
therefore stationary"* is invalid, because the middle step can fail while the conclusion still holds
for a different reason.

**Prior art — this is STUTTERING, and the standard name was already one citation away.** A step with
no observable effect is a *stutter step*; the induced equivalence is *stutter equivalence*. Mathlib's
own Turing development uses the word for exactly this (`Mathlib/Computability/TuringMachine/PostTuringMachine.lean`:
*"a one step stutter before actually halting"*, read at source). ⚠ **Everything beyond that Mathlib quote is cited for EXISTENCE
only — no other source here was read.** The notion is standard in model checking; *stutter equivalence*
is commonly attributed to Browne, Clarke & Grumberg, TCS **59** (1988),
and stuttering-insensitivity of specifications to Lamport (IFIP 1983), with a textbook treatment in
Baier & Katoen, *Principles of Model Checking* (already cited at § 0 of this file for the trap
state). **None of the three was located in `.claude-local/papers/` as of 2026-08-06, and this
paragraph makes no claim about what any of them says.** ⚠ Baier & Katoen is the exception worth
naming: § 0 of this file *does* assert its content (p. 157, the trap state), recorded there as
checked against an extracted source. Unfiled is not unread. ⚠ A draft of this paragraph asserted that stuttering-invariance is *an axiom* of TLA. That
was written without reading Lamport, and axiom-versus-theorem is the one status distinction this
project polices hardest (AX-1 → T-SNAP). The claim is withdrawn, not restated. Nothing in this section is claimed as new
mathematics: the content is that the corpus's own trichotomy does not separate these cases.
-/

/-- **`Statement:` every step leaves the observable unchanged.** The stutter condition, as an
explicit hypothesis rather than a property baked into a carrier. -/
def Stutters {σ α : Type*} (f : σ → Option σ) (obs : σ → α) : Prop :=
  ∀ s s', f s = some s' → obs s' = obs s

/-- **`Statement:` a stuttering machine's observable is constant on its whole reachable set.** -/
theorem stutter_obs_const {σ α : Type*} (f : σ → Option σ) (obs : σ → α)
    (h : Stutters f obs) {s t : σ} (hr : StateTransition.Reaches f s t) : obs t = obs s := by
  induction hr with
  | refl => rfl
  | tail _ hstep ih => rw [h _ _ hstep]; exact ih

/-- The witness: a deterministic step carrying an accumulating index. -/
def carry : Bool × ℕ → Option (Bool × ℕ) := fun p => some (p.1, p.2 + 1)

/-- **`Statement:` it has NO self-loop at any state** — so `loop_is_a_trap` and
`machine_snap_impossible`, which both require `f s = some s`, do not apply to it. -/
theorem carry_no_selfloop (p : Bool × ℕ) : ¬ LoopsInPlace carry p := by
  intro h
  have h2 := congrArg Prod.snd (Option.some_injective _ h)
  simp at h2

/-- **`Statement:` and it never halts.** -/
theorem carry_never_halts (p : Bool × ℕ) : carry p ≠ Option.none := by
  simp only [carry]; exact Option.some_ne_none _

/-- **`Statement:` every one of its steps is a stutter.** -/
theorem carry_stutters : Stutters carry Prod.fst := by
  intro s s' h
  simp only [carry, Option.some.injEq] at h
  rw [← h]

/-- **`Statement:` stepping onward forever, showing nothing.** At every state `carry` is in the
trichotomy's THIRD case — stepping onward to something genuinely different — and yet nothing
reachable from it ever shows anything new. Deterministic, never halting, no fixed point, observably
stationary.

`Reading:` (Tim, 2026-08-06, conjectural) the framework reads this as the honest shape of a
divergent bottom: not a machine trapped at a fixed point, but one whose state advances forever while
what it presents does not. Whether the bottom's *own* observable ever changes is untouched by this
and remains the open commitment (`l_inf`). -/
theorem carry_steps_onward_forever_yet_shows_nothing (p : Bool × ℕ) :
    (∃ q, carry p = some q ∧ q ≠ p)
      ∧ (∀ t, StateTransition.Reaches carry p t → t.1 = p.1) := by
  refine ⟨⟨(p.1, p.2 + 1), rfl, ?_⟩,
    fun t hr => stutter_obs_const carry Prod.fst carry_stutters hr⟩
  intro h
  have h2 := congrArg Prod.snd h
  simp at h2

/-! ## § VII. The capstone — the whole computational shape in one statement

Mirrors `Miniature.lean`'s `shape`. Five faces of the computational bottom, bundled so the
arrangement is checkable rather than narrated. The undecidability half (§ V) lives over `Code`
rather than a bare `σ` and so is not bundled here; it is the same story at a different carrier.

**Read alongside `Miniature.lean`.** Faces 2 and 3 are that file's pole and `swap_involutive`;
face 4 is `pole_cannot_fan` in machine vocabulary — the two-element pole cannot hold a
branching field, so a deterministic machine cannot depart from its own fixed point. What is
absent here relative to `Miniature` is the engine (Lawvere) and the fan-out itself; the
engine's computational instance lives in `Rice.lean` (`effective_floor_fixedPoint`), and the
fan-out is § VI's escape rather than a face of this pole. -/
theorem occurrence_shape [DecidableEq σ] (s : σ) :
    -- (1) there is no "exists but has not started" state
    (f s = Option.none ∨ ∃ s', f s = some s') ∧
    -- (2) the pole and the interior: halted, looping in place, or stepping onward
    (f s = Option.none ∨ LoopsInPlace f s ∨ ∃ s', f s = some s' ∧ s' ≠ s) ∧
    -- (3) the pole is preserved by the swap (which is an involution, `flipPoles_involutive`)
    (Extremal f s ↔ Extremal (flipPoles f) s) ∧
    -- (4) NO-GO: nothing is both its own fixed point and departed from
    (¬ IsComputationalBottom f s) ∧
    -- (5) the inversion: the dead bottom yields, the live bottom withholds
    ((f s = Option.none → s ∈ StateTransition.eval f s) ∧
     (LoopsInPlace f s → ∀ b, b ∉ StateTransition.eval f s)) :=
  ⟨step_dichotomy f s,
   machine_trichotomy f s,
   flipPoles_preserves_extremal f s,
   machine_snap_impossible f s,
   dead_yields_live_withholds f s⟩

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms step_dichotomy
#print axioms not_halted_means_stepping
#print axioms no_unstarted_state
#print axioms machine_trichotomy
#print axioms loop_is_a_trap
#print axioms machine_snap_impossible
#print axioms the_live_bottom_is_coherent
#print axioms eval_of_halted
#print axioms eval_of_loop_is_empty
#print axioms dead_yields_live_withholds
#print axioms selfloop_is_zero_and_infinity
#print axioms live_step_not_wellFounded
#print axioms loops_not_unique
#print axioms inversion_is_the_wf_divide
#print axioms flipPoles_involutive
#print axioms flipPoles_fixes_progress
#print axioms flipPoles_preserves_extremal
#print axioms deterministic_has_no_fanout
#print axioms nondeterministic_escapes_the_trap
#print axioms execution_requires_branching
#print axioms execution_requires_nondeterminism
#print axioms stutter_obs_const
#print axioms carry_no_selfloop
#print axioms carry_never_halts
#print axioms carry_stutters
#print axioms carry_steps_onward_forever_yet_shows_nothing
#print axioms occurrence_shape
#print axioms occurs_iff_halts
#print axioms occurrence_undecidable
#print axioms occurrence_semidecidable_nonoccurrence_not

end PurityCheck
