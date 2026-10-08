import ZeroParadox.Computability.Kleene
import ZeroParadox.Computability.Rice
import ZeroParadox.Computability.Occurrence
import ZeroParadox.Computability.GroundZero
import ZeroParadox.Computability.SelfCopyReference
import ZeroParadox.Category.DiagonalWitness
import ZeroParadox.Category.LawvereTwoAdic
import ZeroParadox.Category.IgnoranceSeam
import ZeroParadox.Settheory.Wall
import ZeroParadox.Information.Disjunctive

/-!
# Machine-checked characterization index of COMPUTATION — what it can and cannot be

## Engineer's Take

We have the bottom, the snap, and epsilon-zero each with an index of what they cannot be.
Computation needed the same thing, formalized into a single reference list. It also needs a
read-this-file rule when discussing computability theory, the way we have for the others, and
that absence is part of what bit us before. Marking each line as Statement or Reading is good
for a human reader as much as for the machines. Putting all of the pieces together is
specifically what this document renders: a list of both positive and negative conditions.

---
## Formal Overview (AI-assisted)
The computational face, beside the four other `*CannotBe.lean` indexes: `#check` lines, each glossed
`Statement:` / `Reading:` above it, and anonymous `example`s, this file's only proofs. Conventions and
the commitments the glosses name: `ZeroParadox/Computability/ComputationCannotBe.md`.
-/

section ComputationCannotBeIndex

/-! ### § I. What computation CANNOT do — the walls -/

-- Statement: for any `g : A → (A → Bool)`, `¬ Function.Surjective g`. Proved from
--   `lawvere_fixedpoint` and `bool_not_no_fixedpoint` — the Cantor/Lawvere no-surjection fact.
-- Reading: the halting wall. Turing (1936) enters at the NEXT entry,
--   `self_halting_undecidable`; this declaration mentions no machine and no halting.
#check @ZeroParadox.no_self_decider

-- Statement: `fun c => (eval c (encode c)).Dom` is not a ComputablePred.
#check @ZeroParadox.self_halting_undecidable

-- Statement: `IsComputationalQuine` is not a ComputablePred — no algorithm decides membership in the
--   predicate. It does not say no algorithm names a member: the constant codes are members (§ III).
#check @ZeroParadox.isComputationalQuine_undecidable

-- Statement: no computable map is EVAL-fixed-point-free — `eval (g c) ≠ eval c` cannot hold for
-- every c. ⚠ LITERAL fixed-point-freeness is a different property and DOES occur on codes:
-- `fun c => Code.pair c c` fixes nothing. The qualifier is in the declaration's own name.
#check @ZeroParadox.no_computable_evalFixedPointFree

-- Statement: on `List Bool`, `partialAddOne w = w ↔ w = []` (`ZeroParadox/Category/LawvereTwoAdic.lean`).
-- Reading: the wall above says no computable map on codes is free of fixed points up to `eval`; add-one
--   extended to partial digit streams is not free of fixed points either, and rests only at the empty stream.
#check @ZeroParadox.partialAddOne_fixed_iff

-- Statement: no map `List Bool → ℤ_[2]` semiconjugates `partialAddOne` to add-one on ℤ_[2]
--   (`ZeroParadox/Category/IgnoranceSeam.lean`).
-- Reading: the obstruction is generic, a fixed point on one side and none on the other, carried by
--   Mathlib's `Function.IsFixedPt.map`; unlike the wall above, it is not specific to computation.
#check @ZeroParadox.partialAddOne_no_semiconj

/-! ### § II. What computation DOES supply — the floors -/

-- Statement: for partial computable `f : Code → (ℕ →. ℕ)`, some code `c` has `eval c = f c` —
--   Kleene's second recursion theorem, imported from Mathlib (`fixed_point₂`). Prior art, cited not
--   claimed.
#check @ZeroParadox.kleene_fixed_point_exists

-- Statement: for partial computable `F`, the codes `c` with `eval c = F c` form an infinite set.
#check @ZeroParadox.fixed_points_infinite

-- Statement: the padding lemma: a partial recursive `g` has infinitely many codes `c`, `eval c = g`.
#check @ZeroParadox.padding

-- Statement: a code satisfying `IsComputationalQuine` exists, via the recursion theorem.
#check @ZeroParadox.computational_quine_exists

-- Statement: for computable `g : Code → Code`, `∃ c, eval (g c) = eval c` — a fixed point of
--   `g` up to extensional equality of the evaluated functions.
-- Reading: "the nontrivial floor in the effective category, where self-reference closes."
--   Floor/wall is framework vocabulary, not a term in the statement.
#check @ZeroParadox.effective_floor_fixedPoint

-- Statement: `selfApply` (`c, n ↦ eval c (encode c + n)`) is partial computable. NB this is NOT the
--   recursion theorem.
#check @ZeroParadox.selfApply_partrec

/-! ### § III. The quine family — a FAMILY, not a point -/

-- Statement: for any n a computational quine exists with Gödel number exceeding n. Its proof's
--   witnesses are the CONSTANT codes, which meet the periodicity condition trivially: both sides
--   evaluate to the constant (the `example` below).
#check @ZeroParadox.infinite_quine_family

-- Statement: every constant code `Code.const k` is a computational quine.
-- Reading: CONTROL. `IsComputationalQuine` holds of programs that ignore their input, so it is a
--   periodicity condition and does not by itself pin self-reference.
example (k : ℕ) : ZeroParadox.IsComputationalQuine (Nat.Partrec.Code.const k) := by
  show Nat.Partrec.Code.eval (Nat.Partrec.Code.const k)
    = ZeroParadox.selfApply (Nat.Partrec.Code.const k)
  funext m
  simp [ZeroParadox.selfApply, Nat.Partrec.Code.eval_const]

-- Statement: equal Gödel numbers imply equal codes (`encode c₁ = encode c₂ → c₁ = c₂`). Proof is
--   `Encodable.encode_inj`; both quine hypotheses are unused. A fact about the encoding, not about
--   quines. The converse holds of any function, by `congrArg`.
#check @ZeroParadox.quine_goedel_injective

-- Statement: `encode c` is *a* period of `eval c` — not shown least, and a constant is
--   periodic with every period.
-- Reading: that the (function, index) pair signatures self-reference. Prior art for
--   index-multiplicity is the Padding Lemma, which gives many indices for the SAME function —
--   a different fact from this family, which is broad. Do not conflate them.
#check @ZeroParadox.quine_period_is_goedel

-- Statement: some code is both `SelfPrints` (channel `0` returns its own Gödel number) and
--   `Universal` (channel `e + 1` agrees with the code numbered `e`).
#check @ZeroParadox.selfref_universal_exists

-- Statement: infinitely many codes are both `SelfPrints` and `Universal`.
#check @ZeroParadox.selfref_universal_infinite

-- Statement: CONTROL, some code is `Universal` and not `SelfPrints`.
#check @ZeroParadox.universal_not_selfprints

-- Statement: two `SelfPrints` codes with the same `eval` are the same code.
-- Reading: computational self-reference has a uniqueness, at the level of behaviour.
#check @ZeroParadox.selfprints_behaviour_injective

-- Statement: two `SelfPrints ∧ Universal` codes agree on every channel `e + 1`, and two distinct
--   ones differ on channel `0`.
-- Reading: replicas share everything but the address; the next instance adds only the address.
#check @ZeroParadox.selfPrints_universal_address

-- Statement: a disjunctive tape `ℕ → Bool` equals its own shift by no `a > 0`: no full copy of
--   itself at any offset.
-- Reading: Tim's commitment concerns the framework's ⊥ role, ⊥ of a `ZPSemilattice`: read as a tape,
--   its occupant is maximally complex (prefix-free sense). What that would add, and the standard
--   theory behind it, is `ZeroParadox/Information/Disjunctive.lean` § VI. No map from a
--   `ZPSemilattice` to `ℕ → Bool` is claimed or constructed, and no order on tapes in which a
--   maximally complex tape is least: the reading is a commitment, not a chart. In `ℕ → Bool` under
--   the pointwise order, ⊥ is the all-false tape, which is not disjunctive
--   (`allFalse_not_disjunctive`).
#check @ZeroParadox.disjunctive_not_periodic

/-! ### § IV. The bottom's computational face — PROVED vs COMMITTED -/

-- Statement: for `q` in a `ZPSemilattice L` carrying `KleeneStructure`,
--   `IsQuineAtom q ↔ q = bot ∧ ∀ x, join q x = x`: the Quine-atom property is equivalent to the
--   CONJUNCTION of the order-bottom and join-identity conditions; those two are equivalent to each
--   other by `da2_bottom_characterization`. Proof term is `t_exec_triple_iff`, a ZP-J result
--   mentioning no computation.
-- Reading: that a fourth, computational face joins the three. No clause of this theorem carries it;
--   `KleeneStructure.botCode_is_quine` below is what the class field supplies.
#check @ZeroParadox.t_comp

-- Statement: under `[KleeneStructure L]`, any Quine atom `q : L` equals `bot` of the `ZPSemilattice L`.
--   No `Code` and no Kleene clause appear; the `[KleeneStructure]` hypothesis is inert on the proof
--   route — though NOT absent from the axiom footprint, since `#print axioms` follows the statement.
-- Reading: the tie of the Kleene quine to `bot` of `L` is the `KleeneStructure` commitment, and not
--   a Lean `=` (`Code` versus `L`).
#check @ZeroParadox.kleene_quine_is_bot

-- Statement: the class field — the instance's `botCode` satisfies `IsComputationalQuine`, which the
--   constant codes also satisfy (§ III). No field of `KleeneStructure` relates `botCode` to `bot`.
-- Reading: that `botCode` is the computational face of `bot` is the `KleeneStructure` commitment. No
--   theorem states it, and no `=` can: `botCode` is a `Code` and `bot` an element of `L`.
#check @ZeroParadox.KleeneStructure.botCode_is_quine

-- Statement: `IsQuineAtom (bot : MachinePhase)` — c₀, ⊥ of `MachinePhase`, is its unique
--   self-containing state. Mentions no `Code` and no execution. `machinePhaseAFA` defines
--   `selfMem x := x = bot`, so the statement holds by definition (the term `⟨rfl, fun _ h => h⟩` proves it), and the
--   `example` after this theorem in
--   `ZeroParadox/Computability/Kleene.lean` proves the same type with no Kleene instance.
-- Reading: that c₀ is self-EXECUTING is DA-1's claim. DA-1's precondition is the occurrence
--   commitment, which DA-1 consumes; the `KleeneStructure` commitment adds only that `botCode`
--   names ⊥ of `MachinePhase`.
#check @ZeroParadox.da1_closed_concrete

-- Statement: c₀ is a Quine atom of `MachinePhase` AND a state sequence in that carrier starts at c₀
--   and never steps.
-- Reading: CONTROL. Being a Quine atom does not make anything move; that the snap occurs follows from
--   the occurrence commitment together with DA-1 (`ZeroParadox/Order/Snap.lean`'s Formal Overview).
open ZeroParadox ZeroParadox.ZPSemilattice in
example : IsQuineAtom (bot : MachinePhase) ∧
    ∃ S : ℕ → MachinePhase, S 0 = bot ∧ IsStateSequence S ∧ ∀ n, S (n + 1) = S n :=
  ⟨da1_closed_concrete, fun _ => bot, rfl, ⟨fun _ => bot, fun _ => (bot_join bot).symm⟩,
    fun _ => rfl⟩

-- Statement: the `KleeneStructure MachinePhase` instance. Its `botCode` is
--   `Classical.choose computational_quine_exists` — SOME code meeting the predicate, and the
--   predicate is met by constants. The `example` after it in `ZeroParadox/Computability/Kleene.lean`
--   builds a computable instance with `Code.const 0`.
#check @ZeroParadox.machinePhaseKleene

/-! ### § V. The pivot face — the fixed point exists, and a semantic property is undecidable -/

-- Statement: for computable `f : Code → Code`, `∃ c, eval (f c) = eval c` — Rogers' fixed point up
--   to `eval`, the same type as `effective_floor_fixedPoint` (§ II).
-- Reading: the floor in the Rice setting. That it is the face's bottom is the family's criterion,
--   as the home docstring says, not this theorem.
#check @ZeroParadox.rice_face_has_bottom

-- Statement: a conjunction, for computable `f` and a non-trivial extensional `C : Set Code`: a fixed
--   point of `f` up to `eval` exists, AND membership in `C` is not a ComputablePred. The
--   undecidability is of `C` over all codes, and the second conjunct does not mention `f`; nothing
--   is stated about membership at `f`'s fixed point.
#check @ZeroParadox.quine_exists_yet_rice

/-! ### § VI. Occurrence — what it takes for a configuration to MOVE

Configurations of a step function `f : σ → Option σ`; the computational bottom is the framework's
reading of one. The negative conditions of this index. See `ZeroParadox/Computability/Occurrence.lean`. -/

-- Statement: in the operational model, not-halted and no-next-configuration cannot both hold.
-- Reading: "exists but has not begun" is not a state in this model. The next configuration may be
--   the configuration itself (`LoopsInPlace`), so this supplies no change of state.
#check @ZeroParadox.no_unstarted_state

-- Statement: at any configuration — halted, looping in place, or stepping onward.
-- Reading: the middle case is not a third route; it is the self-referential object itself,
--   `s` being a fixed point of its own step. Under a function it shares the halted case's fate:
--   each reaches only itself (`loop_is_a_trap`).
#check @ZeroParadox.machine_trichotomy

-- Statement: everything reachable from a self-looping configuration is that configuration.
#check @ZeroParadox.loop_is_a_trap

-- Statement: no configuration of a deterministic machine is both its own fixed point AND
--   departed from.
-- Reading: the same SHAPE as `f_snap_impossible` for ordered fields — a resemblance between
--   two separate no-go results, never an identity or a transfer between them.
-- Reading: the framework's answer is DA-2, instantiation succession, which denies the
--   single-machine premise. The other exit is a non-functional step (next entry).
#check @ZeroParadox.machine_snap_impossible

-- Statement: over a relation `R`, if `R s s` and `R s t` with `t ≠ s`, then `s` has two distinct
--   `R`-successors.
-- Reading: the positive form of the NO-GO above: a fixed point that departs is a branch point.
#check @ZeroParadox.execution_requires_branching

-- Statement: a halted configuration evaluates to itself; a self-looping one has empty
--   evaluation.
-- Reading: halting and looping are the 0 and ∞ readings of the computational bottom, and what
--   each yields is the opposite of what it is. A shared shape, never a Lean identity.
#check @ZeroParadox.dead_yields_live_withholds

-- Statement: `∃ k, evaln k c n ≠ none` holds exactly when `(eval c n).Dom`.
-- Reading: that this is the framework's "occurrence". A modelling choice, not a theorem. Occurrence
--   is then the halting question: semidecidable, not decidable (the next two entries).
#check @ZeroParadox.occurs_iff_halts

-- Statement: CONTROL, `Code.zero`, which is not universal, satisfies `Occurs` on every input.
-- Reading: `Occurs` is a static property of a (code, input) pair.
#check @ZeroParadox.zero_occurs

-- Statement: `fun c => Occurs c n` is not a ComputablePred. Turing (1936) via Mathlib.
#check @ZeroParadox.occurrence_undecidable

-- Statement: occurrence is an REPred; non-occurrence is not.
-- Reading: what can be witnessed runs one way only. A one-way shape like `t_snap_irreversible`'s,
--   an order fact there and a recursion-theoretic one here; a resemblance, never an identity.
#check @ZeroParadox.occurrence_semidecidable_nonoccurrence_not

/-! ### § VI-b. The pole, its swap, and what actually blocks the snap -/

-- Statement: exchanging the halted and self-looping poles twice is the identity, pointwise:
--   `flipPoles (flipPoles g) s = g s`.
-- Reading: the computational `rInv` / `swap`. **Level fence:** an automorphism of the SPACE of
--   machines, not of one machine — same shape at a different level, never an identity.
#check @ZeroParadox.flipPoles_involutive

-- Statement: extremal (halted or looping) stays extremal under the swap.
-- Reading: the pole is preserved as a set while its two elements exchange — `rInv` on {0, ∞}.
#check @ZeroParadox.flipPoles_preserves_extremal

-- Statement: a configuration stepping onward to something else is left unchanged by the swap.
-- Reading: the interior is fixed — the unit circle under `rInv`.
#check @ZeroParadox.flipPoles_fixes_progress

-- Statement: a self-looping configuration makes the step relation non-well-founded.
-- Reading: the bridge to `ZeroParadox/Multihomed/Boundary.lean`'s `floor_not_wellFounded` — the live/dead
--   split has the SHAPE of the ν/μ divide at a different level, never an identity with it.
--   ONE-DIRECTIONAL: the converse is false, and "dead" does NOT give
--   a well-founded relation.
#check @ZeroParadox.live_step_not_wellFounded

-- Statement: a machine can fix two distinct configurations.
-- Reading: self-loops need not be unique, so the step relation is not QuineHost-shaped and no
--   argument from ZP-J's uniqueness may be run on it.
#check @ZeroParadox.loops_not_unique

-- Statement: a deterministic step admits at most one successor.
#check @ZeroParadox.deterministic_has_no_fanout

-- Statement: a non-deterministic relation can self-loop AND reach something else.
-- Reading: what blocks the snap in § VI is DETERMINISM, not the self-loop —
--   `ZeroParadox/Miniature.lean`'s `pole_cannot_fan` in machine vocabulary.
#check @ZeroParadox.nondeterministic_escapes_the_trap

-- Statement: the five faces bundled — halted or has a next configuration, the trichotomy, the
--   pole preserved under swap, the NO-GO, and the inversion (its two halves as two conjuncts).
#check @ZeroParadox.occurrence_shape

/-! ### § VII. NO-GO gauges — what may NOT be inferred -/

-- Statement: every `ZPSemilattice` carries an `AbstractSelfApp`, so no property of the carrier
--   follows from the bare hypothesis.
#check @ZeroParadox.abstractSelfApp_always_inhabited

/-! ### § VIII. Ground zero — the bottom as a BEHAVIOUR, not a configuration

`ZeroParadox/Computability/GroundZero.lean`. Reads the step function as a coalgebra for
`X ↦ 1 + X` and connects it to `ZeroParadox/Computability/NatListRegime.lean`, which the project already carried. -/

-- Statement: `(stepCoalg f s).1` is `false` or `true`. Axiom-free.
-- Reading: there is no "exists but has not begun" — the head type is `Bool`, so that state is
--   absent from the type rather than ruled out by argument.
#check @ZeroParadox.head_is_leaf_or_step

-- Statement: `f s ≠ none → (stepCoalg f s).1 = true`. Axiom-free.
-- Reading: "already executing at ground zero, by definition", GIVEN that `s` has not halted. The
--   head is `true` also for a self-looping configuration (`loop_unfolds_to_infinity`), so
--   "executing" here is taking a step, possibly to itself, and supplies no change of state.
--   Capability and execution are not separated in this model, so a capability that is not being
--   exercised is not expressible. NOT a claim that anything CAUSES execution.
#check @ZeroParadox.not_halted_is_stepping_head

-- Statement: `¬ EventuallyLeaf x → x = natInfinity`. A behaviour that never reaches a leaf is
--   uniquely `natInfinity`. A Lean `=` inside one type, by bisimulation.
-- Reading: the computational counterpart of `quine_unique` — `natInfinity`, in the final coalgebra
--   of `X ↦ 1 + X`, pinned apophatically, by what it never does, with no element-hood in any
--   machine carrier assumed.
#check @ZeroParadox.notEL_unique

-- Statement: a self-looping configuration's unfolding equals `natInfinity`.
-- Reading: a self-looping configuration's BEHAVIOUR and `natInfinity` are the same point of the
--   final coalgebra of `X ↦ 1 + X`. The `=` is between two `Cofix` elements, within one type; the configuration
--   `s : σ` is NOT equated with anything — it lives in a different type. It says nothing about
--   whether the occupant of the framework's ⊥ role, ⊥ of a `ZPSemilattice`, read as a configuration
--   of a step function `f : σ → Option σ` (§ VI), self-loops — that is the commitment.
#check @ZeroParadox.loop_unfolds_to_infinity

-- Statement: with a three-valued head there IS a configuration neither halted nor stepping.
--   `TriStep` is a deliberate counter-model and must never be used as a framework object.
#check @ZeroParadox.tri_unstarted_state_exists

-- Statement: both halves at once — two-valued, no unstarted state; three-valued, one exists.
-- Reading: what removes the unstarted state is the CLEANNESS OF THE SPLIT, not the dynamics. Having
--   no unstarted state is not motion: a self-loop counts as stepping and changes nothing
--   (`loop_is_a_trap`).
#check @ZeroParadox.forcing_needs_the_binary_split

-- Statement: in `MachinePhase`, T-SNAP's triple (`c₀ ≠ c₁`, `c₁ ≠ c₀`, `join c₀ c₁ = c₁`) holds
--   together with a dynamics `stuckPhase` under which every phase is fixed. It constrains the SHAPE
--   of a transition; it does not assert one occurs.
-- Reading: that the snap occurs follows from the occurrence commitment together with DA-1, as
--   stated in `ZeroParadox/Order/Snap.lean`'s Formal Overview, not from this line.
#check @ZeroParadox.tsnap_holds_but_nothing_moves

/-! ### § IX. Self-copy maps on infinite carriers — a map EXISTS, classically; that one is applied is a commitment -/

-- Statement: for `α : Type`, `α` is infinite iff it carries a `SelfCopyRef` map: one-to-one, not
--   onto, with exactly one fixed point. The infinite-to-map direction is proved with
--   `Classical.choice` and is not provable in set theory without choice (the `PurityCheck` note in
--   `ZeroParadox/Computability/SelfCopyReference.lean`).
-- Reading: SCOPE. This is the existence of such a map, not that one is applied. That ⊥ on an
--   infinite carrier performs one is a commitment (`ZeroParadox/Computability/SelfCopyReference.lean`
--   § IV); `MachinePhase`, the two-phase rounding that carries `machinePhaseKleene`, admits none
--   (the `example` below).
#check @ZeroParadox.infinite_iff_exists_selfCopyRef

-- Statement: for finite `α : Type`, no `SelfCopyRef` map exists.
#check @ZeroParadox.no_selfCopyRef_of_finite

-- Statement: in particular none exists on `MachinePhase`, the two-state carrier of c₀ and c₁.
-- Reading: CARRIER. The infinite-to-map direction reaches infinite carriers only; `MachinePhase`,
--   the carrier of c₀'s Quine atom (§ IV) and of `machinePhaseKleene`, admits no such map.
example (f : ZeroParadox.MachinePhase → ZeroParadox.MachinePhase) : ¬ ZeroParadox.SelfCopyRef f :=
  haveI : Finite ZeroParadox.MachinePhase :=
    Finite.of_surjective (fun b : Bool => if b then ZeroParadox.c₁ else ZeroParadox.c₀)
      (fun x => by cases x; exacts [⟨false, rfl⟩, ⟨true, rfl⟩])
  ZeroParadox.no_selfCopyRef_of_finite f

end ComputationCannotBeIndex
