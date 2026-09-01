import ZeroParadox.Computability.Kleene
import ZeroParadox.Computability.Rice
import ZeroParadox.Computability.Occurrence
import ZeroParadox.Computability.GroundZero
import ZeroParadox.Category.DiagonalWitness
import ZeroParadox.Settheory.Wall

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

The fourth `#check`-only index, beside `BottomCannotBe.lean`, `Order/SnapCannotBe.lean` and
`Ordinal/Epsilon0CannotBe.lean`. Those pin the three core *objects*; this one pins the
**computational face** — and in particular the proved-versus-committed line, which is where
this face has historically drifted.

Like the others it states no new results and reproduces no logic: every line `#check`s an
already-proven theorem in its home file, so the `import`s recompile those files and the index
cannot point at a dead or renamed result.

## The honest status of a `#check`-only index (corrected 2026-07-26)

The `#check` **lines** cannot overclaim — they create no declarations. The `--` **glosses
beside them absolutely can**, and in two sibling indexes they did, surviving four adversary
rounds. So this file is built under the standing convention from the outset:

* **`Statement:`** — an accurate restatement of what the declaration proves.
* **`Reading:`** — the framework's interpretation, explicitly NOT a claim about the theorem.

No gloss is anything else. Where a `Reading:` is load-bearing, the commitment carrying it is
named.
-/

section ComputationCannotBeIndex

/-! ### § I. What computation CANNOT do — the walls -/

#check @ZeroParadox.no_self_decider
-- Statement: for any `g : A → (A → Bool)`, `¬ Function.Surjective g`. Proved from
--   `lawvere_fixedpoint` and `bool_not_no_fixedpoint` — the Cantor/Lawvere no-surjection fact.
-- Reading: the halting wall. Turing (1936) enters at the NEXT entry,
--   `self_halting_undecidable`; this declaration mentions no machine and no halting.

#check @ZeroParadox.self_halting_undecidable
-- Statement: `fun c => (eval c (encode c)).Dom` is not a ComputablePred.

#check @ZeroParadox.isComputationalQuine_undecidable
-- Statement: `IsComputationalQuine` is not a ComputablePred — no algorithm identifies the quines.

#check @ZeroParadox.no_computable_evalFixedPointFree
-- Statement: no computable map is EVAL-fixed-point-free — `eval (g c) ≠ eval c` cannot hold for
-- every c. ⚠ LITERAL fixed-point-freeness is a different property and DOES occur on codes:
-- `fun c => Code.pair c c` fixes nothing. The qualifier is in the declaration's own name.

/-! ### § II. What computation DOES supply — the floors -/

#check @ZeroParadox.kleene_fixed_point_exists
-- Statement: Kleene's second recursion theorem, imported from Mathlib (`fixed_point₂`).
--   Prior art, cited not claimed.

#check @ZeroParadox.computational_quine_exists
-- Statement: a code satisfying `IsComputationalQuine` exists, via the recursion theorem.

#check @ZeroParadox.effective_floor_fixedPoint
-- Statement: for computable `g : Code → Code`, `∃ c, eval (g c) = eval c` — a fixed point of
--   `g` up to extensional equality of the evaluated functions.
-- Reading: "the nontrivial floor in the effective category, where self-reference closes."
--   Floor/wall is framework vocabulary, not a term in the statement.

#check @ZeroParadox.selfApply_partrec
-- Statement: self-application is partial computable. NB this is NOT the recursion theorem.

/-! ### § III. The quine family — a FAMILY, not a point -/

#check @ZeroParadox.infinite_quine_family
-- Statement: for any n a computational quine exists with Gödel number exceeding n. Its
--   witnesses are the CONSTANT codes, which satisfy the periodicity condition vacuously.

#check @ZeroParadox.quine_goedel_injective
-- Statement: distinct Gödel numbers imply distinct codes. Proof is `Encodable.encode_inj`;
--   both quine hypotheses are unused. A fact about the encoding, not about quines.

#check @ZeroParadox.quine_period_is_goedel
-- Statement: `encode c` is *a* period of `eval c` — not shown least, and a constant is
--   periodic with every period.
-- Reading: that the (function, index) pair signatures self-reference. Prior art for
--   index-multiplicity is the Padding Lemma, which gives many indices for the SAME function —
--   a different fact from this family, which is broad. Do not conflate them.

/-! ### § IV. The bottom's computational face — PROVED vs COMMITTED -/

#check @ZeroParadox.t_comp
-- Statement: THREE characterisations proved equivalent. Proof term is `t_exec_triple_iff`, a
--   ZP-J result mentioning no computation.
-- Reading: that a fourth, computational face joins them. It enters as the `KleeneStructure`
--   class field `botCode_is_quine`, NOT as a clause of this theorem.

#check @ZeroParadox.kleene_quine_is_bot
-- Statement: any Quine atom equals ⊥. No `Code` and no Kleene clause appear; the
--   `[KleeneStructure]` hypothesis is inert on the proof route — though NOT absent from the
--   axiom footprint, since `#print axioms` follows the statement.
-- Reading: "the Kleene quine IS ⊥" — the class's commitment, and not a Lean `=`.

#check @ZeroParadox.da1_closed_concrete
-- Statement: `IsQuineAtom (bot : MachinePhase)`. Mentions no `Code` and no execution.
-- Reading: that ⊥ is self-EXECUTING rather than a static description. DA-1's claim, carried by
--   the `KleeneStructure` commitment. `l_inf`'s docstring states that the step from unbounded
--   surprisal to forced execution is an ontological bridge, not a consequence.

#check @ZeroParadox.machinePhaseKleene
-- Statement: the `KleeneStructure MachinePhase` instance. Its `botCode` is
--   `Classical.choose computational_quine_exists` — SOME code meeting the predicate, and the
--   predicate is met by constants.

/-! ### § V. The pivot face — the fixed point exists yet is undecidable -/

#check @ZeroParadox.rice_face_has_bottom
-- Statement: the floor exists in the Rice setting.

#check @ZeroParadox.quine_exists_yet_rice
-- Statement: the fixed point is present, yet membership at it is undecidable.

/-! ### § VI. Occurrence — what it takes for the bottom to MOVE

The negative conditions of this index. See `ZeroParadox/Computability/Occurrence.lean`. -/

#check @ZeroParadox.no_unstarted_state
-- Statement: in the operational model, not-halted and no-next-configuration cannot both hold.
-- Reading: existence is a machine, so "exists but has not begun" is not a state it can be in.

#check @ZeroParadox.machine_trichotomy
-- Statement: at any configuration — halted, looping in place, or stepping onward.
-- Reading: the middle case is not a third route; it is the self-referential object itself,
--   `s` being a fixed point of its own step.

#check @ZeroParadox.loop_is_a_trap
-- Statement: everything reachable from a self-looping configuration is that configuration.

#check @ZeroParadox.machine_snap_impossible
-- Statement: no configuration of a deterministic machine is both its own fixed point AND
--   departed from.
-- Reading: the same SHAPE as `f_snap_impossible` for ordered fields — a resemblance between
--   two separate no-go results, never an identity or a transfer between them.
-- Reading: the departure must come from outside a single machine's dynamics — which is DA-2,
--   instantiation succession.

#check @ZeroParadox.dead_yields_live_withholds
-- Statement: a halted configuration evaluates to itself; a self-looping one has empty
--   evaluation.
-- Reading: halting and looping are the 0 and ∞ readings of the computational bottom, and what
--   each yields is the opposite of what it is. A shared shape, never a Lean identity.

#check @ZeroParadox.occurs_iff_halts
-- Statement: `∃ k, evaln k c n ≠ none` holds exactly when `(eval c n).Dom`.
-- Reading: that this is the framework's "occurrence". A modelling choice, not a theorem.

#check @ZeroParadox.occurrence_undecidable
-- Statement: `fun c => Occurs c n` is not a ComputablePred. Turing (1936) via Mathlib.

#check @ZeroParadox.occurrence_semidecidable_nonoccurrence_not
-- Statement: occurrence is an REPred; non-occurrence is not.
-- Reading: what can be witnessed runs one way only — the same asymmetry as
--   `t_snap_irreversible`, reached information-theoretically.

/-! ### § VI-b. The pole, its swap, and what actually blocks the snap -/

#check @ZeroParadox.flipPoles_involutive
-- Statement: exchanging the halted and self-looping poles twice is the identity.
-- Reading: the computational `rInv` / `swap`. **Level fence:** an automorphism of the SPACE of
--   machines, not of one machine — same shape at a different level, never an identity.

#check @ZeroParadox.flipPoles_preserves_extremal
-- Statement: extremal (halted or looping) stays extremal under the swap.
-- Reading: the pole is preserved as a set while its two elements exchange — `rInv` on {0, ∞}.

#check @ZeroParadox.flipPoles_fixes_progress
-- Statement: a configuration stepping onward to something else is left unchanged by the swap.
-- Reading: the interior is fixed — the unit circle under `rInv`.

#check @ZeroParadox.live_step_not_wellFounded
-- Statement: a self-looping configuration makes the step relation non-well-founded.
-- Reading: the bridge to `Multihomed/Boundary.lean`'s `floor_not_wellFounded` — the live/dead
--   split has the SHAPE of the ν/μ divide at a different level, never an identity with it.
--   ONE-DIRECTIONAL: the converse is false, and "dead" does NOT give
--   a well-founded relation.

#check @ZeroParadox.loops_not_unique
-- Statement: a machine can fix two distinct configurations.
-- Reading: self-loops need not be unique, so the step relation is not QuineHost-shaped and no
--   argument from ZP-J's uniqueness may be run on it.

#check @ZeroParadox.deterministic_has_no_fanout
-- Statement: a deterministic step admits at most one successor.

#check @ZeroParadox.nondeterministic_escapes_the_trap
-- Statement: a non-deterministic relation can self-loop AND reach something else.
-- Reading: what blocks the snap in § VI is DETERMINISM, not the self-loop —
--   `Miniature.lean`'s `pole_cannot_fan` in machine vocabulary.

#check @ZeroParadox.occurrence_shape
-- Statement: the five faces bundled — no unstarted state, the trichotomy, the pole preserved
--   under swap, the NO-GO, and the inversion.

/-! ### § VII. NO-GO gauges — what may NOT be inferred -/

#check @ZeroParadox.abstractSelfApp_always_inhabited
-- Statement: every `ZPSemilattice` carries an `AbstractSelfApp`, so no property of the carrier
--   follows from the bare hypothesis.

/-! ### § VIII. Ground zero — the bottom as a BEHAVIOUR, not a configuration

`ZeroParadox/Computability/GroundZero.lean`. Reads the step function as a coalgebra for
`X ↦ 1 + X` and connects it to `NatListRegime.lean`, which the project already carried. -/

#check @ZeroParadox.head_is_leaf_or_step
-- Statement: `(stepCoalg f s).1` is `false` or `true`. Axiom-free.
-- Reading: there is no "exists but has not begun" — the head type is `Bool`, so that state is
--   absent from the type rather than ruled out by argument.

#check @ZeroParadox.not_halted_is_stepping_head
-- Statement: `f s ≠ none → (stepCoalg f s).1 = true`. Axiom-free.
-- Reading: "already executing at ground zero, by definition." Capability and execution are not
--   separated in this model, so a capability that is not being exercised is not expressible.
--   NOT a claim that anything CAUSES execution.

#check @ZeroParadox.notEL_unique
-- Statement: `¬ EventuallyLeaf x → x = natInfinity`. A behaviour that never reaches a leaf is
--   uniquely `natInfinity`. A Lean `=` inside one type, by bisimulation.
-- Reading: the computational counterpart of `quine_unique` — the bottom pinned apophatically,
--   by what it never does, with no element-hood in any machine carrier assumed.

#check @ZeroParadox.loop_unfolds_to_infinity
-- Statement: a self-looping configuration's unfolding equals `natInfinity`.
-- Reading: the machine bottom's BEHAVIOUR and the coalgebraic infinity are the same point of the
--   final coalgebra. The `=` is between two `Cofix` elements, within one type; the configuration
--   `s : σ` is NOT equated with anything — it lives in a different type. (The home file states it
--   correctly: "the BEHAVIOUR of a self-looping machine configuration IS `natInfinity`"; an earlier
--   revision of this gloss dropped those words and asserted the identification was cross-type-free.)
--   It says nothing about whether the FRAMEWORK's bottom self-loops — that is the commitment.

#check @ZeroParadox.tri_unstarted_state_exists
-- Statement: with a three-valued head there IS a configuration neither halted nor stepping.
--   `TriStep` is a deliberate counter-model and must never be used as a framework object.

#check @ZeroParadox.forcing_needs_the_binary_split
-- Statement: both halves at once — two-valued, no unstarted state; three-valued, one exists.
-- Reading: what makes execution forced is the CLEANNESS OF THE SPLIT, not the dynamics; and the
--   framework takes that split to be a third encoding of AX-B1, beside `ax_b1_distinct` and
--   `HasFirstStep`. That the three are ONE commitment is an interpretation in the manner of
--   MC-1's bottom family — per-encoding membership is checkable, cross-encoding identity is
--   neither claimed nor well-formed.

#check @ZeroParadox.tsnap_holds_but_nothing_moves
-- Statement: T-SNAP holds in a dynamics where every state is fixed. It constrains the SHAPE of
--   a transition; it does not assert one occurs.

end ComputationCannotBeIndex
