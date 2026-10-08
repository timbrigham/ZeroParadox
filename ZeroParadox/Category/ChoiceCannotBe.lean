import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.SnapNucleus
import ZeroParadox.Ordinal.SnapNucleusConstructive
import ZeroParadox.Category.DoubleNegationNucleus
import ZeroParadox.Category.ExcludedMiddleBridge
import ZeroParadox.Valuation.PoleChartSelection
import ZeroParadox.Ordinal.SyntacticCollapse
import ZeroParadox.Computability.RootCutTrichotomy
import ZeroParadox.Computability.ChoicePurityInvariant
import ZeroParadox.Settheory.Wall
import ZeroParadox.Ordinal.OrdinalChoiceEssential
import ZeroParadox.Category.LawvereTaboo
import ZeroParadox.Computability.SelfCopyReference
import ZeroParadox.Order.PataraiaChoiceFree
import ZeroParadox.Order.PataraiaFromBourbakiWitt

/-!
# Machine-checked characterization index of the framework's relationship to `Classical.choice`

An index of the framework's relationship to `Classical.choice`, an ambient kernel axiom and not a
framework object. Every indexed name is `#check`ed, so the `import`s recompile each home file; it
creates no declarations. The `#check`s cannot overclaim; the comments can, so read every line that
is not a `#check` as unverified prose. Long form: `ZeroParadox/Category/ChoiceCannotBe.md`.

## Engineer's Take

We have built what bottom is not, and what the snap is not. The same kind of file for what choice is not
was in order, as a way to organize and reference that object.

---
-/

section ChoiceCannotBeIndex

/-! ## § I. What choice is NOT — choice-free proofs, beside the classical proofs they replace

Each `ZeroParadox` entry below has its footprint in its home file's `PurityCheck` section; the two Mathlib
entries at the end were measured with `#print axioms` directly. "NO axioms" means the fully axiom-free
footprint; `[propext]` means propositional extensionality only. -/

-- The framework's central theorem. T-SNAP's shape in its `MachinePhase` chart (`c₀ ≠ c₁`,
-- `join c₀ c₁ = c₁`) depends on NO axioms at all — not choice, not
-- `propext`, not `Quot.sound`. Whatever else the corpus carries, T-SNAP itself carries nothing.
#check @ZeroParadox.t_snap_derived

-- The excluded-middle modality ITSELF is choice-free: `a ↦ aᶜᶜ` as a genuine `Nucleus`, `[propext]`.
-- The point of the direction fence: had this leaked `Classical.choice` it would have been routing
-- through Diaconescu to build the very thing Diaconescu delivers.
#check @ZeroParadox.dnegNucleus

-- The lemma that made it possible, and the worked ACCIDENTAL case. Mathlib's `compl_compl_inf_distrib`
-- proves meet-preservation via `sup`/`compl_sup_distrib` and reports `Classical.choice`; this re-proof
-- stays on the MEET side and measures `[propext]`. The `sup` route is where the classical dependency
-- enters — that is the localization, not a general principle.
#check @ZeroParadox.dneg_inf_distrib

-- Selecting a chart at a two-ended pole: NO axioms. This is the direct refutation of the naive reading
-- that "viewing the pole as definitely the floor is an act of choice." Given `x₀ : X`, on `OnePoint X`
-- a selector exists that is constant on the pole orbit of `x₀`; empty `X` is not covered.
#check @ZeroParadox.chart_selection_is_freeG

-- The metric-collapse content on the syntactic side: `[propext]`. Contrast the measured
-- `[propext, Classical.choice, Quot.sound]` on `tower_converges_to_zero`. **These are DIFFERENT
-- statements on DIFFERENT carriers, not one statement rephrased** — the bridge `synVal` = 2-adic
-- valuation is NOT proved, and cannot be without importing the stack under investigation. So this is
-- EVIDENCE that the choice in the ℚ₂ statement is Mathlib-imposed, not a demonstration that the metric
-- collapse is choice-free. See `ZeroParadox/Ordinal/SyntacticCollapse.md`'s "What this does NOT establish".
#check @ZeroParadox.synCollapse_epsN
#check @ZeroParadox.synVal_mono

-- The ν-side inhabitation witnesses at the root cut: NO axioms. These matter because they REFUTE the
-- general form of "choice enters precisely where the diagonal fixed point is asserted inhabited."
-- Inhabiting a non-well-founded (greatest) fixed point can be entirely choice-free. FENCE: the
-- refutation is functor-specific, not universal — the QPF `Cofix` route in `ZeroParadox/Computability/ChoicePurityInvariant.lean`
-- (`cofix_nonempty'`) DOES carry `Classical.choice`. Located exactly, measured 2026-08-03: the M-type
-- FORMER and its constructors are axiom-free (`PFunctor.M`, `M.mk`, `M.corec`), its DESTRUCTOR is
-- not
-- (`M.children`, `M.dest` carry `[propext, Classical.choice, Quot.sound]`), and `QPF.Cofix` inherits
-- from the destructor through `Mcongr`/`IsPrecongr`. The two `#check`s below are axiom-free because
-- they only BUILD and never destruct. So: the general claim
-- is false; the per-functor question stays open case by case.
#check @ZeroParadox.strict_cofix_nonempty
#check @ZeroParadox.mixed_cofix_nonempty

-- The μ side of the same fork, emptiness witnessed by the bare inductive `WType` eliminator: NO axioms,
-- strictly tighter than `fix_isEmpty`'s (`[propext, Quot.sound]`).
#check @ZeroParadox.fix_isEmpty_constructive

-- Statement: `boundaryDouble` is one-to-one, not onto, and has exactly one fixed point; measured
-- `[propext, Quot.sound]`. That the point is `botEnd` is `boundaryDouble_botEnd` with
-- `boundaryDouble_unique_fp` (`ZeroParadox/Valuation/PoleCompletion.lean`), not this type.
#check @ZeroParadox.boundaryDouble_selfCopyRef
-- Statement: along a GIVEN `α ≃ ℕ`, a `SelfCopyRef` map exists on `α`; measured `[propext, Quot.sound]`.
#check @ZeroParadox.selfCopyRef_of_equiv_nat
-- Statement: an ACCIDENTAL case — over `[Fintype] [DecidableEq]` no `SelfCopyRef` map exists, re-proved at
-- `[propext, Quot.sound]`; Mathlib's `Finite.injective_iff_surjective` route reports `Classical.choice`.
#check @ZeroParadox.no_selfCopyRef_of_fintype

-- Statement: an ACCIDENTAL case — Pataraia's theorem (monotone `f` on `[CompletePartialOrder α]` has a
-- fixed point below every fixed point), proved via Bourbaki–Witt, measured `[propext, Classical.choice,
-- Quot.sound]`.
#check @ZeroParadox.dcpo_exists_least_fixedPoint
-- Statement: a fixed point below every PRE-fixed point, measured NO axioms; the `example` after it in
-- its home file derives the statement above from it in one line.
#check @ZeroParadox.pataraia_least_prefixedPoint
-- Statement: Pataraia induction — for monotone `f` on `[CompletePartialOrder α]`, a set containing `⊥`,
-- closed under `f` and under sups of nonempty directed subsets, contains every fixed point lying below
-- every fixed point; proved via Bourbaki–Witt, measured `[propext, Classical.choice, Quot.sound]`.
#check @ZeroParadox.pataraia_induction
-- Statement: the same signature as `pataraia_induction`, measured NO axioms.
#check @ZeroParadox.pataraia_induction_constructive
-- Statement: Mathlib, on a nonempty chain-complete partial order every inflationary `f`
-- (`x ≤ f x`) has a fixed point; measured `[propext, Classical.choice, Quot.sound]`.
-- Reading: both classical proofs above call it.
#check @ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary
-- Statement: for any `x y` of any `Sort`, `x = y ∨ x ≠ y`; measured
-- `[propext, Classical.choice, Quot.sound]`.
-- Reading: the case split in both classical proofs' chain-to-directed step.
#check @eq_or_ne
-- Reading: scoped to the ORDER-THEORETIC principle; `⊥` here is the dcpo's least element, and whether a
-- ZP carrier is a dcpo with a monotone self-map is not claimed.

/-! ## § II. What choice is NOT to be confused with — the excluded-middle boundary

The modality of §I generates classical LOGIC — excluded middle — which is strictly weaker than **full**
choice (Cohen 1963). The RESTRICTED fragment is a different matter: see `ZeroParadox/Category/ChoiceCannotBe.md`. This section indexes
the boundary and its scope fence. -/

-- What the modality's closed points actually are: the regular elements `aᶜᶜ = a` — the Boolean core.
-- That is the whole of "generates classical logic", and it is NOT choice.
#check @ZeroParadox.dnegNucleus_isClosed_iff

-- Excluded middle ⟺ every `Prop` is a closed point of the nucleus. Scoped to `Prop`; see the fence below.
#check @ZeroParadox.em_iff_dnegNucleus_trivial

-- DIACONESCU, hypothesis form: a choice fragment implies excluded middle. PRIOR ART, not a framework
-- result: Diaconescu (1975), "Axiom of choice and complementation"; independently Goodman–Myhill (1978),
-- "Choice implies excluded middle". The framework contributes only the hypothesis-form packaging (Lean's
-- kernel realizes the arrow as a derivation, not a reusable theorem).
-- DIRECTION, stated precisely. Diaconescu's theorem is
-- an EQUIVALENCE for this restricted shape (choice for inhabited subobjects of a two-element object IS
-- excluded middle); "the converse fails" belongs to FULL AC and is Cohen 1963, not Diaconescu.
-- Reading: in `ZeroParadox/Category/ExcludedMiddleBridge.lean` the natural construction of the fragment
-- from `ExcludedMiddle` fails to elaborate without `classical`, and a candidate explanation is Lean's
-- `Prop`/`Type` stratification. A failed construction is not a non-derivability result, so this is a
-- candidate, not a finding.
#check @ZeroParadox.em_of_choiceFragment

-- THE SCOPE FENCE. Excluded middle does NOT make an arbitrary Heyting algebra Boolean: the middle
-- element of the three-element chain has `1ᶜᶜ = 2 ≠ 1`, exhibited inside a classical metatheory where
-- excluded middle is fully available. Scope every "collapses the nucleus" claim to `Prop`.
#check @ZeroParadox.fin3_middle_not_closed_point

-- The Lawvere boundary underneath all of it: logical negation has no fixed point, `¬(p ↔ ¬p)`.
#check @ZeroParadox.negation_no_fixedpoint

-- Statement: the limited principle of omniscience at ⊥ of `ℕ → Bool` (the all-false tape, pointwise
-- order): every tape is ⊥ or has a witnessed `true` is equivalent to the weak limited principle of
-- omniscience (every tape is ⊥ or is not ⊥) together with Markov's principle (a tape that is not ⊥
-- has a witnessed `true`).
-- Reading: the standard ladder, not a finding. This bit-tape form (α ∈ 2^ℕ) is Escardó, "Infinite
-- sets that satisfy the principle of omniscience in any variety of constructive mathematics",
-- J. Symbolic Logic 78(3) (2013) 764–784, doi 10.2178/jsl.7803040, § 3, which also restates all three
-- as questions about the point ∞ = 1^ω of ℕ∞; with `true` and `false` exchanged, that point is this ⊥.
-- The form over ℕ^ℕ is Ishihara, "Reverse mathematics in Bishop's constructive mathematics"
-- (Philosophia Scientiae CS 6, 2006), § 6, Prop 10.1, p. 53.
example :
    (∀ f : ℕ → Bool, f = ⊥ ∨ ∃ n, f n = true) ↔
      (∀ f : ℕ → Bool, f = ⊥ ∨ f ≠ ⊥) ∧ (∀ f : ℕ → Bool, f ≠ ⊥ → ∃ n, f n = true) := by
  refine ⟨fun h => ⟨fun f => (h f).imp id fun ⟨n, hn⟩ heq => ?_, fun f hf => (h f).resolve_left hf⟩,
    fun ⟨hw, hm⟩ f => (hw f).imp id (hm f)⟩
  rw [heq] at hn; cases hn

/-! ## § III. What IS established about choice here

Not "what choice is" — that is Lean's, not the framework's. What this corpus has actually measured or
proved about where choice does work. -/

-- A CHOICE-CARRYING CASE, indexed on purpose. Everything in § I is a negative result, which risks
-- reading as "the framework is choice-free". It is not, and this entry is the counterweight.
-- Statement: `Nonempty (Cofix idPF_Coalgebra.Obj)` — the ν side is inhabited. Footprint measured
-- `[propext, Classical.choice, Quot.sound]`.
-- Measurement (2026-08-03, about the AMBIENT TYPES rather than about this declaration — hence no
-- Statement:/Reading: label, which belong to claims about the checked decl): `QPF.Cofix` carries
-- `Classical.choice` IN THE TYPE, so no proof of any `Cofix`-mentioning statement is choice-free;
-- while `PFunctor.M`'s former and constructors are axiom-free (its DESTRUCTOR is not) and
-- `strict_cofix_nonempty` proves the same ν-inhabitation over
-- it with NO axioms.
-- Reading: the framework therefore attributes this footprint to Mathlib's QPF *quotient layer*
-- rather than to the mathematics — escaping it means changing the carrier, not cleaning the proof.
-- (Setting: ACS's construction needs only function extensionality, which Lean has; only its
-- uniqueness half uses univalence. See ZeroParadox/Computability/ChoicePurityInvariant.lean.)
-- Contrast `strict_cofix_nonempty` (§ I, NO axioms): same phenomenon, different construction,
-- opposite footprint. That contrast is the accidental/essential distinction in one pair.
#check @ZeroParadox.cofix_nonempty'

-- THE TWO MODALITIES, side by side — the comparison a reader arrives wanting. `snapNucleus`
-- (⊥ of `Ordinal` ↦ ε₀) inherits `Classical.choice` from Mathlib's `Ordinal` fixed-point machinery;
-- `dnegNucleus` (§ I) is `[propext]`. Both are difference-generators seeded at their carrier's ⊥ —
-- negation satisfies `a ⇨ ⊥ = aᶜ` (the class law `himp_bot`), and `HeytingAlgebra` extends `OrderBot`,
-- so ⊥ of the Heyting algebra is part of the structure negation lives in. Same role, different carriers, opposite footprints, and
-- opposite behaviour AT the seed: `dnegNucleus` fixes ⊥ of the Heyting algebra (⊥ is always regular),
-- `snapNucleus` provably moves ⊥ of `Ordinal` (`snapNucleus_bot_ne_bot`). On the footprint difference: `snapNucleus`
-- has **not been re-proved choice-free as of 2026-08-02**, so do not call it merely representational. What ZP-N
-- re-proved is the ordinal *ascent* (`exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono` on
-- `ONote`), which is suggestive for the nucleus and is not the nucleus. Its `Classical.choice` is
-- UNCLASSIFIED — the honest tier. Choice is NOT in the `Ordinal` type: `Ordinal` measures
-- `[propext, Quot.sound]`. The choice
-- enters through the order instance and the operations (`Ordinal.instLinearOrder`, `nfp`, `omega0`,
-- `epsilon`, each `[propext, Classical.choice, Quot.sound]`). UNCLASSIFIED means simply that nobody has
-- re-proved it choice-free — an open question, not a demonstrated obstruction.
#check @ZeroParadox.snapNucleus
#check @ZeroParadox.snapNucleus_bot_ne_bot

-- THE SAME LOCATION FOR `Code`, measured 2026-09-19:
-- `Nat.Partrec.Code` is axiom-free and so is `Nat.Partrec.Code.eval`, so the choice is not "in
-- the `Code` type" either. It enters through Mathlib's `Denumerable Code` instance, reached by
-- `Encodable.encode` — so the two SPELLINGS of one code's Gödel number differ:
-- `ZeroParadox.encodeCode_self` measures NO axioms while `ZeroParadox.encode_self` carries the
-- triple, although `encode = encodeCode` holds by `rfl`. Both are `rfl` and do no work.
-- Home: `ZeroParadox/Computability/Kleene.lean` § VII declares the pair; its `PurityCheck`
-- section emits the two `#print axioms` lines. ⚠ Prose, not a `#check` — this index does not
-- import `Kleene.lean`, so read it as unverified here and check it there.
-- ⛔ NO RULE about which declarations carry this footprint is stated here or in ZP-K § IV (a claim
-- about those two sites, not a swept absence claim about the corpus). ZP-K § IV holds a dated
-- measurement table instead, which is `ZeroParadox/Category/ChoiceCannotBe.md`'s § "No count is
-- recorded here" discipline applied to provenance rather than to counts.

-- AND THE NATURAL COUNTERPART ROUTE IS BLOCKED — the attempt was made, and it failed provably.
-- `no_snap_closure`: no idempotent endomap of the notation carrier has the ε-numbers as its closed
-- points. Idempotence alone suffices; `no_snap_nucleus` is the `Nucleus`-typed corollary, and its
-- quantifier ranges over an inhabited type: `idNucleus` is a nucleus on that carrier.
-- **READ THE OBSTRUCTION CORRECTLY — it is NOT about choice.** Every proof in that file is `[propext]`.
-- What blocks the counterpart is EXPRESSIVE REACH: the carrier cannot name what the closure produces,
-- because ε₀ is the supremum of Cantor normal form rather than a member. So this does NOT make
-- `snapNucleus`'s footprint accidental, does NOT make it essential, and does NOT show the snap nucleus
-- is constructively impossible in general — a notation system extending past ε₀ is untouched and open.
-- It closes one route and leaves the classification exactly where it was: UNCLASSIFIED.
#check @ZeroParadox.no_snap_closure
#check @ZeroParadox.no_snap_nucleus
#check @ZeroParadox.idNucleus

-- Statement: every infinite type carries a `SelfCopyRef` map; measured with `Classical.choice`, UNCLASSIFIED.
-- Cited, not claimed: in set theory without choice the analogue is unprovable (Banakh,
-- arXiv:2006.01613v4, Rem. 43.14); dependent choice gives a one-to-one, not-onto self-map
-- (Prop. 43.12), and the unique fixed point is not in that result.
#check @ZeroParadox.exists_selfCopyRef_of_infinite

-- The choice fragment is NON-VACUOUS: `Classical.choice` supplies it. Without this, `em_of_choiceFragment`
-- could be dismissed as an implication with an unsatisfiable hypothesis. Classical by construction —
-- it is the SOURCE end of the arrow.
#check @ZeroParadox.choiceFragment_of_classical

-- Choice suffices for uniform chart selection at the (stipulated) undetermined pole — again the source
-- end, again non-vacuity rather than necessity.
#check @ZeroParadox.uniformChartSelection_of_classical

-- And the pole's uniform-selection principle IS the choice fragment — definitionally (`Iff.rfl`). The
-- pole vocabulary is a renaming, and renaming a hypothesis does not make it true.
#check @ZeroParadox.uniformChartSelection_iff_choiceFragment

-- THE CONTRAST THAT LOCALIZES THE WORK: when the predicate is DECIDABLE, selection is free — computed
-- by `if`, no choice, no excluded middle. So choice is not doing work at "selection"; it is doing work
-- at "the predicate is undecided." That is where to look for an essential case, and where the
-- framework's own built pole (`builtChartAdmissible`, decidable) is not.
#check @ZeroParadox.select_of_decidable

-- THE INSTANCE HAZARD — the most practically dangerous item in this index. `Prop` carries TWO relevant
-- order instances on the SAME object. `Prop.instBooleanAlgebra` discharges its `top_le_sup_compl` field
-- with `Classical.em` and so carries `Classical.choice` IN ITS OWN TERM; `Prop.instHeytingAlgebra` is
-- `[propext]`. A `Prop`-scoped statement that does not PIN its instance can silently resolve through the
-- Boolean one and acquire choice — which would make every choice-freeness claim about `Prop` vacuous.
-- Every `Prop`-scoped statement in `ZeroParadox/Category/ExcludedMiddleBridge.lean` pins `@… Prop Prop.instHeytingAlgebra`
-- explicitly for this reason. Pin the instance, or measure nothing.
#check @Prop.instHeytingAlgebra
#check @Prop.instBooleanAlgebra

/-! ## § IV. The ESSENTIAL cases — two reductions to taboos, and the premise they rest on

The arrow runs from the principle to the taboo, so each theorem speaks of the principle, not of any one
proof of it. ESSENTIAL, in the sense of § "Accidental versus essential" of
`ZeroParadox/Category/ChoiceCannotBe.md`, means that no proof of the principle in Lean's choice-free
fragment (the kernel with `propext` and `Quot.sound` as its only axioms) exists, GIVEN that the taboo
the case reaches is not derivable in that fragment. That premise is not proved in this corpus; without
it, what is proved is that a choice-free proof of the principle would be a choice-free proof of the
taboo. Neither case is an independence result, and neither says the framework's overall use of choice
is essential. -/

-- Each case is a reduction proved without `Classical.choice` (`[propext, Quot.sound]`), from a classical
-- principle the framework uses to a constructive taboo: case 1 from comparability of well-orders to
-- excluded middle, case 2 from the fixed-point-free principle over arbitrary `Type` to weak excluded
-- middle.

-- ESSENTIAL CASE 1 — comparability of well-orders implies EXCLUDED MIDDLE. Mathlib's `le_total` on
-- `Ordinal` has exactly this shape, which is what puts it in the framework's path.
-- PRIOR ART, not a framework result: Kraus-Nordvall Forsberg-Xu, arXiv:2104.02549, **Theorem 38(d)** —
-- there in the DATA form (`⊎`) and as a paper proof, not covered by their Agda development. The
-- framework's contribution is the propositional (`∨`) form, on their witnesses.
#check @ZeroParadox.em_of_wellOrder_comparable

-- Non-vacuity, the source end of the arrow: Mathlib's `InitialSeg.total` supplies the hypothesis and
-- spends a literal `Classical.choice` in its final branch. Without this the reduction could be dismissed
-- as an implication with an unsatisfiable antecedent.
#check @ZeroParadox.comparable_of_classical

-- ESSENTIAL CASE 2 — the general fixed-point-free principle implies WEAK excluded middle, and this one
-- sits on the KEYSTONE (the diagonal engine) rather than on an imported order instance. Its hypothesis
-- is the ∀-closure of `ZeroParadox/Category/Lawvere.lean`'s `fixedPointFree_of_nontrivial` at `Type`, and every
-- proof of that theorem's statement instantiates to it (`fixedPointFree_of_classical`), so that theorem's
-- `classical` is essential in the sense of the header above, and on its premise.
#check @ZeroParadox.wem_of_fixedPointFree

-- Non-vacuity again: `fixedPointFree_of_nontrivial` supplies the hypothesis, classically by
-- construction. Contrast `select_of_decidable` (§ III) — where the predicate is decidable the work
-- disappears; the classical content lives at "undecided", not at "chooses".
#check @ZeroParadox.fixedPointFree_of_nontrivial

-- AND THE ESCAPE, WHICH IS THE HALF THAT MAKES CASE 2 USEFUL RATHER THAN ALARMING. "Essential" scopes
-- to the GENERAL principle, quantified over arbitrary `Type`. Restrict the carrier to decidable
-- equality and the same statement is choice-free — measured `[propext]`, against the general form's
-- `[propext, Classical.choice, Quot.sound]`. `ZeroParadox/Category/DiagonalWitness.lean`'s `no_witnessRel_top_of_nontrivial`
-- carries the same audit for the level-set form. **Where a carrier has `DecidableEq`, the essential
-- form is not needed** — the taboo says the general statement cannot be re-proved constructively, and
-- the restriction says it does not have to be *there*. Together they localize the classical content
-- rather than obstruct it: they say where it lives and how far it reaches.
-- SCOPE: how far the escape reaches is UNSURVEYED. Which carriers in this corpus have `DecidableEq`
-- was unmeasured as of 2026-08-02, so "the restriction covers what we need" is unverified in general — and a
-- universal over every carrier would be the sentence shape `ZeroParadox/Category/ChoiceCannotBe.md`'s § "No count" warns about.
-- The two `#check`ed declarations are what is established; the reach is not.
#check @ZeroParadox.fixedPointFree_of_nontrivial_decidable

end ChoiceCannotBeIndex
