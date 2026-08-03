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

/-!
# Machine-checked characterization index of the framework's relationship to `Classical.choice`

A fourth index, **not a fourth framework object** — alongside `ZeroParadox/BottomCannotBe.lean`,
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` and `ZeroParadox/Order/SnapCannotBe.lean`. A `#check`-only
index: it states no new results and reproduces no logic. Every line `#check`s an already-proven
declaration in its home file, and the `import`s force those files to compile, so the index cannot point
at a dead or renamed result. A `#check`-only index creates no declarations, so **the `#check` LINES**
cannot overclaim. **The prose around them absolutely can, and in this file it did** — § IV records a
universal negative that stood here while two counterexamples sat in the corpus. Read every claim below
that is not a `#check` as ordinary unverified prose.

## Engineer's Take

We have built what bottom is not, and what the snap is not. The same kind of file for what choice is not
was in order, as a way to organize and reference that object.

---

## Formal Overview (AI-assisted)

**How this index differs from the other three.** Those index the framework's OWN objects — ⊥, the snap,
ε₀ — things the framework constructs. `Classical.choice` is **not** a framework object. It is an ambient
axiom of Lean's kernel, present whether or not this project exists. So this file indexes something
different: **the framework's relationship to choice** — where choice is provably not needed, what choice
must not be confused with, and what is actually established about it here. Nothing below should be read
as the framework claiming choice as one of its constructions, or as a claim about choice in general.

### The headline fence — read this before anything else

The ordinary English word "choice" — an act of picking, adopting a point of view, selecting a chart —
and the kernel axiom `Classical.choice` are **not the same thing**, and conflating them is this
framework's standing temptation. The literature that separates them:

> **Diaconescu (1975)** (independently Goodman–Myhill 1978): in a topos, the axiom of choice implies
> excluded middle. His theorem is stated as an **equivalence** — a coequalizer of two nonintersecting
> monomorphisms has a section *iff* subobjects have complements (p. 176); "AC implies complemented
> subobjects" is the corollary (p. 178). In modern terms: choice for inhabited subobjects of a
> two-element object **is** excluded middle.
>
> **Cohen (1963)**, with Fraenkel–Mostowski: *full* AC is strictly stronger than excluded middle. This
> is an independence result about ZF, **not** anything Diaconescu proved — do not attribute it to him.

So *full* choice is strictly stronger than excluded middle, which is in turn strictly stronger than the
constructive base. **The restricted fragment is a different matter, and the distinction matters here.**
`ZeroParadox/Category/ExcludedMiddleBridge.lean`'s `ChoiceFragment` has exactly Diaconescu's shape — choice for inhabited
predicates on `Bool` — so in a topos it would be *equivalent* to excluded middle. In Lean it **appears
not to be**: the natural construction of the fragment from excluded middle fails to elaborate, dying at
`Decidable (S true)`, and closes only under `classical`. **That is strong evidence, not a proof of
unprovability** — a failed elaboration is not a negative result, and a formal independence claim would
need a metatheoretic argument outside Lean (the home file
`ZeroParadox/Category/ExcludedMiddleBridge.lean` states this limit explicitly). The apparent gap is a
fact about **Lean's `Prop`/`Type` stratification**, not about Diaconescu's theorem: the fragment selects
into `Bool`, so it is really `∀ p, Decidable p` — data-valued excluded middle — while `ExcludedMiddle` is
the `Prop`-valued form, and `Or` in `Prop` does not eliminate into `Bool`. A topos has no such split,
which is why Diaconescu gets an equivalence and we do not. **That reconciliation is the framework's own
small finding; the equivalence is his.** Every evocative reading in the framework's prose — "choice is which way you view the
self-dual split", "reading the pole as the floor is an act of choice" — is a **model** of the
choice-versus-no-choice distinction, never the axiom itself. Where such a reading has been made precise
(`ZeroParadox/Valuation/PoleChartSelection.lean`), the honest result was that the built object **refutes** the naive
form: selection there is free, and the non-constructivity in the conditional model is *inserted by
stipulation* at `poleAdmissible`, not discovered in the pole. Two files carry a written correction of
record on exactly this error — `ZeroParadox/Category/DoubleNegationNucleus.lean` (once titled "choice as a
difference-generator"; it is the *excluded-middle* modality) and `ZeroParadox/Category/ExcludedMiddleBridge.lean`
(once stated unscoped, as though excluded middle made every Heyting algebra Boolean).

### No count is recorded here, deliberately

**This file states no figure for how many declarations carry `Classical.choice`, and none should be added
to it.** Three reasons, in order of importance.

**A count mostly measures Mathlib, not this framework.** Most choice footprints traced so far come from a
Mathlib construction — the `Ordinal` type, `NONote.repr`, the recursion-theorem proof,
`compl_sup_distrib`, arbitrary-type decidability, a `ℚ` division-ring instance, in one case a single
tactic call. **Not all: `ZeroParadox/Category/Lawvere.lean:70`'s bare `classical` in
`fixedPointFree_of_nontrivial` is the framework's own, and § IV shows it is ESSENTIAL** — the cost is in
stating the swap over types **whose equality is not decidable** (the swap is `if x = b₀ then b₁ else b₀`;
decidable equality is exactly what the § IV escape restores), which is the framework's chosen
generality, not Mathlib's. So a corpus-wide
total still mixes the two sources and still reads as a property of this project, which is reason enough
not to record one; but it is not true that the framework contributes none.

**It invites precisely the wrong conclusion.** A large choice-carrying fraction reads as "most of this
framework is non-constructive." The load-bearing fact is the opposite and much narrower: **T-SNAP, the
core, is axiom-free** (`t_snap_derived` — no axioms at all, not even `propext`). Beyond it the picture
is mixed and the categories are what matter, not a total: some footprints are *accidental* (a choice-free
re-proof exists — two carried out, § I), two are **ESSENTIAL** (§ IV), and others are **UNCLASSIFIED**,
meaning nobody has tried. A count collapses those three into one number and loses the only distinction
that carries information.

**And in practice the number will not stay right.** It has been wrong three times. The first version was
quoted rather than measured and was off by more than an order of magnitude. The replacement was measured
correctly and went stale within the same session, because further files landed before it was written
down; a claim-review referee caught it. The figure that then sat in the project's operating manual was
stale again by the following review, for the same reason. All three are one error — citing a figure that
is not being regenerated at the moment of use — and a docstring cannot regenerate anything.

What is true, and is what this file asserts instead: **the framework is not choice-free; the core is
(`t_snap_derived`, no axioms at all); examined footprints fall into three classes — accidental,
essential, unclassified — and § I and § IV name the cases in the first two.** No fraction is given, for
the reason stated above.

**⚠ THE STANDING LESSON, and it is why this paragraph was rewritten.** This sentence used to read
*"every examined footprint has been removable — that statement does not go stale."* It was falsified
the next day (§ IV's two cases, committed 2026-07-20), had been copied into `CLAUDE.md` as the
recommended safe formulation, and was contradicted by `RELEASES.md` for ten days with nothing to
reconcile them. **A universal negative is the most dangerous sentence shape in a `CannotBe` index:**
the `#check` lines cannot overclaim, but prose quantified over *the whole framework* is falsified by
any single future commit and nothing mechanical notices.
**Write "none located as of <date>", never "none exists."**

**If you want a count, measure it — do not look for one to cite.** Every `ZeroParadox` file carries a
`PurityCheck` section, so a full build emits one `#print axioms` line per indexed declaration. From the
repository root (PowerShell), as two separate calls:

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```
```
$all = Get-Content build.log | Select-String -Pattern "depends on axioms|does not depend on any axioms"
"total:       $($all.Count)"
"with choice: $(($all | Where-Object { $_ -match 'Classical.choice' }).Count)"
"axiom-free:  $(($all | Where-Object { $_ -match 'does not depend' }).Count)"
$f = $all | ForEach-Object { if ($_ -match '(ZeroParadox[/\\][^:]+\.lean)') { $matches[1] } } |
     Sort-Object -Unique
"files:       $($f.Count)"
```

**The build must be a full one.** `lake build` emits `#print axioms` lines only for modules it builds or
replays in that invocation, so a targeted build (`lake build ZeroParadox.Some.Module`) undercounts, and a
count taken before later files were added is stale the moment they land. Re-run the whole snippet at the
moment you cite it.

The counts are of emitted *reports*, so a declaration `#check`ed in more than one file is counted once
per report; the total therefore exceeds the number of distinct declarations. Whatever it returns is a
fact about the build you just ran, not a fact to carry anywhere.

**The survey is partial, and that is the honest caveat that matters.** Only some footprints have been
traced to a source and classified; much of the corpus is unexamined. **The hypothesis that every
footprint is accidental was held here until 2026-08-01 and is REFUTED** — § IV exhibits two that are
not. What survives is narrower and is a statement about method, not about the corpus: *where a footprint
has been examined, it has been **assigned** a class* — accidental, essential, or unclassified. (Not
"classifiable": with `unclassified` among the buckets, classifiability holds of everything and says
nothing. Corrected 2026-08-01.) Do not
upgrade that, and — for the same reason no count is recorded above — **do not quantify the examined
fraction either**; it moves with every commit.

### Accidental versus essential

* **ACCIDENTAL** — a choice-free re-proof exists. Detected by *re-proving*, which is the only
  demonstration available: `dneg_inf_distrib` (§ I) is the worked example — Mathlib's route through
  `compl_sup_distrib` reports `Classical.choice`; staying on the meet side drops it to `[propext]`.
  `ZeroParadox/Ordinal/SyntacticCollapse.lean` records another: a single tactic call was the whole footprint.
* **ESSENTIAL** — the theorem implies excluded middle, or a choice fragment, over an intuitionistic
  base. **Two are located: § IV.** Detected by *reducing* — deriving a taboo from the principle — which
  is the mirror image of the accidental test: accidental is shown by re-proving without choice, essential
  by showing that re-proving without choice would decide a taboo. Note this is a statement about the
  PRINCIPLE, not about any one proof of it: `#print axioms` reports a proof's footprint and can never
  witness necessity, which is exactly why the essential side needs a reduction instead of a measurement.

Prior art for the distinction and its methods: constructive reverse mathematics (Ishihara;
Diener–Ishihara). Cited, not claimed.

### What this index does NOT do

It does **not** claim the framework is choice-free — it is not. It does **not** claim any
footprint is provably removable beyond the specific cases actually re-proved. **On the negative side it
claims exactly two non-removability results, and neither comes from a measurement** — § IV's cases are
**reductions**, and that is the only route available: `#print axioms` reports **a proof's** footprint,
never **a theorem's** necessity. A choice-carrying proof is evidence about how the proof was written,
and nothing more; to show a principle *needs* choice you must derive a taboo from it.
-/

section ChoiceCannotBeIndex

/-! ## § I. What choice is NOT — where the framework provably does not need it

Each entry below is a measured purity result in its home file's `PurityCheck` section. "NO axioms" means
the fully axiom-free footprint; `[propext]` means propositional extensionality only. -/

-- The framework's central theorem. The snap ⊥ → ε₀ depends on NO axioms at all — not choice, not
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
-- that "viewing the pole as definitely the floor is an act of choice." At every one-point
-- compactification there is a canonical selector, constant on the pole orbit.
#check @ZeroParadox.chart_selection_is_freeG

-- The metric-collapse content on the syntactic side: `[propext]`. Contrast the measured
-- `[propext, Classical.choice, Quot.sound]` on `tower_converges_to_zero`. **These are DIFFERENT
-- statements on DIFFERENT carriers, not one statement rephrased** — the bridge `synVal` = 2-adic
-- valuation is NOT proved, and cannot be without importing the stack under investigation. So this is
-- EVIDENCE that the choice in the ℚ₂ statement is Mathlib-imposed, not a demonstration that the metric
-- collapse is choice-free. See `ZeroParadox/Ordinal/SyntacticCollapse.lean`'s "What this does NOT establish".
#check @ZeroParadox.synCollapse_epsN
#check @ZeroParadox.synVal_mono

-- The ν-side inhabitation witnesses at the root cut: NO axioms. These matter because they REFUTE the
-- general form of "choice enters precisely where the diagonal fixed point is asserted inhabited."
-- Inhabiting a non-well-founded (greatest) fixed point can be entirely choice-free. FENCE: the
-- refutation is functor-specific, not universal — the QPF `Cofix` route in `ZeroParadox/Computability/ChoicePurityInvariant.lean`
-- (`cofix_nonempty'`) DOES carry `Classical.choice`, as a Mathlib M-type artifact. So: the general claim
-- is false; the per-functor question stays open case by case.
#check @ZeroParadox.strict_cofix_nonempty
#check @ZeroParadox.mixed_cofix_nonempty

-- The μ side of the same fork, emptiness witnessed by the bare inductive `WType` eliminator: NO axioms,
-- strictly tighter than the earlier `fix_isEmpty` (`[propext, Quot.sound]`).
#check @ZeroParadox.fix_isEmpty_constructive

/-! ## § II. What choice is NOT to be confused with — the excluded-middle boundary

The modality of §I generates classical LOGIC — excluded middle — which is strictly weaker than **full**
choice (Cohen 1963). The RESTRICTED fragment is a different matter: see the header. This section indexes
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
-- DIRECTION, stated precisely — an earlier version of this comment had it wrong. Diaconescu's theorem is
-- an EQUIVALENCE for this restricted shape (choice for inhabited subobjects of a two-element object IS
-- excluded middle); "the converse fails" belongs to FULL AC and is Cohen 1963, not Diaconescu. That the
-- fragment nonetheless does not follow from `ExcludedMiddle` *in Lean* is a fact about Lean's
-- `Prop`/`Type` stratification, measured in `ZeroParadox/Category/ExcludedMiddleBridge.lean`, and is the framework's own
-- finding rather than Diaconescu's.
#check @ZeroParadox.em_of_choiceFragment

-- THE SCOPE FENCE. Excluded middle does NOT make an arbitrary Heyting algebra Boolean: the middle
-- element of the three-element chain has `1ᶜᶜ = 2 ≠ 1`, exhibited inside a classical metatheory where
-- excluded middle is fully available. Scope every "collapses the nucleus" claim to `Prop`.
#check @ZeroParadox.fin3_middle_not_closed_point

-- The Lawvere boundary underneath all of it: logical negation has no fixed point, `¬(p ↔ ¬p)`.
#check @ZeroParadox.negation_no_fixedpoint

/-! ## § III. What IS established about choice here

Not "what choice is" — that is Lean's, not the framework's. What this corpus has actually measured or
proved about where choice does work. -/

-- A CHOICE-CARRYING CASE, indexed on purpose. Everything in § I is a negative result, which risks
-- Statement: `Nonempty (Cofix idPF_Coalgebra.Obj)` — the ν side is inhabited. Footprint measured
-- `[propext, Classical.choice, Quot.sound]`.
-- Reading: the framework does NOT read this as "the framework is choice-free" — it is not.
-- This is the ν-side inhabitation
-- via Mathlib's QPF `Cofix`, measured `[propext, Classical.choice, Quot.sound]`. Its home file argues
-- the footprint is a library artifact of the M-type construction rather than a necessity, citing
-- Ahrens-Capriotti-Spadotti that polynomial final coalgebras are choice-free in principle.
-- (Setting: ACS's construction needs only function extensionality, which Lean has; only its
-- uniqueness half uses univalence. See ZeroParadox/Computability/ChoicePurityInvariant.lean.)
-- Contrast `strict_cofix_nonempty` (§ I, NO axioms): same phenomenon, different construction,
-- opposite footprint. That contrast is the accidental/essential distinction in one pair.
#check @ZeroParadox.cofix_nonempty'

-- THE TWO MODALITIES, side by side — the comparison a reader arrives wanting. `snapNucleus` (⊥ ↦ ε₀)
-- inherits `Classical.choice` from Mathlib's `Ordinal` fixed-point machinery; `dnegNucleus` (§ I) is
-- `[propext]`. Both are difference-generators seeded at ⊥ — negation is DEFINED as `a ⇨ ⊥`, and
-- `HeytingAlgebra` extends `OrderBot`, so ⊥ is required before negation exists at all. Same seed,
-- opposite footprints, and opposite behaviour AT the seed: `dnegNucleus` fixes ⊥ (⊥ is always regular),
-- `snapNucleus` provably moves it (`snapNucleus_bot_ne_bot`). On the footprint difference: `snapNucleus`
-- has **not been re-proved choice-free as of 2026-08-02**, so do not call it merely representational. What ZP-N
-- re-proved is the ordinal *ascent* (`exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono` on
-- `ONote`), which is suggestive for the nucleus and is not the nucleus. Its `Classical.choice` is
-- UNCLASSIFIED — the honest tier. NOT because "choice is in the `Ordinal` type": that claim was
-- asserted here earlier and is FALSE as measured — `Ordinal` is `[propext, Quot.sound]`. The choice
-- enters through the order instance and the operations (`Ordinal.instLinearOrder`, `nfp`, `omega0`,
-- `epsilon`, each `[propext, Classical.choice, Quot.sound]`). UNCLASSIFIED means simply that nobody has
-- re-proved it choice-free — an open question, not a demonstrated obstruction.
#check @ZeroParadox.snapNucleus
#check @ZeroParadox.snapNucleus_bot_ne_bot

-- AND THE NATURAL COUNTERPART ROUTE IS BLOCKED — the attempt was made, and it failed provably.
-- `no_snap_closure`: no idempotent endomap of the notation carrier has the ε-numbers as its closed
-- points. Idempotence alone suffices; `no_snap_nucleus` is the `Nucleus`-typed corollary, non-vacuous
-- because `idNucleus` exhibits nuclei on that carrier.
-- **READ THE OBSTRUCTION CORRECTLY — it is NOT about choice.** Every proof in that file is `[propext]`.
-- What blocks the counterpart is EXPRESSIVE REACH: the carrier cannot name what the closure produces,
-- because ε₀ is the supremum of Cantor normal form rather than a member. So this does NOT make
-- `snapNucleus`'s footprint accidental, does NOT make it essential, and does NOT show the snap nucleus
-- is constructively impossible in general — a notation system extending past ε₀ is untouched and open.
-- It closes one route and leaves the classification exactly where it was: UNCLASSIFIED.
#check @ZeroParadox.no_snap_closure
#check @ZeroParadox.no_snap_nucleus
#check @ZeroParadox.idNucleus

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

/-! ## § IV. The ESSENTIAL cases — where the choice is NOT removable

Added 2026-08-01. Both were committed 2026-07-20, one day after this index was last touched, and the
index went on asserting the opposite until this section landed. They satisfy § "Accidental versus
essential"'s own definition of ESSENTIAL: each derives a **taboo** — excluded middle, or its weak form —
from a classical principle the framework uses.

**Read the logical shape before citing either.** The theorems are themselves *choice-free reductions*:
the classical content sits entirely in the **hypothesis**, which is what makes each an implication rather
than a restatement. What is established is about the **principle**, not about any particular proof:
re-proving that principle constructively would decide a taboo, so no choice-free re-proof is available.
**The premise that step rests on, named rather than left implicit** (this file demands exactly that at
§ "the equivocation" above, then used it here without naming it — corrected 2026-08-01): *excluded
middle, and weak excluded middle, are not derivable in Lean's choice-free fragment.* That is standard
and is **not** proved here — it is a metatheoretic fact about the ambient type theory, not a Lean
theorem, and it is the only thing licensing "no choice-free re-proof exists" rather than the weaker
"none is known".
Neither says the framework's overall use of choice is essential, and neither is an independence result. -/

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
-- is the ∀-closure of `ZeroParadox/Category/Lawvere.lean`'s `fixedPointFree_of_nontrivial` at `Type`, so that
-- theorem's `classical` is essential, not accidental: no rewriting of the proof removes it.
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
-- universal over every carrier would be the sentence shape this file's own § "No count" warns about.
-- The two `#check`ed declarations are what is established; the reach is not.
#check @ZeroParadox.fixedPointFree_of_nontrivial_decidable

end ChoiceCannotBeIndex
