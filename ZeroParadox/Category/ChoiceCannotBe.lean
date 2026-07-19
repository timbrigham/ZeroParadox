import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.SnapNucleus
import ZeroParadox.Category.DoubleNegationNucleus
import ZeroParadox.Category.ExcludedMiddleBridge
import ZeroParadox.Valuation.PoleChartSelection
import ZeroParadox.Ordinal.SyntacticCollapse
import ZeroParadox.Computability.RootCutTrichotomy
import ZeroParadox.Computability.ChoicePurityInvariant
import ZeroParadox.Settheory.Wall

/-!
# Machine-checked characterization index of the framework's relationship to `Classical.choice`

The fourth index alongside `ZeroParadox/BottomCannotBe.lean`,
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` and `ZeroParadox/Order/SnapCannotBe.lean`. A `#check`-only
index: it states no new results and reproduces no logic. Every line `#check`s an already-proven
declaration in its home file, and the `import`s force those files to compile, so the index cannot point
at a dead or renamed result. A `#check`-only index creates no declarations and therefore *structurally
cannot overclaim*.

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
framework's standing temptation. They are separated by a one-directional implication:

> **Diaconescu (1975)** (independently Goodman–Myhill 1978): the axiom of choice implies excluded
> middle. **One direction only** — the converse fails.

So choice is strictly stronger than excluded middle, which is in turn strictly stronger than the
constructive base. Every evocative reading in the framework's prose — "choice is which way you view the
self-dual split", "reading the pole as the floor is an act of choice" — is a **model** of the
choice-versus-no-choice distinction, never the axiom itself. Where such a reading has been made precise
(`Valuation/PoleChartSelection.lean`), the honest result was that the built object **refutes** the naive
form: selection there is free, and the non-constructivity in the conditional model is *inserted by
stipulation* at `poleAdmissible`, not discovered in the pole. Two files carry a written correction of
record on exactly this error — `Category/DoubleNegationNucleus.lean` (once titled "choice as a
difference-generator"; it is the *excluded-middle* modality) and `Category/ExcludedMiddleBridge.lean`
(once stated unscoped, as though excluded middle made every Heyting algebra Boolean).

### The census, stated correctly

A live full build reports **882** `#print axioms` results across roughly **150** files. Of those:

* **658** carry `Classical.choice`;
* **135** are fully axiom-free (no `propext`, no `Quot.sound`, no choice);
* the remainder carry `propext` and/or `Quot.sound` without choice.

A prior internal note recorded "22 of ~1266 (~1.7%)" choice-carrying. That figure was **wrong by roughly
29×** and is corrected here so the error cannot recur. The framework is not choice-free; it is
majority-choice-carrying by proof footprint.

**Reproduce the census yourself — do not take these numbers on trust.** That is the whole point: the
figure being corrected here was wrong precisely because it was quoted rather than measured. Every
`ZeroParadox` file carries a `PurityCheck` section, so a full build emits one `#print axioms` line per
indexed declaration. From the repository root (PowerShell), as two separate calls:

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```
```
$all = Get-Content build.log | Select-String -Pattern "depends on axioms|does not depend on any axioms"
"total:       $($all.Count)"
"with choice: $(($all | Where-Object { $_ -match 'Classical.choice' }).Count)"
"axiom-free:  $(($all | Where-Object { $_ -match 'does not depend' }).Count)"
```

The counts are of emitted *reports*, so a declaration `#check`ed in more than one file is counted once
per report; that is why the total exceeds the number of distinct declarations. Re-run it after any
change — a number in a docstring goes stale silently, and this one already did once.

The detailed accidental-versus-essential classification covers only about **22 of the 658 (~3%)**. The
working hypothesis that all footprints are accidental therefore rests on a sample with **~97% of the
corpus unexamined**. It is a hypothesis, not a finding.

### Accidental versus essential

* **ACCIDENTAL** — a choice-free re-proof exists. Detected by *re-proving*, which is the only
  demonstration available: `dneg_inf_distrib` (§ I) is the worked example — Mathlib's route through
  `compl_sup_distrib` reports `Classical.choice`; staying on the meet side drops it to `[propext]`.
  `SyntacticCollapse.lean` records another: a single tactic call was the whole footprint.
* **ESSENTIAL** — the theorem implies excluded middle, or a choice fragment, over an intuitionistic
  base. **No essential case has been found anywhere in the framework.** That is an absence of evidence
  from a partial survey, not a theorem.

Prior art for the distinction and its methods: constructive reverse mathematics (Ishihara;
Diener–Ishihara). Cited, not claimed.

### What this index does NOT do

It does **not** claim the framework is choice-free — it is not, on 658 counts. It does **not** claim any
footprint is provably removable beyond the specific cases actually re-proved. And it cannot: `#print
axioms` reports **a proof's** footprint, never **a theorem's** necessity. A choice-carrying proof is
evidence about how the proof was written, and nothing more.
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

-- The metric-collapse content on the syntactic side: `[propext]`. (Contrast the measured
-- `[propext, Classical.choice, Quot.sound]` on the ℚ₂-carrier statement `tower_converges_to_zero` —
-- same content, different phrasing, and the choice is the carrier's, not the collapse's.)
#check @ZeroParadox.synCollapse_epsN
#check @ZeroParadox.synVal_mono

-- The ν-side inhabitation witnesses at the root cut: NO axioms. These matter because they REFUTE the
-- general form of "choice enters precisely where the diagonal fixed point is asserted inhabited."
-- Inhabiting a non-well-founded (greatest) fixed point can be entirely choice-free. FENCE: the
-- refutation is functor-specific, not universal — the QPF `Cofix` route in `ChoicePurityInvariant.lean`
-- (`cofix_nonempty'`) DOES carry `Classical.choice`, as a Mathlib M-type artifact. So: the general claim
-- is false; the per-functor question stays open case by case.
#check @ZeroParadox.strict_cofix_nonempty
#check @ZeroParadox.mixed_cofix_nonempty

-- The μ side of the same fork, emptiness witnessed by the bare inductive `WType` eliminator: NO axioms,
-- strictly tighter than the earlier `fix_isEmpty` (`[propext, Quot.sound]`).
#check @ZeroParadox.fix_isEmpty_constructive

/-! ## § II. What choice is NOT to be confused with — the excluded-middle boundary

The modality of §I generates classical LOGIC. That is excluded middle, and it is strictly weaker than
choice. This section indexes the boundary and its scope fence. -/

-- What the modality's closed points actually are: the regular elements `aᶜᶜ = a` — the Boolean core.
-- That is the whole of "generates classical logic", and it is NOT choice.
#check @ZeroParadox.dnegNucleus_isClosed_iff

-- Excluded middle ⟺ every `Prop` is a closed point of the nucleus. Scoped to `Prop`; see the fence below.
#check @ZeroParadox.em_iff_dnegNucleus_trivial

-- DIACONESCU, hypothesis form: a choice fragment implies excluded middle. ONE DIRECTION — the converse
-- fails, which is exactly why choice and excluded middle are not interchangeable. PRIOR ART, not a
-- framework result: Diaconescu (1975), "Axiom of choice and complementation"; independently
-- Goodman–Myhill (1978), "Choice implies excluded middle". The framework contributes only the
-- hypothesis-form packaging (Lean's kernel realizes the arrow as a derivation, not a reusable theorem).
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
-- reading as "the framework is choice-free" — it is not (658 counts). This is the ν-side inhabitation
-- via Mathlib's QPF `Cofix`, measured `[propext, Classical.choice, Quot.sound]`. Its home file argues
-- the footprint is a library artifact of the M-type construction rather than a necessity, citing
-- Ahrens-Capriotti-Spadotti and Veltri (FSCD 2021) that polynomial final coalgebras are choice-free in
-- principle. Contrast `strict_cofix_nonempty` (§ I, NO axioms): same phenomenon, different construction,
-- opposite footprint. That contrast is the accidental/essential distinction in one pair.
#check @ZeroParadox.cofix_nonempty'

-- THE TWO MODALITIES, side by side — the comparison a reader arrives wanting. `snapNucleus` (⊥ ↦ ε₀)
-- inherits `Classical.choice` from Mathlib's `Ordinal` fixed-point machinery; `dnegNucleus` (§ I) is
-- `[propext]`. Both are difference-generators seeded at ⊥ — negation is DEFINED as `a ⇨ ⊥`, and
-- `HeytingAlgebra` extends `OrderBot`, so ⊥ is required before negation exists at all. Same seed,
-- opposite footprints, and opposite behaviour AT the seed: `dnegNucleus` fixes ⊥ (⊥ is always regular),
-- `snapNucleus` provably moves it (`snapNucleus_bot_ne_bot`). The footprint difference is
-- representational — ZP-N re-proves the ordinal ascent choice-free on `ONote` — not intrinsic.
#check @ZeroParadox.snapNucleus
#check @ZeroParadox.snapNucleus_bot_ne_bot

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
-- Every `Prop`-scoped statement in `ExcludedMiddleBridge.lean` pins `@… Prop Prop.instHeytingAlgebra`
-- explicitly for this reason. Pin the instance, or measure nothing.
#check @Prop.instHeytingAlgebra
#check @Prop.instBooleanAlgebra

end ChoiceCannotBeIndex
