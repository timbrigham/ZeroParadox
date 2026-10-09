# Choice and the framework: the long form of the choice index

Long form of `ZeroParadox/Category/ChoiceCannotBe.lean`. Every § number below (§ I to § IV) refers
to that file.

## Formal Overview (AI-assisted)

**How this index differs from the other `*CannotBe` indexes.** Those index the framework's OWN objects
and faces — the bottom role ⊥, the snap, ε₀, computation. `Classical.choice` is **not** a framework object. It is an ambient
axiom of Lean's kernel, present whether or not this project exists. So `ChoiceCannotBe.lean` indexes something
different: **the framework's relationship to choice** — where choice is provably not needed, what choice
must not be confused with, and what is actually established about it here. Nothing below should be read
as the framework claiming choice as one of its constructions, or as a claim about choice in general.

### The headline fence — read this before anything else

`Statement:` CARRIER. On every one-point compactification `OnePoint X` of an inhabited `X`, given a
point `x₀ : X`, a selector constant on the pole orbit of `x₀` exists with no axioms
(`chart_selection_is_freeG`, which takes `x₀` as an argument, so empty `X` is not covered); at the stipulated undetermined pole a
uniform selector is, by definition, the choice fragment (`uniformChartSelection_iff_choiceFragment`).

The ordinary English word "choice" — an act of picking, adopting a point of view, selecting a chart —
and the Lean axiom `Classical.choice` are **not the same thing**, and conflating them is this
framework's standing temptation. The literature that separates them:

> **Diaconescu (1975)**: in a topos, the axiom of choice implies excluded middle. **Goodman–Myhill
> (1978, p. 461)** give the analogue in intuitionistic set theory. Diaconescu's theorem is stated as an
> **equivalence** — a coequalizer of two nonintersecting monomorphisms has a section *iff* subobjects have complements (p. 176); "AC implies complemented
> subobjects" is the corollary (p. 178). The theorem already concerns a two-point shape, since such a
> coequalizer has fibres of at most two points; Goodman–Myhill state the restriction explicitly, choice
> "for sets B, C of at most two elements". With unique choice into `Bool`, `ChoiceFragment` and excluded
> middle are inter-derivable (the `example` after `em_of_choiceFragment` in
> `ZeroParadox/Category/ExcludedMiddleBridge.lean`).
>
> **Cohen (1963)**, with Fraenkel–Mostowski: *full* AC is strictly stronger than excluded middle. This
> is an independence result about ZF, **not** anything Diaconescu proved — do not attribute it to him.

So *full* choice is strictly stronger than excluded middle, which is in turn strictly stronger than the
constructive base. **The restricted fragment is a different matter, and the distinction matters here.**
`ZeroParadox/Category/ExcludedMiddleBridge.lean`'s `ChoiceFragment` is a choice principle into the two-element `Bool` — a
chooser on every inhabited predicate on `Bool` — so in a topos, which always has unique choice, it is *equivalent* to excluded middle (the standard
Diaconescu–Goodman–Myhill theorem); in Lean the equivalence holds with unique choice into `Bool` as a
hypothesis (the `example` after `em_of_choiceFragment`). In Lean, the natural construction of the
fragment from excluded middle fails to elaborate, dying at `Decidable (S true)`, and closes only under
`classical`. **That failure measures that construction, not the fragment** — a failed elaboration is not
a negative result, and a formal independence claim would
need a metatheoretic argument outside Lean (the home file
`ZeroParadox/Category/ExcludedMiddleBridge.lean` states this limit explicitly). `Reading:` a candidate
explanation of the apparent gap between that equivalence and that failed construction is
**Lean's `Prop`/`Type` stratification**, not anything in Diaconescu's theorem. The fragment's chooser
returns data, a `Bool` (`ChoiceFragment`), while `ExcludedMiddle` is `Prop`-valued, and Lean's
stratification does not let `Or` in `Prop` eliminate into `Bool`. A topos also distinguishes its
truth-value object from 1 + 1 (they coincide exactly when it is Boolean); there unique choice holds, so
a decided proposition determines an element of 1 + 1, and without unique choice the equivalence need not carry over to Lean. Whether the fragment is derivable from `ExcludedMiddle` in
Lean is not established here, so this explanation is a candidate, not a finding; the topos theorem is
Diaconescu's. Every evocative reading in the framework's prose — "choice is which way you view the
self-dual split", "reading the pole as the floor is an act of choice" — is a **model** of the
choice-versus-no-choice distinction, never the axiom itself. Where such a reading has been made precise
(`ZeroParadox/Valuation/PoleChartSelection.lean`), the honest result was that the built object **refutes** the naive
form: selection there is free, and the non-constructivity in the conditional model is *inserted by
stipulation* at `poleAdmissible`, not discovered in the pole. The same distinction is drawn in
`ZeroParadox/Category/DoubleNegationNucleus.lean` (the double-negation nucleus is the *excluded-middle*
modality, not choice) and `ZeroParadox/Category/ExcludedMiddleBridge.lean` (excluded middle does not make
every Heyting algebra Boolean; the scope is `Prop`).

### No count is recorded here, deliberately

**`ChoiceCannotBe.lean` and this long form state no figure for how many declarations carry `Classical.choice`, and none should be added
to it.** Three reasons, in order of importance.

**A count mostly measures Mathlib, not this framework.** Most choice footprints traced so far come from a
Mathlib construction — the `Ordinal` order instance and operations (`Ordinal.instLinearOrder`, `nfp`,
`omega0`, `epsilon`; the `Ordinal` type itself measures `[propext, Quot.sound]`), `NONote.repr`, the recursion-theorem proof,
`compl_sup_distrib`, arbitrary-type decidability, a `ℚ` division-ring instance, in one case a single
tactic call. **Not all: `ZeroParadox/Category/Lawvere.lean`'s bare `classical` in
`fixedPointFree_of_nontrivial` is the framework's own, and § IV classifies it ESSENTIAL, on the
premise stated there** — the cost is in stating the swap over types **whose equality is not decidable** (the swap is `if x = b₀ then b₁ else b₀`;
decidable equality is exactly what the § IV escape restores), which is the framework's chosen
generality, not Mathlib's. So a corpus-wide
total still mixes the two sources and still reads as a property of this project, which is reason enough
not to record one; but it is not true that the framework contributes none.

**It invites precisely the wrong conclusion.** A large choice-carrying fraction reads as "most of this
framework is non-constructive." The load-bearing fact is the opposite and much narrower: **T-SNAP, the
core, is axiom-free** (`t_snap_derived` — no axioms at all, not even `propext`). Beyond it the picture
is mixed and the categories are what matter, not a total: some footprints are *accidental* (a choice-free
re-proof exists — the entries labelled ACCIDENTAL in § I), two are **ESSENTIAL** on § IV's premise
(§ IV), some are **STATEMENT-CARRIED** (the statement itself carries choice), and others are
**UNCLASSIFIED**, meaning nobody has tried. A count collapses those four into one number and loses the
only distinction that carries information.

**And in practice the number will not stay right.** A figure is true of the build it was measured on and
goes stale as further files land; citing one that is not regenerated at the moment of use is the error,
and a docstring cannot regenerate anything.

What is true, and is what this long form asserts instead (the members are labelled in
`ZeroParadox/Category/ChoiceCannotBe.lean`): **the framework is not choice-free; the core is
(`t_snap_derived`, no axioms at all); examined footprints fall into four classes — accidental,
essential, statement-carried, unclassified — and § I's ACCIDENTAL entries and § IV name cases in the
first two, § I and § III in the third.** No fraction is given, for the reason stated above.

**A universal negative is the most dangerous sentence shape in a `CannotBe` index:**
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
traced to a source and classified; much of the corpus is unexamined. **Not every footprint is
accidental** — § IV exhibits two reductions to taboos, which make two footprints essential on the
premise stated there. What survives is narrower and is a statement about method, not about the corpus: *where a footprint
has been examined, it has been **assigned** a class* — accidental, essential, statement-carried, or
unclassified. (Not
"classifiable": with `unclassified` among the buckets, classifiability holds of everything and says
nothing.) Do not
upgrade that, and — for the same reason no count is recorded above — **do not quantify the examined
fraction either**; it moves with every commit.

### Accidental versus essential

* **ACCIDENTAL** — a choice-free re-proof exists. Detected by *re-proving*, which is the only
  demonstration available: `dneg_inf_distrib` (§ I) is the worked example — Mathlib's route through
  `compl_sup_distrib` reports `Classical.choice`; staying on the meet side drops it to `[propext]`.
  `ZeroParadox/Ordinal/SyntacticCollapse.md` records another: a single tactic call was the whole footprint.
* **ESSENTIAL** — the PRINCIPLE (the theorem's statement, not one proof of it) implies a constructive
  taboo by a choice-free reduction, and so has no choice-free proof GIVEN that the taboo is not derivable
  without choice. A taboo here is a principle not provable over an intuitionistic base: excluded middle;
  a choice fragment, which implies it (`em_of_choiceFragment`); or a strictly weaker one such as weak
  excluded middle, which excluded middle implies (`wem_of_excludedMiddle`) and which does not imply
  excluded middle intuitionistically (Jankov 1968, "The calculus of the weak law of excluded middle",
  Math. USSR-Izv. 2(5) 997-1004; checked through a secondary source, not read). Lean's choice-free
  fragment is not plain intuitionistic logic, so the § IV premise is what carries that non-provability
  over to it. Reaching a weaker taboo is a weaker implication and needs a stronger premise. **Two are
  located, and the premise is stated, in § IV.** Detected by *reducing* — deriving a taboo from the
  principle — which is the mirror image of the accidental test: accidental is shown by re-proving
  without choice, essential by showing that re-proving without choice would prove a taboo. Note this is
  a statement about the PRINCIPLE, not about any one proof of it: `#print axioms` on a proof reports that
  proof's footprint and can never witness the principle's necessity, which is exactly why the essential
  side needs a reduction instead of a measurement.
* **STATEMENT-CARRIED** — the statement's own type carries `Classical.choice`: a theorem that only assumes the statement and proves `True` already reports it (the statement control). No proof can remove it, so neither ACCIDENTAL nor ESSENTIAL can be asked of it. What can be asked is whether a restatement, on a carrier whose statements are choice-free, holds without choice. Detected by the statement control; members are listed in § I/§ III where measured.

"The statement" in STATEMENT-CARRIED is the term as written, which is what the statement control
measures; a definitionally equal respelling whose own statement is choice-free is a restatement in
the bin's sense (example: `le_total` on `Ordinal.{0}` versus its respelling over the bare `le`
relation, `ZeroParadox/Ordinal/OrdinalChoiceEssential.md`).

The same split between a statement's and a proof's reach of `Classical.choice` is drawn across Mathlib
by V. Gonzalez, "Where Formal Libraries Spend Their Axioms", Zenodo 2026, doi:10.5281/zenodo.21769846
(page numbers from v1.0.3, doi:10.5281/zenodo.21866855), § 4 (p. 8) and § 8 (p. 14): a theorem whose
statement mentions something choice-dependent "cannot be made choice-free however it is proved".
Cited, not claimed.

Prior art for the distinction and its methods: constructive reverse mathematics, which classifies
theorems ("to classify [over intuitionistic logic] various theorems … by logical principles") and whose
taboo direction (a theorem
implying a constructively dubious principle) is the essential test above. Overview read: Hannes Diener,
*Constructive Reverse Mathematics*, arXiv:1804.05495v3 (2020), pp. 4-6, which quotes that aim from
Hajime Ishihara, *Reverse mathematics in Bishop's constructive mathematics*, Philosophia Scientiæ
CS 6 (2006) 43-59 (named; not retrieved). Joint chapter: Hannes Diener and Hajime Ishihara,
*Bishop-Style Constructive Reverse Mathematics*, in *Handbook of Computability and Complexity in
Analysis*, Theory and Applications of Computability (Springer, 2021) 347-365,
doi:10.1007/978-3-030-59234-9_10 (bibliographic record checked at Crossref 2026-10-04; text not
retrieved).
Cited, not claimed.

### What this index does NOT do

It does **not** claim the framework is choice-free — it is not. It does **not** claim any
footprint is provably removable beyond the specific cases actually re-proved. **On the negative side,
for the necessity of a PRINCIPLE, it claims exactly two reductions to taboos — non-removability results
given § IV's premise — and neither comes from a measurement** — § IV's cases are **reductions**, and
for a principle that is the only route available: `#print axioms` on a proof reports **that proof's**
footprint, never **the principle's** necessity. A choice-carrying proof is evidence about how the proof
was written, and nothing more; to show a principle *needs* choice you must derive a taboo from it.
STATEMENT-CARRIED is a different question, decided by measuring the statement (the statement control),
not any proof of it.
