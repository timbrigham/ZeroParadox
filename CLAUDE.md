# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

**Gate exemption — this file and operational meta.** `CLAUDE.md` itself (and other internal operating-instruction / meta files, as opposed to the mathematical publication content) is **exempt from the Editorial Review Gate and the Adversary Review Gate** below. The review gates are scoped to externally-facing publication prose — formal documents, companions, README.md/GUIDE.md, build-script prose. `CLAUDE.md` is the operating manual, not publication content, so it needs **version control only**: commit and push normally, and use `git push --no-verify` if the pre-push hook blocks on a stale review signal for a `CLAUDE.md`-only change.

## Core Objects — Read the Lean First (Hard Rule)

The framework has three core objects, each pinned by an authoritative Lean characterization. **Before writing ANY prose, figure, docstring, companion text, or claim about ⊥ (the bottom), the snap (⊥ → ε₀), or ε₀ — first READ that object's Lean source and ground every statement in a named theorem there.** Do NOT reconstruct these objects from working memory, from prose notes, or from this summary; the Lean is the ground truth. State the theorem, not a gloss. If this summary and the Lean ever appear to disagree, **the Lean wins — stop and ask Tim.**

**The three objects and their authoritative Lean files:**
- **⊥ (the bottom element)** — `ZeroParadox/BottomCannotBe.lean` (the `#check`-only "what ⊥ is / is not" index) + reader map `BOTTOMELEMENT.md`.
- **The snap (⊥ → ε₀)** — `ZeroParadox/Order/SnapCannotBe.lean` (the `#check`-only "what the snap is / is not" index) + home file `ZeroParadox/Order/Snap.lean` (T-SNAP, `t_snap_derived`) + reader map `SNAP.md`.
- **ε₀** — `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` (the `#check`-only "what ε₀ is / is not" index) + `Epsilon0LeastFP.lean` / `Epsilon0MinMax.lean`.

The `CannotBe` indexes are `#check`-only — they create no declarations, so a line cannot point at a dead or renamed result; reading one shows what the object IS and IS NOT, each line a live theorem.

**⚠ The `#check` lines cannot overclaim. The `--` glosses beside them absolutely can, and have.** This file used to say the indexes "structurally cannot overclaim" full stop; that is true of the *declarations* and **false of the comments**, which are ordinary unverified prose sitting in a file whose stated premise is that it cannot overclaim. Measured 2026-07-26: two glosses in `DiagonalFixedPoint.lean` (`-- the Kleene quine IS ⊥`, a flat cross-type identity on a theorem stating `IsQuineAtom q → q = bot`) survived **four** adversary rounds inside that blind spot, and three more were found in `SnapCannotBe.lean`.

**The standing convention (Tim, 2026-07-26) — every gloss carries one of two labels, and there is no third option:**
- **`Statement:`** — an accurate restatement of what the declaration actually proves. Best form is an
  elaborating `example` (a wrong gloss then fails to compile); prose is acceptable where an `example`
  would be unwieldy, but it must be checkable by reading the statement.
- **`Reading:`** — the framework's interpretation, explicitly NOT a claim about what the theorem says.

This is as much for a human reader as for a checker: the label tells you at a glance whether you are looking at mathematics or at interpretation. **The rule generalizes beyond the indexes** — the same defect class (prose asserting conjuncts the cited statement lacks) was found this session in ordinary docstrings, in `CLAIMS.md` rows, and in this file itself.

**Why the labels, and not another sweep.** Grepping for a claim's vocabulary cannot terminate — there is always another claim, and a sweep that greps `da1_closed_concrete` misses the site that says `da1_paths_unified`. Checking **witnesses against statements** is finite: bounded by the number of citations. `ZeroParadox/ClaimsMirror.lean` already proves the principle works — `claim_DA1` states the honest content precisely because it had to elaborate.

**The keystone index (the phenomenon the three objects share):** `ZeroParadox/DiagonalFixedPoint.lean` — the `#check`-only index routing every formalized face of **self-reference** (the diagonal fixed point) by the μ/ν fork: wall faces where self-reference cannot close (no fixed point — Cantor, Russell, Turing, Tarski, Curry) and floor faces where it closes and lands at ⊥ (the Quine atom, the Kleene quine, Löb/Gödel-2, Rice), all off Lawvere's engine. It is the direct route to self-reference the three object indexes point back toward. It states no new claim: the cross-face unification is Lawvere (1969) / Yanofsky (2003), cited prior art, and the cross-face identity across domains stays a **type boundary**, never a Lean `=`.

**The μ/ν fork and the HOST VERDICT — read before writing about the "one root or two" question, about
well-foundedness as a "second root," or about how many faces self-reference has. It is ALREADY BUILT — do
not build it again.** Authoritative sites, all pre-existing: `ZeroParadox/Settheory/LawvereBridge.lean` § V
("the whole μ/ν picture … one engine, two regimes, discriminated by the self-loop"), whose
`mu_nu_branch_exclusion` (`:124`) and `selfApp_lands_on_nu` (`:133`) are the theorems;
`ZeroParadox/Settheory/QuineHost.lean`, whose class is named for the host and already sorts three theories
by whether they permit the self-loop; `ZeroParadox/DiagonalFixedPoint.lean` § II/§ III, whose spine is the
wall/floor (μ/ν) carving; and `Settheory/Wall.lean`'s reframe paragraph.

The engine (`negation_no_fixedpoint` → `lawvere_fixedpoint`) forks: **μ** — the map is fixed-point-free, no
object forms; **ν** — a fixed point exists. The well-founded family then renders a **verdict on ν**: a
well-founded host refuses it (`no_quine_atom`), a host carrying it is thereby not well-founded
(`quineHost_not_wellFounded`, `floor_not_wellFounded`). Same theorem (`wf_no_selfloop`), two hosts — so
well-foundedness is **not a third root of self-reference; it is the axis of the host's verdict**.

**Use the STANDARD NAMES — all four are published and all four sources are in `.claude-local/papers/`:**
- the ν direction is **"the Diagonal Theorem"** (Lawvere & Schanuel, via Yanofsky 2003 p. 5 Remark 3,
  p. 14 Thm 3 — Yanofsky was already cited in `Wall.lean`; the names were not);
- a host permitting ν is **"degenerate"** (Yanofsky p. 3; nLab, *Lawvere's fixed point theorem*);
- in set theory the permit/refuse split **is** Foundation vs Anti-Foundation (Aczel 1988 **p. 6**);
- the general form is a **published theorem** — Adámek-Milius-Moss 2020 **Thm 7.6** p. 30, *"the only
  well-founded fixed point is the initial algebra"* — with the axis named the **well-founded part /
  coreflection into well-founded coalgebras** (their Def 5.1 p. 22, credited to Taylor). The corpus proves
  the **one-relation shadow** of Thm 7.6, never the coalgebraic theorem.

**Three fences.** (1) The narrow one-root question is still **NO** — `wf_no_selfloop` is proved by
accessibility, not by the engine; `selfloop_permitted` / `engine_is_wf_free` stand. (2) Scope: the
ν-refusal reading covers the **well-founded family only** — the ε₀ row (`ZPN.omegaPow_no_fixedpoint`) is
ordinal arithmetic, not a self-loop instance. (3) **No traversal** — nothing here says the object moves;
that stays the commitment (`l_inf`'s docstring).

**⚠ Prefer the STRONGER library forms; this family has been re-proving the weakest rung.**
`WellFounded.asymmetric` (`Mathlib/Order/RelClasses.lean:225`) beats `wf_no_selfloop` (forbids 2-cycles
between distinct points; `asymmetric₃` for 3-cycles); Mathlib's `WellFounded.irrefl` is **class-valued**
(`Std.Irrefl`, a class with a *field* — it does NOT "unfold to `¬ r x x`") with instances registered, so
`irrefl_of`/`asymm_of` fire free and `ZFSet` already carries the instance; and
**`wellFounded_iff_isEmpty_descending_chain`** (`Order/WellFounded.lean:51`) is a **biconditional** that
renders the ν-hosted side as *"the host contains an infinite ℕ-indexed descent"* — **the INFINITE pole the
Two-Pole rule demands, which the `r x x` form hides.**

**⚠ THAT ADOPTION IS DONE — do not build it again.** It landed 2026-07-29 (`27b1911`) at
`ZeroParadox/Multihomed/Boundary.lean` § I-b: `floor_descent_from_bot`, `bot_not_acc`,
`floor_not_wellFounded_via_descent`. `ZeroParadox/Settheory/Wall.lean:74-75` already says "Now adopted."
**This line said "Adopting it is open work worth doing" until 2026-07-30 — while § "unstated adjacency"
BELOW, in this same file, already listed the descending-chain form among the CLOSED finds. One file,
two contradictory answers, 186 lines apart.** That is the exact trap that produced the `HostVerdict.lean`
Trigger-0 revert, and it was live in the manual meant to prevent it. Sweep this file too when a find closes.
- **Purity, measured not inferred:** citing the biconditional at all costs `Classical.choice` (its `mp`
  builds the chain with `.choose_spec`, and `#print axioms` follows the STATEMENT). So
  `floor_not_wellFounded_via_descent` carries `[propext, Classical.choice, Quot.sound]` while § I's
  `floor_not_wellFounded` stays axiom-free and remains load-bearing. `bot_not_acc` is axiom-free **only
  because it is proved by hand**; the one-line `not_acc_iff_exists_descending_chain.mpr` route measured
  choice. Same verdict as the `CovBy` precedent: keep the hand proof, cite the standard name.
- **Fence:** the witness is `fun _ => bot`, the **degenerate** (constant) descent. A genuine non-constant
  descent is strictly more and does **not** follow from a self-loop — still open.
- Correct neighbour names in the pin: `not_acc_iff_exists_descending_chain` (`:34`) and
  `RelEmbedding.wellFounded_iff_isEmpty` (`Order/OrderIsoNat.lean:71`). There is no
  `not_acc_iff` and no `RelEmbedding.wellFounded_iff_no_descending_seq`.

**Why this section exists (2026-07-29) — a measured Trigger-0 failure, and the most expensive one yet.**
A file `Settheory/HostVerdict.lean` was written to "consolidate" this carving **before any prior-art
search**. Its `nu_hosted_forces_non_wf` was **character-for-character** `mu_nu_branch_exclusion`, same proof
body; its `nu_hosted_face` was `selfApp_lands_on_nu`. The contraposition already existed **eight times
across six files**, the carving **three times**, and the standard names sat in a paper the file's own base
already cited. It was **reverted in full** (`7b997fa`, `4a56da4`). Step 1 of the three-step check —
`grep -rn "¬ WellFounded" ZeroParadox` — would have prevented the entire build. **The failure was ORDERING,
not effort:** the expensive corpus grep was done (it is what made the file possible) and the two cheap steps
were skipped, which is the worst split, because doing the expensive half *feels* like diligence. Full
findings: `.claude-local/notes/prior_art_hostverdict_2026-07-29.md`; the reframe itself (Tim's) is
`.claude-local/notes/wall_one_root_or_two_trinary_2026-07-29.md`.

**The choice index (NOT a fourth core object — read it before writing about choice or constructivity):** `ZeroParadox/Category/ChoiceCannotBe.lean` — the `#check`-only index of the framework's **relationship to `Classical.choice`**. `Classical.choice` is an ambient kernel axiom, **not** a framework object, so this index is scoped differently from the three above: where choice is provably not needed, what it must not be confused with, and what is actually established. **Read it before writing any prose, docstring, note, or outreach copy touching choice, constructivity, purity, axiom footprints, or the "choice = point of view / chart selection" reading.** Three standing traps it exists to stop:
- **The equivocation (hit four separate times on 2026-07-19).** The ordinary English "choice" — an act of picking, a point of view, a chart selection — is **not** the axiom `Classical.choice`. Every evocative "choice = which way you view the split" reading is a **model** of the choice-vs-no-choice distinction, never the axiom. State it as a model or not at all. **Attribution, stated precisely — an earlier version of this bullet had it wrong and seeded the error into five Lean files:** Diaconescu (1975) proves an **EQUIVALENCE** — a coequalizer of two nonintersecting monomorphisms has a section *iff* subobjects have complements (p. 176), the choice direction being his corollary (p. 178); in modern terms, choice for inhabited subobjects of a two-element object **IS** excluded middle. That **full** AC is strictly stronger is **Cohen 1963** / Fraenkel-Mostowski independence, **not** Diaconescu — never attribute strictness or a failing converse to him. That the restricted fragment nonetheless *appears* not to follow from excluded middle in Lean — the natural construction fails to elaborate and closes only under `classical`, which is **strong evidence, never a proof of unprovability** — looks like a fact about **Lean's `Prop`/`Type` stratification** (the fragment selects into `Bool`, making it data-valued excluded middle), which a topos lacks; that reconciliation is the framework's own finding. **Never state the Lean gap as a negative result**: a failed elaboration is not an independence theorem, and claiming one would need a metatheoretic argument outside Lean. Full statement: `ZeroParadox/Category/ChoiceCannotBe.lean`.
- **NO COUNT — measure on demand, never record one.** Do **not** write a figure for how many declarations carry `Classical.choice` into this file, into any `.lean` docstring, or into any note. `ZeroParadox/Category/ChoiceCannotBe.lean` deliberately records none and gives the three reasons: a corpus total mostly measures how classically **Mathlib** is built rather than anything about this framework (**mostly, not entirely — `Category/Lawvere.lean:70`'s bare `classical` is the framework's own and is ESSENTIAL**, so do not write "none of it is ours"); it reads as "most of this is non-constructive" when the load-bearing fact is that **T-SNAP is axiom-free**; and the number has already been wrong three times (once quoted rather than measured, once measured and gone stale inside a single session — this bullet itself carried the stale one). That index supplies the PowerShell to measure on demand. **The framework is not choice-free; the core is (`t_snap_derived`, no axioms at all); most examined footprints proved removable; and TWO ARE PROVABLY NOT** (§ IV of the choice index). **Date the claim** — see the lesson below.
  - **⚠ CORRECTED 2026-08-01. This line previously read "every examined footprint has been removable — that statement does not go stale, and it is the one to use." BOTH HALVES WERE FALSE**, and the second half is what made the first durable. The two **essential** cases were committed 2026-07-20, one day after the choice index was last touched: `em_of_wellOrder_comparable` (`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` — comparability of well-orders implies excluded middle; prior art Kraus-Nordvall Forsberg-Xu arXiv:2104.02549 **Thm 38(d)**, there in the data form) and `wem_of_fixedPointFree` (`ZeroParadox/Category/LawvereTaboo.lean` — the general fixed-point-free principle implies **weak** excluded middle, and this one sits on the **keystone**, not on an imported order instance). Both are **taboo reductions**, not failed elaborations, so they clear this file's own bar for a negative result. **Fixed in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV.**
  - **State the shape correctly or not at all.** Each theorem is itself a **choice-free reduction**: the classical content is entirely in the **hypothesis**. What is established is about the **PRINCIPLE** — re-proving it constructively would decide a taboo, so no choice-free re-proof exists — **not** about any particular proof, and **not** an independence result. `#print axioms` reports a proof's footprint and can never witness necessity; that is precisely why the essential side needs a **reduction** where the accidental side needs a **measurement**.
  - **The defect was bigger than this line and was fixed AS A CLASS (closed 2026-08-01).** `ZeroParadox/Category/ChoiceCannotBe.lean` — the index this file *mandates reading* before any prose about choice — had asserted at `:91` *"No essential case has ever been found"* and at `:142` *"**No essential case has been found anywhere in the framework**"* while referencing **neither** theorem (`#check` count: 0). Meanwhile `RELEASES.md:425`, the **published** record, already advertised that index as containing "the two essential cases". The index was written honest and went false **one day later**. **Now closed:** both universal negatives are gone from the corpus (grep the claim: 0 hits) and both witnesses are `#check`ed in § IV. **Residual debt, not yet swept:** several dated notes still repeat the claim — `notes/choice_essential_vs_accidental_2026-07-18.md:31,122,134` and `notes/future-research/roots_enumeration_category_2026-07-20.md:295`. Dated records are deliberately not rewritten (they cite the tree as it stood), so **verify at the artifact, never from a note** — which is this file's standing rule anyway.
  - **The lesson, which is this file's own warning arriving at full scale:** the `#check` lines cannot overclaim; the **prose** can, and here the overclaim is not a gloss on one theorem but a **global negative** ("nowhere in the framework") in an index whose stated premise is that it cannot overclaim. **A universal negative in a `CannotBe` index is the most dangerous sentence shape in this corpus — it is falsified by any single future commit and nothing mechanical notices.** Prefer "none located as of &lt;commit&gt;" over "none exists".
- **The instance hazard.** Choice often enters at the **instance** level, invisible in the lemma: `Prop.instBooleanAlgebra` carries `Classical.choice` while `Prop.instHeytingAlgebra` is `[propext]`. A `Prop`-scoped statement that does not PIN its instance silently acquires choice and every purity claim about it becomes vacuous. Measure the instance and the tactic, not just the lemma.

**The computation index (NOT a core object — read it before writing about the computational face):** `ZeroParadox/Computability/Kleene.lean`, specifically **§ II** (the `KleeneStructure` class), **§ III** (T-COMP and its fence), **§ VI** (the quine family), and the **axiom-footprint block** in its header. Also `ZeroParadox/Information/Surprisal.lean`'s `l_inf` docstring, which is the honest statement of where the argument stops. *(A dedicated `#check`-only `ComputationCannotBe` index is drafted at `.claude-local/lean_wip/DRAFT_ComputationCannotBe.lean` and will replace this pointer when it is promoted through the gates.)*

**Read it before writing any prose, docstring, companion text, figure, or outreach copy touching computation, execution, the Kleene quine, DA-1, or "the bottom runs itself."** Six standing traps, every one of them measured on 2026-07-26 and every one of them shipped in the corpus for months:

- **`da1_closed_concrete` proves `IsQuineAtom (bot : MachinePhase)` and NOTHING computational.** No `Code`, no execution. It is named as though it closes DA-1; it closes the structural half. **Never cite it for self-execution.**
- **T-COMP proves THREE characterisations equivalent, not four** (`t_comp` is literally `t_exec_triple_iff`). The computational face enters as the class field `botCode_is_quine` — an assumption, not a clause.
- **`da1_paths_unified` is a CONJUNCTION, not an identity.** "Both hold" is not "these are the same fact," and they cannot be equated: one is about an element of `L`, the other about a `Code`.
- **The quine family is witnessed by CONSTANT codes** (`hconst_quine`, inside `infinite_quine_family`). `IsComputationalQuine` is a *periodicity* condition, strictly weaker than self-reference — a constant satisfies it vacuously. So the family is broad, and it is **not** a padding orbit (padding gives many indices for the *same* function).
- **The set-theoretic bottom is UNIQUE; the computational fixed points are an INFINITE indexed family.** A point and a family are different shapes. No fix to the predicate changes that.
- **`#print axioms` follows the STATEMENT, not the proof.** `[KleeneStructure L]` in a statement reaches Mathlib's `eval` and puts `Classical.choice` in the footprint even when the hypothesis is inert in the proof. **Inert-in-the-proof and absent-from-the-footprint are different properties — never infer either from the other.** This figure has been wrong four times, always because it was quoted rather than measured. **Measure it.**

**The honest line, which `l_inf`'s own docstring already states:** L-INF supplies the formal premise (surprisal at ⊥ is unbounded); the step from that to *forced execution* is an ontological bridge, a named design principle, **not** a mathematical consequence. The framework commits that the snap fires; it does not prove it.

**The claims mirror (the claim graph made checkable — read/update it whenever a claim's STATUS is asserted or changed):** `ZeroParadox/ClaimsMirror.lean` — the machine-checked representation of the SSOT `claims` store. Each claim node the store marks `proved` / `corr` / `deep` is **restated exactly and discharged from the existing machinery**, so a claim's status is a **verified link to a green declaration, not a label**; the purity block prints each claim's honest axiom footprint (three faces axiom-free — `node-order`, `node-set-theory`, `T-SNAP`; the p-adic floor `[propext]`; the rest carry Mathlib choice). The three non-theorems are represented by their **deliberate absence**: the two `Lawvere-*` conjectures (one Set face provably *not* a Lawvere instance) and the retired `MC-1-identity` (ill-typed — `x = y` across distinct categories is not a well-formed proposition) carry **no theorem**, and that non-representation is itself the checked fact. **Why it exists (2026-07-21):** a `proved` label is only as good as the decl under it, and a false premise attached to a *true* conclusion is invisible from the outside — nothing downstream breaks, so being right about the conclusion hides a wrong reason (the ZP-A / ZP-E Foundation-squeeze false premise survived to high revision exactly this way). The mirror is the mechanical guard: the kernel re-derives each claim indifferent to how it was reached, so a status that is not actually backed shows up as a decl that will not elaborate. **The rule:** before asserting a claim is proved (in prose, a docstring, a companion, outreach), check it has a green entry here; and whenever a core claim is added, or a claim's status changes, update `ClaimsMirror.lean` and its SSOT `link_claim` in the **same** change — the same reflex as the purity check and the SJV sync.

**Bedrock invariants — machine-checked; never violate, always verify against the theorem (do not assume):**
- **ε₀ ≠ 0. Always. In any reading, carrier, or encoding.** (`epsilon0_ne_zero`.) Never "fence ε₀ = 0" or treat 0 as a candidate value for ε₀ — it is not a well-formed possibility.
- **ε₀ ≠ ⊥.** (`epsilon0_ne_bot`.) ⊥ = 0 is the *base* the ε₀-tower is seeded at; ε₀ is its *closure* — the base is never its own closure.
- **ε₀ is both min AND max at once** — least fixed point ≡ tower supremum (`epsilon0_min_eq_max`); direction-/instance-specific, never collapsed to one face.
- **ε₀ requires two conditions**: the ω-tower operator `α↦ω^α` AND the base ⊥ (`ε₀ = nfp(ω^·)⊥`, `epsilon0_eq_nfp_bot`; Mathlib `ε₀ = deriv(ω^·) 0`). It is the *minimum* step next to the pole (Veblen coords (1,0); the 1/∞ reading), never the pole.
- **⊥ = 0 = ∞ is the pole** — *stated*, not fenced (the framework's own identity). **It is a CHART claim, not a point identity:** the same object reads as the zero pole under one measurement and the infinity pole under another. The two halves have **different witnesses** — **coincidence**: `infinitude_forces_infinite_complexity` (`ZeroParadox/Valuation/InfinitudeFloor.lean`; the floor's complexity *is* `⊤`); **drift**: `pole_inversion` (same file; the members converge to the floor while their complexity ascends to `⊤` — two measures running opposite along **one sequence**); **inversion**: `rInv_swaps` (the antipodal exchange). ⚠ **CORRECTED 2026-08-06 — this line used to name `pole_inversion` as the COINCIDENCE witness, contradicting the KIND table below, which lists it under DRIFT.** The table is right: `pole_inversion`'s conclusion is two `Tendsto` conjuncts and contains no `cx floor = ⊤`. The coincidence on that carrier is a *separate* declaration, named above. (`pole_inversion`'s own docstring also claims the theorem holds "their coincidence" — the **typeclass** does, the **theorem** does not.) **Never cite `rInv_swaps` for the coincidence.** It proves `rInvHomeo (some 0) = ∞ ∧ rInvHomeo ∞ = some 0` — two points *exchanged*, and its own docstring calls this "the 0=∞ antipodality"; in that carrier `some 0` and `∞` are provably distinct, and if they were one point the swap would be trivial. (Corrected 2026-07-26: line had cited `rInv_swaps` for the identity for months. The computability face's version of the coincidence is `selfloop_is_zero_and_infinity` — a self-looping configuration yields nothing (zero pole, output chart) while never halting (infinity pole, step chart).) This is NOT ⊥ = ε₀ (which is false).
- The snap-arc **returns to a bottom, never to ε₀** (`epsilon0_ne_bot`). The framework reads that bottom as a **new** one — a successor null, the next instantiation. What is *proved* is the **role** half: anything playing the bottom role **is** the bottom (`t_iz_limit_is_new_null`, which is one direction of `da2_bottom_characterization` — its statement is `(∀ x, join terminal x = x) → terminal = bot`, with no chain, no limit and no novelty in it). The **novelty is a commitment, not a theorem**: within a single lattice `bot` is unique, so "a different bottom" is not expressible there, and in the 2-adic realization the arc reapproaches the *same* 0 (`snap_arc_z2_loop`). **Never cite `t_iz_limit_is_new_null` as a witness for novelty.** (Corrected 2026-07-26: it had been named here as the novelty witness for months. Found by an adversary gate probing a *second* claim after the ZP-K sweep closed — see the note on the witness-vs-statement defect class.)

**Why this rule exists (2026-07-17):** a run of prose/figure errors — fencing ε₀ = 0, "co-locating ⊥ and ε₀," flattening min≡max to one face, calling ε₀ "a large ordinal / ceiling" — all came from reconstructing these objects from working memory instead of reading the Lean. The fix is mechanical: read the `CannotBe` index first, cite the theorem, never gloss.

## Commitments Go In HYPOTHESES, Data Goes In BRACKETS — Default Method, Hard Rule

**A commitment encoded as a typeclass field reads as data, because brackets are where data lives.
That single fact produced every bedrock defect of 2026-07-26.** State commitments as explicit
hypotheses so the signature cannot be misread.

**The test — CAN IT BE FALSE?**
- **Data** (goes in brackets): the carrier either has it or does not. `[ZPSemilattice L]` — a join with
  laws. Cannot be "wrong"; inference on it is worth keeping.
- **Commitment** (goes in a hypothesis): the framework asserts it and reality might not comply.
  "Nothing external can execute ⊥." "The bottom departs." "States are discrete."

**NEVER BUNDLE ONE INTO THE OTHER.** If a class field asserts something the framework could be wrong
about, extract it as a hypothesis on the theorems that need it. `KleeneStructure` is the worked example
of the failure: it bundles a `Code` (data) with the assertion that the code names ⊥ (commitment), and the
bundling is precisely what let `da1_closed_concrete` read as establishing self-execution for months.
`AbstractSelfApp` has the same shape — which is why `trivialSelfApp` inhabits it, and why "L carries
`AbstractSelfApp`, therefore …" is vacuous.

**The canonical form** (`ZeroParadox/Computability/Occurrence.lean` § VI-b):

```lean
theorem execution_requires_branching (R : σ → σ → Prop) (s : σ)
    (hfix : R s s)                      -- COMMITMENT: the bottom is its own fixed point
    (hdep : ∃ t, R s t ∧ t ≠ s) :       -- COMMITMENT: execution occurs
    ∃ t u, R s t ∧ R s u ∧ t ≠ u        -- CONSEQUENCE, not a further assumption
```

**Why this is the default and not a preference.** It is the only defence found on 2026-07-26 that
**requires nobody to remember anything** — gloss labels need discipline, review rounds need reviewers, a
type signature simply is what it is. It makes the framework's assumption load **countable** (grep the
hypotheses) instead of recoverable only by reading prose. And it would have prevented **both** bedrock
findings that day: `da1_closed_concrete` could not have been cited for self-execution with execution
visible as a hypothesis, and `t_iz_limit_is_new_null` could not have been cited for novelty with novelty
visible as one.

**Three encodings, decreasing honesty — know which you are writing:**
1. **Baked into the carrier** — `ax_b1_distinct : nullState ≠ firstAtomicState := by decide`, where
   discreteness *is* the two-element type. Invisible at every use site. **Worst.**
2. **Hidden in a class** — `[QuineHost L]`, `[KleeneStructure L]`. Visible only if you know what the
   class carries.
3. **Explicit hypothesis.** Visible on the face of the statement. **Prefer this for anything that can be
   false.**

**Rollout — AS-TOUCHED, not a rewrite.** The corpus has ~1400 declarations on the class form and there is
no realistic big-bang migration. Every new or edited commitment uses the hypothesis form immediately;
where an existing class carries a commitment, add a **companion explicit-hypothesis theorem** rather than
refactoring the class. First candidates: `KleeneStructure`'s identification, and **AX-B1**, which is the
framework's one substantive modelling commitment and currently the least visible of the three (encoding 1).

## Point-of-view claims: declare the KIND and the STATUS. Gate-enforced.

**"Point of view" / "chart" / "frame" was doing FIVE different jobs with one word.** The cost, measured
2026-07-30: a full day of gate rounds, two bedrock findings, and a correction that itself over-corrected
into *denying* the framework's own thesis. The sequence is worth keeping because both halves are traps:

1. `snap_is_frameflip` was cited as proving the snap **is** a change of frame. Its statement contains no
   snap. Witness-vs-statement defect.
2. The fix then wrote *"the POLE EXCHANGE (**NOT** of the snap)"* into a dozen sites — which **denies** a
   reading that is well-motivated and is ZP-Q's stated conjecture. Over-correction, and the same class as
   `feedback_triage_review_vs_grounded_figures`: a review pass gutting a grounded claim.

**Neither is possible if every POV claim declares WHICH KIND it is and WHETHER IT IS PROVED.**

**THE FIVE KINDS** — genuinely different phenomena, previously all called "chart":

| KIND | means | example witness |
|---|---|---|
| **COINCIDENCE** | both readings hold of ONE object **simultaneously** | `selfloop_is_zero_and_infinity`; `epsilon0_min_eq_max`; `catseam_is_frameflip` |
| **INVERSION** | a map **exchanges** the readings; always an involution | `rInv_swaps`, `swap_involutive`, `flipPoles_involutive` |
| **DRIFT** | two measures run **opposite** along one sequence | `pole_inversion` (element descends, complexity ascends) |
| **CARRIER** | the claim's **truth value** depends which carrier you are in | snap available in ℚ₂, impossible in ℝ — both completions of ℚ (Ostrowski) |
| **INVARIANT** | the quantity **does not transform**; flipping the chart gains nothing | measure-zero-ness, cardinality |

**THE STATUS — folded into the EXISTING `Statement:` / `Reading:` labels. This adds no new label:**
- **`Statement:` + KIND** — the theorem proves it. Name the witness.
- **`Reading:` + KIND** — the framework reads X as an instance of that kind. Conjectural.

**ONE THEOREM MAY CARRY TWO KINDS — write one `Statement:` line per KIND it actually proves.** A bundle
carrying two is the **normal case for a self-dual object**, not an exception. `catseam_is_frameflip` is the
worked example: (i) and (ii) say the seam is initial AND terminal — **COINCIDENCE** — while (iii) says `op`
exchanges those characterisations and fixes the seam — **INVERSION**. Being both is exactly what makes it
self-dual; either label alone is a mischaracterisation. **Measured 2026-07-30, one commit after this table
was written:** the gloss went in tagged INVERSION only, disagreeing with the COINCIDENCE entry in this very
table, and the prior-art gate caught it. The convention as first drafted implied one KIND per claim, and the
mislabel followed immediately.

**There is deliberately NO slot for denying a reading.** That is what makes trap 2 unwriteable. If a
theorem does not establish an identification, say `Reading:` and mark it conjectural — never "NOT the snap".

**And the DENIAL is checked directly, not inferred from a missing tag.** Measured 2026-07-30: the tag-check
passed at **zero** new untagged claims while **seven** denial sites sat live in the corpus, and the editorial
gate had to find four of them by eye. A denial is wrong regardless of how it is tagged, so `check_pov.py`
carries a `DENIAL` pattern checked **unconditionally and never baselined**. **The generalizable lesson, which
applies to every gate this project writes:** a convention with a *forbidden form* must detect the forbidden
form itself — detecting only the *absence of the required form* leaves the violation invisible.

**Enforcement is MECHANICAL, because this is the FOURTH convention of this shape and the previous three
all leak.** (`vocabulary_reference.md`: the bare-"bottom" rule, "iterative bottoms", standard-math-first.)
`feedback_jargon_blindspot` records why: Claude is embedded in the project's language and structurally
cannot self-detect vocabulary drift, so discipline-level rules fail here by construction.
- `python .claude-local/check_pov.py` — **WARNS**, wired into `.git/hooks/pre-commit` (staged copy at
  `.claude-local/proposed_pre_commit_hook.sh`; hooks are not version-controlled, re-install per clone).
  It never blocks a commit — the stub-first protocol commits incomplete work on purpose, and a blocking
  commit gate with false positives trains the `--no-verify` reflex that would cost the push gate too.
- `python .claude-local/check_pov.py --block` — **BLOCKS**, wired into `pre-push` § 3b. Validated
  2026-07-30 end-to-end: injecting a real POV overclaim made `git push --dry-run` exit 1 on the POV
  check; removing it passed.
- **Baselined.** The corpus already carries **90** untagged sites (measured). Demanding a tag on all of
  them is a migration, not a gate, and a gate that blocks everything on day one gets muted. So
  `.claude-local/pov_baseline.txt` grandfathers them and the gate blocks on **NEW** sites only —
  as-touched rollout, same as the file-path and CC-2 conventions. **Shrink the baseline as files are
  touched; never grow it deliberately.**

**Do not flag the intentional collisions.** `project_notation_notes`: the ⊥ / ε₀ / P₀ overloads are
deliberate. The checker allowlists them, and anything that starts crying wolf must be narrowed, not
tolerated — a muted gate is worse than none.

## A requirements class is only informative if something FAILS to be a member. Gate-enforced.

**Five of seventeen classes in this corpus are degenerate or bundle a commitment as data. That is one
design habit, not five incidents** — writing a class without asking what it EXCLUDES:

| class | verdict |
|---|---|
| `WheelValuationStructure` | constant-`⊤` valuation satisfies every field on any commutative ring → `WVSNondegenerate` added |
| `AbstractSelfApp` | `trivialSelfApp` inhabits it, so *"L carries it, therefore…"* is vacuous |
| `InfinitudeFloor` | characterised 2026-08-07 as **exactly** `Infinite α` — nothing more |
| `SeparatedSuccession` | `Unit` + the always-true relation discharges every field (2026-08-07) |
| `KleeneStructure` | bundles a `Code` (data) with the assertion that it names ⊥ (commitment) |

**⚠ THIS IS NOT A NEW RULE — IT IS TIM'S OWN 2026-06-29 NO-GO GAUGES, FINALLY ENFORCED AND FINALLY
POINTED AT THE RIGHT OBJECT.** `.claude-local/notes/nogo_gauges_2026-06-29.md` already specifies
**gauge 1, the decorative check** (*"delete all framework vocabulary; if nothing specific is lost, the
entry is a label. REJECT"*), **gauge 4, the vacuity check** (*"if every confirmed edge is tier-1
generic, the dictionary is true-but-empty"*), and **discipline (b): NAME the obstruction in advance —
"if you can't say what would break it, you don't understand the claim."** That is *name a non-member*,
written 40 days before this section.

**Why it never fired:** the gauges were scoped to **dictionary transport edges**, nobody pointed them
at **requirements classes**, and they lived in a memory body plus a note rather than here — exactly the
failure this file names in its own words, *memory is for context, not enforcement*. Fifty files carry
NO-GO text, so it was applied wherever someone remembered. Eighteen classes were never asked.

**The check is mechanical and cheap: BUILD THE TRIVIAL WITNESS, or prove you cannot.** Both answers are
worth having — a failed attempt is evidence the class has teeth. Do it **before** citing membership as
meaningful, because a vacuous class makes every downstream *"X carries this, therefore…"* empty.

**⚠ The failure is invisible from inside.** Every one of the five was found by someone building a
witness, never by reading the class. `SeparatedSuccession`'s `separated` field even carries the comment
*"the succession never repeats"* while admitting a **constant** sequence — the comment asserts what the
field does not enforce.

**Enforcement (2026-08-07, Tim's call — mechanical because this is the FIFTH convention of this shape
and the earlier four all leak).** `python .claude-local/check_classes.py` WARNS at commit;
`--block` ENFORCES at push. It cannot decide degeneracy (that needs a witness); it enforces that the
question was **asked** — a `NO-GO` section, a `Nondegenerate` predicate, or a named trivial witness in
the declaring file. Same design as `check_pov.py`: enforce that a convention was followed, never that a
claim is true. **Baselined at 18 grandfathered sites; blocks on NEW classes only.** Shrink the baseline
as files are touched; `SeparatedSuccession` is first to remove (tracked as `SEP-1`).

**Detector verified before use**, per this file's own rule: it fires on `SeparatedSuccession` (the
known-degenerate case, found by hand the same day) and suppresses `InfinitudeFloor`,
`WheelValuationStructure` and `AbstractSelfApp` (where the question was asked). A checker with only a
must-fire control is half-tested.

## Short header, statement per declaration. Prose never exceeds code. Gate-enforced.

**Tim, 2026-08-08, and it is a software-engineering norm, not a preference:**

> *"I'm not a big fan of having just a giant header block full of prose. Usually it's a short
> summary of what the file is supposed to be doing as a whole, no more than a few sentences, and
> only once you actually get into the individual lines, do you have a statement of what that exact
> line is supposed to be doing. Apart from the Engineer's Take, I don't think there should be more
> prose than code as a general rule, counted by line numbers."*

**THE SHAPE:**
1. **File header** — a few sentences on what the file does. **Not** an essay.
2. **Every declaration** — a docstring saying what **that declaration** does, no longer than the
   declaration itself.
3. **Long-form reasoning** — a note in `.claude-local/notes/`, with a pointer. Not the source file.
4. **The Engineer's Take is exempt.** It is Tim's voice and the only corpus written in the register
   a question arrives in — `where.py` reports Takes for exactly that reason.

**WHY IT IS A CORRECTNESS RULE AND NOT TIDINESS. Code is kernel-checked; prose is unchecked by
construction.** The prose:code ratio is the ratio of verified asset to unverified liability.
Measured across three gate rounds on 2026-08-08: **~12 findings, every one in prose, none in a
theorem statement** — and an 82-line cut then passed all three gates with nothing load-bearing lost,
one deletion being an outright *improvement* because the paragraph asserted a distinction the
artifact could not support. **The corpus's characteristic defect class is prose, and prose volume is
its carrier.**

**MEASURED, so the rule is calibrated and not guessed** (2026-08-08, whole corpus):
- prose **15,629** lines vs code **14,795** excluding Takes — ratio **1.06**, with **129 of 218
  files** already over.
- **The design is already the norm**: file-header blocks run **p50 = 1 line, p75 = 3, p90 = 7**;
  section blocks **p50 = 1, p75 = 6, p90 = 14**; and **85% of declarations already have a
  docstring**. This is **outlier control, not a migration** — the tail runs 121, 115, 100, 83 lines.
- **41% of all prose sits in detached header blocks** rather than attached to what it describes.
  The extreme is `ChoiceCannotBe.lean`: **302 prose lines, five blocks, zero docstrings** — and two
  false universal negatives lived in exactly that prose until 2026-08-01.

**⚠ THIRD-PARTY BACKPORTS ARE EXEMPT STRUCTURALLY, NOT BASELINED** (Tim, 2026-08-08: *"the vendored
bucket we shouldn't touch at all, that's a backport from an official source"*). A baseline entry
means *fix later*; this means **never**. Editing an Apache-2.0 backport's prose also destroys the
diff against upstream, which is the reason for vendoring it. `check_prose.py` skips any file under
`Vendored/` or carrying a provenance header (`VENDORED FROM`, `Apache-2.0`, `Upstream:`) and **names
the exempt files in its output**, so the exemption is visible rather than silent. Currently
`ZeroParadox/Vendored/NaturalOps.lean` (verbatim, Mathlib v4.28.0) and
`ZeroParadox/Ordinal/NaturalOpsPow.lean` (a port of Hernández's Combinatorial Games file) — verified
to match those two files and no others. This removed **140 sites, 119 of them undocumented
declarations we did not author**. ⚠ `check_pov` / `check_modal` / `check_classes` have no vendored
handling; nothing in them fires on those files today, so this is latent, not live — fix it there if
it ever does.

**AND AN INDEX LINE MUST JUSTIFY ITSELF** (Tim, same day): *"every one of those CannotBe line items
should be distinguishable from the others, and the statement for why the CannotBe is applicable
should be directly tied to the specific lines."* A `#check` index is nothing **but** line items, so
a justification sitting in the header leaves every line uncheckable and no two items
distinguishable. **Measured across the six index files:** 47 of 204 `#check`s carry **no gloss at
all** — `BottomCannotBe.lean` is 36 of 72 — while `ChoiceCannotBe.lean` carries **203 header lines
against 31 checks**, which is what "built after the fact" looks like. ⚠ **And the
`Statement:`/`Reading:` convention is applied to 13 of 151 glosses** — zero in four of the six
files. The mechanism meant to stop glosses overclaiming is, in the indexes whose premise is that
they cannot overclaim, essentially absent.

**ENFORCEMENT — mechanical, because this is the SIXTH convention of this shape and the previous
five all leaked.** `python .claude-local/check_prose.py` WARNS at commit; `--block` ENFORCES at
push (`pre-push` § 3b-e). Five rules: a module-doc block over **10 lines** (just above the p90 for
file headers); a docstring longer than its declaration; a declaration with **no** docstring
(`private` and `example` exempt); a `#check` with **no gloss**; and a gloss carrying **no
`Statement:`/`Reading:` label**. Corpus at adoption — blocks 98, over-long docstrings 381,
undocumented declarations 119, bare `#check`s 63, unlabelled glosses 140 — 797 after the vendored
exemption. **Baselined at 778 sites — fires on NEW and EDITED prose only.**
Blocks are keyed by a **content hash**, so editing a grandfathered block re-fires it: the
baseline-shrinking rule enforced rather than remembered. **Detector verified with six controls**
(must-fire on an oversized block, an oversized docstring, an undocumented declaration, a bare
`#check` and an unlabelled gloss; must-suppress on the Take, documented/attributed declarations,
`private`, `example`, and both label forms in same-line, line-above and bolded shapes), plus an
end-to-end control that `--block` exits 1 on a new site and 0 once baselined. ⚠ **The first
baseline silently under-covered by six sites** because a truncated key could end in whitespace,
which `.strip()` destroyed on read-back — a clean-looking zero that was wrong, and the reason the
end-to-end control exists.

⚠ **The failure mode to watch is mine, not the tool's.** Every gate round of that arc, I answered a
finding by *adding a paragraph*, and each new paragraph carried a new claim. **When a section will
not stabilise, cut the essay around the theorem — do not extend it.** That is the § *Prose that
resists correction* protocol arriving at file scale.

## The recurring defect is UNSTATED ADJACENCY — the fix is a pointer, not a theorem

**This corpus's characteristic failure is not wrong theorems. It is true theorems whose reach nobody
recorded.** Measured four times on 2026-07-29/30, each time the honest finding was *"the mathematics is
already here, and nothing says so"*:

* **Oscillation.** Asked whether the framework excludes liar-type flip-flop. `wf_no_cycle` already proved
  it — its own docstring says *"this also rules out 2-cycles"* — and grepping the Lean for "oscillation"
  returned nothing. Fix: instantiate at the two ends + state the fence (the floor is non-well-founded, so
  the exclusion holds ABOVE it and fails AT it).
* **min≡max.** Related coincidences, never cross-linked, so the "both poles" and "both extremes" readings
  drifted as if separate. **NONE of them is a `fork_collapse_iff` instance** — corrected TWICE on
  2026-07-30, because the first fix relocated the error rather than removing it. `fork_collapse_iff` needs
  `[CompleteLattice α]` and a monotone `f : α →o α`; `Ordinal` with `α ↦ ω^α` has a proper class of fixed
  points (`omega0_opow_epsilon`, so nothing collapses), `ZPSemilattice` is a bare join-semilattice whose
  `selfApp` is not an `OrderHom`, and the categorical seam lives in `ModuleCat ℂ`. **They share a SHAPE,
  which across distinct structures is a type boundary, never a common theorem.** State the shape; never an
  instance-of relation.
* **Turing machines.** `Occurrence.lean`'s results are stated over `σ → Option σ`, which **is** Mathlib's
  `StateTransition`; `Turing.TM0/TM1/TM2.step` all have that exact type and Mathlib's TM development is
  *built on* it. So those results already cover every Mathlib Turing machine — and the corpus had never
  mentioned `Turing.*` once.
* **The descending-chain form.** The INFINITE-pole reading of the floor sat in a Mathlib biconditional
  (`wellFounded_iff_isEmpty_descending_chain`) that this family had never cited.

**The rule.** When a question arises and the answer turns out to be already proved, **the deliverable is a
POINTER, not a new declaration.** Adding an elementary instantiation is the failure mode the prior-art gate
keeps catching (see Trigger 0). Ask in order: is it proved here already? is it in Mathlib? is the gap only
that nobody wrote it where the question gets asked? If the last — write it *there*, at the site the reader
lands on, not five sections away.

**Two corollaries worth their own line.** (1) **Generality is why the results are weak, and also why they
are free** — a theorem over `σ → Option σ` is elementary *because* it covers everything, and covering
everything is the payoff; state both halves. (2) **Adjacency is not identity.** "Turing machines are
witnesses" is licensed; "the bottom is a Turing machine" is a cross-carrier identity and the same type
boundary as everywhere else. The `QuineHost` precedent is the model: never "we commit to AFA", always "here
are the requirements, and AFA is a witness meeting them."

### And the pointer must not become a COPY. Never enumerate in prose what the artifact defines.

**A pointer that re-lists its target's contents is a second copy of the definition, and a second copy
drifts.** This is the general form of a rule this file already states three times for three specific
figures — the choice-footprint count ("NO COUNT — measure on demand, never record one"), the
`papers/` file count, and the `LEAN_CUSTOM_REGISTRY` tally. It is one rule, so state it once:

**Do not write into prose any count, tally, field list, instance list, or "these are the N conditions"
enumeration of something a Lean file, a directory, or a data store already defines.** Point at it, name
the one or two members that are load-bearing for what you are saying, and let the reader open it.

**Measured 2026-08-04 — the same defect twice in two rounds, one level apart, in the same paragraph.**
A pointer block added to `ZeroParadox/Valuation/PoleCornersBridge.lean` said `InfinitudeFloor` had
**four** realizations (there are five — `boundaryFloor` was missed) and, after that was fixed, said the
class had **two** conditions and that this "is the whole requirement" (it has three, and the dropped
`cx_floor_eq_iSup` is the load-bearing one, the field the headline theorem rewrites with first). Both
are the same error: **a completeness claim about an artifact's contents, asserted in prose that cannot
check itself** — in a file whose entire job was to POINT AT that artifact.

**Why enumeration specifically, and not just counts.** A count at least looks like a figure and invites
the "measure it" reflex. A field list reads as *description* and invites nothing, which makes it the
more dangerous of the two. Both are completeness claims; neither is checkable from where it is written.

**What IS legitimate to write down:** a **dated survey result** — "realizations located as of
&lt;date&gt;: …" — because that is a measurement, not a re-copy, and the date says so. Same for
"none located as of &lt;date&gt;" over "none exists" (§ the choice index's universal-negative rule).
The distinguishing question: *would this sentence be wrong if someone added a field tomorrow, with
nothing mechanical noticing?* If yes, it is an enumeration — replace it with a pointer or a date.

## Determinism is the SINGLE recurring cost — name it, don't rediscover it

**Every "the bottom cannot move" result in this corpus is powered by SINGLE-VALUEDNESS, not by
self-reference.** This surfaced four separate ways in one session (2026-07-30) and was re-derived each
time, so it is written here rather than left to be found five sections into a file:

- `machine_snap_impossible` — nothing is both its own fixed point and departed from. `Occurrence.lean` § VI
  states the diagnosis: *"the obstruction of § III is the absence of fan-out, not the presence of a fixed
  point."*
- `deterministic_has_no_fanout` — a function `σ → Option σ` admits at most one successor. That is the
  whole obstruction.
- `nondeterministic_escapes_the_trap` — a **relation** can loop at `s` *and* reach elsewhere. That is the
  whole escape.
- `execution_requires_branching` — stated over a **relation** for exactly this reason.

**The consequence to carry into any prose about the trichotomy:** halted / self-looping / stepping-onward
are three distinct **states** under any dynamics, but under a **function** the first two share a **FATE** —
`loop_is_a_trap` and `eval_of_halted` each give a singleton reachable set. The trichotomy is genuinely
three-valued **only** in the non-deterministic setting; make the step single-valued and the self-loop is a
relabelled trap. So **"could it still move?" is a MODAL question, and the framework encodes that modality as
the function-vs-relation choice — nothing else.**

**Do not re-derive this, and do not attribute the obstruction to the fixed point.** The self-loop is not
what blocks departure; being a function is. Note also what it is NOT: this says nothing about whether the
bottom *does* move. Non-determinism buys the *possibility* and never the *occurrence* — see `l_inf`'s
docstring, and `tri_idle_never_starts`, where a perfectly well-formed third state sits inert forever.

## The Two-Pole Test — Hard Rule. Run BOTH readings of ⊥ concurrently, never one.

**⊥ = 0 = ∞ is the framework's own pole identity (`rInv_swaps`). So every face of ⊥ has TWO readings —
the EMPTY one and the INFINITE one — and a face that implements only one is half-built.** Build and check
both concurrently. Do not sequence them, and do not treat "which first?" as a real question: the poles are
one object seen from two ends, so picking one builds half and forces a later switch.

**The test, run on every new development and on any face that is stuck:**
- **Q1 — where is the zero that runs to infinity?** (valuation, frequency, surprisal, self-reference…)
- **Q2 — what is the one-way arrow, and what does it look like run backwards?** (reversal is the
  *inversion*, never a second construction.)

**If either has no answer, the piece is not part of the framework yet, or its floor has not been found.**
That is a finding, not a stall — record it.

**The measured case that made this a hard rule (2026-07-26).** ZP-K's computational bottom is
`MachinePhase.initial`, whose own comment reads *"machine exists; no instruction fetched"* — a pure EMPTY
reading, with no infinity in it. **Q1 has no answer there**, and the test was never run. The consequence
was not cosmetic: because a machine that has fetched nothing has no reason to fetch anything, the claim
that ⊥ *executes itself* needed an ontological bridge, and that bridge is a commitment rather than a
theorem (see `l_inf`'s docstring, which says so honestly). **The INFINITE reading of the computational
bottom is divergence — the non-terminating computation — which does not need starting because it is
already running.** The occurrence problem is an artifact of implementing one pole.

**The diagnostic value, stated generally:** when a claim will not close, or a face needs an extra
assumption to work, **first check whether only one pole has been built.** A missing pole shows up as a
bridge you cannot formalize.

### The test applies to METHOD, not only to objects (Tim, 2026-08-07)

**A search that implements one polarity is a half-built detector, for exactly the reason a face that
implements one pole is half-built.** Tim, on being shown that four of five false negatives in one
session were one grep away in the opposite polarity: *"that polarity is the nature of the project — I
feel like every instance we can have will have that structure."* He is right, and **Q2 above is already
that question**, asked of a construction rather than of a search: *what does the one-way arrow look like
run backwards?*

**So run the test on the METHOD:**
- **Q1-M — what would this claim look like stated from the other side?** *"Seed-independent"* and
  *"⊥ is **a** seed, not a distinguished one"* are one fact. *"Converges"* and *"diverges"*. *"Is
  used"* and *"has no call sites"*. **Search both, or you have searched half.**
- **Q2-M — if the corpus disagreed with me, what words would it use?** That phrasing is where a
  contradicting result is sitting, and it is the phrasing you will never reach from your own.

**Measured, same day:** `seed-independent` → 0 hits; the inverse `"a seed, not"` → the section that
already proved it, by Tim, eight days earlier. `atTop (nhds _)` → 13 convergent files; the inverse
`atTop atTop` → the divergences, in files the survey never saw. Both had already shipped into docstrings
as measured fact. See § *NOT IN THE LIBRARY IS A CLAIM* step (c) for the operational form.

**⚠ Where it STOPS, and the framework already names the exception.** *"Every instance"* is the right
instinct and needs one qualifier the corpus itself supplies: the fifth POV KIND, **INVARIANT** — *"the
quantity does not transform; flipping the chart gains nothing."* That is the ratified slot for polarity
**not** applying. Four of the five KINDs are two-sided (COINCIDENCE, INVERSION, DRIFT, CARRIER); the
fifth is the null case. **So: expect polarity, and when flipping genuinely gains nothing, say INVARIANT
rather than forcing a second pole.** A rule that fires everywhere is the cry-wolf shape this file
elsewhere says to narrow rather than tolerate.

**Why this is here and not only in memory.** It *was* only in memory
(`feedback_two_part_lens_call_out`), where the body does not load — only the one-line index entry does,
competing with ~100 others. It did not fire for months. Per this file's own rule: *memory is for context,
not enforcement.* The memory keeps the full lens (the which-first corollary, the external-evaluation
corollary, and the call-out protocol for where Tim's human read is load-bearing); **the binding
obligation is here.**

**Call-out protocol (retained from the memory, still required):** when development turns on this lens —
a floor to locate, a reversal to characterize, a 0↔∞ swap — say so explicitly and flag it as needing
Tim's read rather than guessing; and when his input on such a point proves load-bearing, name what it
changed instead of presenting the result as self-derived.

## Prose that resists correction is a CLAIM defect. Revalidate, don't redraft. Hard Rule.

**If a sentence has to be fixed three times, the sentence is not the problem.** Stop editing it and go
measure the claim underneath. This is gate-enforced: `gate_round.py` prints a MANDATORY CLAIM
REVALIDATION protocol at **round 3**, or as soon as the **same `--target` has been re-fixed 3 times**.

**Why (measured 2026-08-03, Tim's call).** One remark-box sentence in ZP-P was wrong in **six
consecutive versions** — v1.9 a universal, v1.10 a doubling, v1.11 the universal restored, v1.13/v1.14
a false universal, v1.15 a false uniqueness. Four gate rounds ran over it. **Every round passed the
citations, because the citations were always correct.** The defect was one level down: the claim the
sentence existed to support — that Mathlib's `Classical.choice` in `cofix_nonempty` is *"an artifact,
not a necessity"* — had never been measured by anyone. **One probe settled it in a minute:**

```
QPF.Cofix         (the TYPE) : [propext, Classical.choice, Quot.sound]
PFunctor.M.corec             : does not depend on any axioms
```

`QPF.Cofix` carries choice **in the type**, so *no proof of any statement mentioning it can be
choice-free* — "removable in principle" was not merely unproved, it was unprovable as stated. The
honest, measurable version nobody had written: the choice comes from Mathlib's **QPF quotient layer**,
not from the mathematics, and the corpus already witnesses the same inhabitation choice-free
(`strict_cofix_nonempty`). ⚠ **Do NOT sharpen that into "the M-type underneath is axiom-free"** — the
former and constructors are, the **destructor is not**, and that sharpening is the bedrock defect
recorded below. That ACS is choice-free is a separate fact: an ω-limit with no quotient layer.

**The generalizable lesson: the gates check WORDING against SOURCES. They cannot see an unmeasured
claim, and they will keep passing one forever.** Six rounds of prose editing could never have found
this. A one-minute probe did.

**⚠ MODAL CLAIMS ARE THE HIGH-RISK CLASS — and this corpus is full of them.** *"not a necessity"*,
*"an artifact"*, *"in principle"*, *"could be removed"*, *"eliminable"*, *"inherited from Mathlib"* are
claims about what **cannot be proved**, and a footprint measurement can never establish one:
- **ACCIDENTAL** is proved only by **EXHIBITING** the clean proof.
- **ESSENTIAL** is proved only by a **REDUCTION** to a taboo.
- **`#print axioms` follows the STATEMENT, not the proof.** A *type* can carry an axiom — then no
  proof is clean, and every "removable" claim about it is false. **Measure the type, not just the
  theorem.**

**The protocol, when the tripwire fires:** name the claim in one line without its framing → ask what
would settle it and whether anyone did that → probe it in the scratchpad (`lake env lean` on a
standalone file needs no repo write) → then either restate to exactly what was measured, or restate as
an explicit conjecture, **or delete the sentence**. **Deleting is legitimate and often correct**: if an
accurate statement already lives in a checkable file, published prose does not need to relitigate it —
that is how the ZP-P case was finally closed (v1.16, Tim: *"if the Lean is accurate, just delete the
problem sentence"*).

**Record what the MEASUREMENT showed, not that you re-worded something.** A changelog entry saying
"clarified" after a revalidation round is the failure repeating.

### The sweep this produced, and what it found on the first run (2026-08-03)

`python .claude-local/check_modal.py` (WARN at commit) / `--block` (pre-push § 3b-c). Baselined like
`check_pov.py`: fires on NEW sites only. It flags modal vocabulary not accompanied by a measurement, a
reduction, an explicit non-claim, or a **named exhibited witness**.

**Yield, first run: 31 sites → 3 real defect clusters.**
- **A FALSE UNIVERSAL NEGATIVE LIVE IN A PUBLISHED PDF.** `ZP_Choice_Free_Core_Addendum` § III said
  *"The framework has no proven-necessity case anywhere."* Two taboo reductions exist
  (`em_of_wellOrder_comparable`, `wem_of_fixedPointFree`) and **neither was named anywhere in that
  document**. The 2026-08-01 sweep that recorded both universal negatives as removed had grepped
  `.lean` and **missed a Python build script** — so the claim survived in rendered public prose.
  **Grep the CLAIM across every surface that renders, not just the sources.**
- **The `Cofix` cluster, 9 sites including `CLAIMS.md`.** Restated from inference to measurement.
- **Six sites were already honest** — retractions, `UNCLASSIFIED` tiers, explicit "does not show"
  fences. `SnapNucleus.lean` had measured this correctly in July, including that `Ordinal` the *type*
  is choice-free while `Ordinal.instLinearOrder` is not. **Read hits, do not count them.**

**⚠ THE DETECTOR SHIPPED WITH THREE FALSE-NEGATIVE PATHS, AND EVERY ONE WAS FOUND BY A PROBE RATHER
THAN BY READING THE CODE.** All three would have made a clean `0` meaningless:
1. **`#print axioms` listed as *evidence*** — so a claim beside a `PurityCheck` block was suppressed,
   which is exactly where these claims live. A footprint is the one thing that **cannot** establish a
   modal claim. Removing it surfaced two real sites at once.
2. **One wide evidence window** — a live claim passed because the word *"measured"* sat six lines away
   describing a **different** measurement. **Proximity is not aboutness.** Fixed with two tiers: weak
   tokens (`measur`, a named witness) must be in the *same sentence*; structural markers
   (`retracted`, `UNCLASSIFIED`, `NOT claimed`) may sit wider.
3. **Literal spaces in the pattern** — so any claim *wrapped across a line* was invisible, and Lean
   docstrings wrap constantly. Two fixes were needed: `\s+` between words, **and** blanking the
   `--` / `//` / quote-join separators that sit in the gap (to spaces of **equal length**, so line
   numbers stay exact). The first fix alone still missed a wrapped Lean comment — measured by probe.

**VERIFY THE DETECTOR BEFORE BELIEVING A ZERO.** Plant a known-bad line *in the shape you actually
expect* — wrapped, comment-prefixed, near a purity block — confirm it fires, then remove it. A probe
in the wrong shape passes and teaches you nothing: the wrapped probe was written flat first and gave
a false all-clear. Keep a reproduction script in the scratchpad with **both** must-fire and
must-suppress controls; a checker that fires on everything is as useless as one that fires on nothing.

**The measured facts worth not re-deriving** (⚠ the first version of this block listed only
`PFunctor.M no axioms` and that half-truth immediately re-seeded a bedrock defect — see below):
```
PFunctor.M       (TYPE former) no axioms       ]  the M-type's FORMER and
PFunctor.M.mk                  no axioms       ]  CONSTRUCTORS are clean
PFunctor.M.corec               no axioms       ]
PFunctor.M.children  [propext, Classical.choice, Quot.sound]  <-- THE ORIGIN (destructor)
PFunctor.M.dest      [propext, Classical.choice, Quot.sound]
QPF.Cofix  (TYPE)    [propext, Classical.choice, Quot.sound]  <-- inherits via Mcongr/IsPrecongr
strict_cofix_nonempty          no axioms       -- clean because it only BUILDS, never destructs
Ordinal    (TYPE)              [propext, Quot.sound]                    -- choice-FREE
Ordinal.instLinearOrder        [propext, Classical.choice, Quot.sound]  -- the instance hazard
Ordinal.nfp / .epsilon         [propext, Classical.choice, Quot.sound]
padicValNat                    [propext, Classical.choice, Quot.sound]
```
**Read that table as a whole or not at all.** *"`PFunctor.M` is axiom-free"* is true of the **type
former** and says nothing about its **eliminators** — and citing it to conclude *"the choice is not
from the M-type underneath"* is a **witness-vs-statement defect**, which is exactly what shipped to a
published PDF on 2026-08-03 under the word *"Measured"* and was caught by the gate measuring it.
**The choice DOES come from the M-type — from its destructor.**

**The accurate account is stronger than the false one it replaced:** choice enters at
`M.children`/`M.dest`; `Cofix` inherits it in the type through the congruence it quotients by; and
`strict_cofix_nonempty` is axiom-free **because it only builds and never destructs**. So the escape is
not "use `M` instead of `Cofix`" generically — it is *build without destructing*. Attributing the
footprint to the **QPF quotient layer** is defensible and is the claim to keep; *"not from the
M-type"* is false and must not be re-introduced.

## "NOT IN THE LIBRARY" IS A CLAIM. Probe it before you believe it. Hard Rule.

**The characteristic error of 2026-08-04 was not a wrong theorem. It was three wrong NEGATIVES**, each
of the form *"X is not available"*, each recorded as measured, each false:

| the claim | what was actually there |
|---|---|
| *"`pole_inversion` is not available on `ℤ_[2]`"* | true of the class instance, **false of the content** — both halves of the drift were already proved (`towerCx_zero`/`towerCx_member`, `tower_converges_to_zero`); only the packaging was missing |
| *"`WellPowered (Type 0)` does not synthesize"* | `instance : WellPowered.{u} (Type u)` sits in a module **titled** *"`Type u` is well-powered"*; the probe failed on an unimported name and an **unresolved universe parameter** |
| *"AMM Def 2.14 clause (c) is not a Mathlib concept"* | **derivable in six lines** — `IsStableUnderColimitsOfShape.condition` already has that exact shape; instantiate its second diagram at the constant functor |

**A failed `#synth` is EVIDENCE ABOUT YOUR PROBE, not a fact about the library.** It has at least four
innocent causes, and all four were hit in one day:
1. **Not imported.** `unknown identifier` and `failed to synthesize` look alike in a hurried read, and
   `Mathlib.Tactic` does not reach most of `CategoryTheory`.
2. **Universe parameters.** `WellPowered (Type 0)` fails; `WellPowered.{u} (Type u)` succeeds. An
   unresolved metavariable in the goal is the tell — read it.
3. **A different name.** Grep the CONCEPT, never the name you would have chosen.
4. **Decomposed into parts.** The thing is not absent, it is *assembled from* pieces that are present —
   the clause-(c) case, where a three-clause definition had two clauses as instances and the third as a
   short derivation. **A definition can be available without any declaration bearing its name.**

**The rule.** Before writing *"not in Mathlib"*, *"the corpus does not have"*, *"no instance exists"*, or
any dated survey negative: **(a)** confirm the name is imported and elaborates at all, **(b)** re-run
with universes explicit, **(c)** **run THREE phrasings, and make one of them the INVERSE** (see below),
and **(d)** ask whether it decomposes. Then write **"not located as of &lt;date&gt;, searched as
follows"** — never *"absent"*.

### (c) in full — THREE PHRASINGS, AND THEY MUST VARY ALONG AXES, NOT BE SYNONYMS. Tim's rule, 2026-08-07, measured three times the same day.

Step (c) used to read *"grep the concept in at least two vocabularies"*. That is the right principle and
it kept failing, because it says nothing about **which** vocabularies — and three synonyms of one
formulation are one search run three times. **Vary along the three axes below. Each has its own measured
false negative from a single session.**

| axis | run BOTH ends | the failure it prevents |
|---|---|---|
| **1. POLARITY** | the claim / **its inverse** — how the corpus would say it if it *disagreed* with you | you find only the half stated your way |
| **2. PART OF SPEECH** | the **noun** (the object) / the **verb** (the operation that produces it) | you search for the *thing* and miss the *step that makes it* |
| **3. VOCABULARY** | your words / the **domain's** words | you find only what you would have named it |

**Measured, all on 2026-08-07, all having already shipped into docstrings as fact before a gate or Tim
caught them:**

| axis | the claim | what was run | what should have been run |
|---|---|---|---|
| POLARITY | *"the corpus never measured seed-independence"* | `seed-independent` → **0 hits** | `"a seed, not"` → lands directly on `Epsilon0MinMax.lean` § I-b, which states the theorem, the proof route, and the verdict *"Elementary and not novel"* |
| POLARITY | *"every `Tendsto` in the corpus runs inward"* | `atTop (nhds _)` → 13 files, all convergent | `atTop atTop` → the divergences, immediately, in files the survey never saw |
| **PART OF SPEECH** | *"the succession of bottoms is not formalized"* | the NOUN — `family of bottom`, `botSeq`, `ℕ → .*Bot` → nothing | the VERB — `next bottom`, `re-seed`, `succ` → **`succession_succ`**, the n → n+1 re-seeding theorem, which had been there all along |

**⚠ The part-of-speech axis is the newest and was the most expensive**, because it produced a *published
note* asserting a formalization did not exist. Tim: *"you need to look closer at n and n+1 logic. we very
likely already have this belt."* **A corpus names an operation and a thing differently, and formal corpora
overwhelmingly declare the OPERATION** — `succession_succ`, `snapNucleus`, `nfp` — while prose about them
uses the noun. **If you are asking whether a structure exists, search for the step that builds it.**

**Why the inverse specifically.** A corpus records a fact in whichever polarity its author found natural,
and that is frequently the opposite of yours. *"Seed-independent"* and *"⊥ is **a** seed, not a
distinguished one"* are the same fact; only one of them is greppable from the other. Likewise
*"converges"* / *"diverges"*, *"is available"* / *"cannot be stated"*, *"is used"* / *"has no call
sites"*. **A single-polarity grep is a detector with a blind half**, and this file's own
*"VERIFY THE DETECTOR BEFORE BELIEVING A ZERO"* applies to it.

**A bonus worth expecting:** the inverse grep surfaces the corpus's *idioms*. `"a seed, not a
distinguished one"` also returned `Computability/Kleene.lean`'s *"computational quine, not a
distinguished one"* — the same sentence shape used for a different object. Finding the idiom is how you
find the other places the claim is made.

**The generalization, now that there are three axes:** a search is a **projection**, and a projection
loses whatever is orthogonal to it. Polarity, part of speech and vocabulary are the three projections
this corpus has actually been caught by; there is no reason to think they are the only three.
**When an absence matters, ask what dimension your query collapsed** — and note that this is the
Two-Pole Test again (§ above), which is itself a rule about never looking from only one end.

**Why this is its own section and not a footnote.** This file already says
*"VERIFY THE DETECTOR BEFORE BELIEVING A ZERO"* — but scoped to `check_modal.py`, so it did not fire for
`#synth`, and the identical failure recurred three times in one day. **The generalization is the point:
any tool that reports absence needs its absence-reporting verified before the absence is believed.**
It also compounds: each false negative was written into a docstring as a *measured* fact, which is the
`CannotBe`-index universal-negative hazard arriving through a new door.

**And the payoff for checking is real, not just defensive.** Correcting the three negatives above turned
"one of four hypotheses holds" into "three of four", and put an instance-of claim the corpus had twice
withheld back within reach. **Searching harder gets you MORE** — the same lesson as Trigger 0.

## Review-Loop Cap — Severity-Tiered, Hard Rule

**The gates will always find something. Stopping is a decision about SEVERITY, not a wait for silence.**

- **BEDROCK severity → up to 5 iterations.** A violated core invariant (`ε₀ ≠ 0`, `ε₀ ≠ ⊥`, min≡max
  flattened, the snap-arc returning to the same ⊥, a cross-type `=`), a **fabricated** claim about an
  external source, or a false premise carrying a conclusion. These must not ship — keep iterating.
- **ORDINARY severity → 2 iterations, then STOP and push normally.** Citation scope, a mischaracterized
  lemma, hedging a tier too strong, path-convention drift, wording. These never reach zero.

**The stopping question is "did this round find anything BEDROCK?" — if no, stop**, even on ten ordinary
findings. Ratified 2026-07-19 after three rounds; memory `feedback_er_ar_max_iterations` carries the
detail.

**⚠ NO `--no-verify` IS INVOLVED, AND THIS LINE USED TO SAY OTHERWISE (corrected 2026-08-01, Tim).**
It read *"2 iterations, then push `--no-verify`"* — wording that predates the reviewer refactor and
describes a scheme that no longer exists. **Under the current scheme a STOP-ORDINARY reviewer WRITES
ITS SIGNAL**, so at the ordinary cap the hook clears **on its own merits** and there is nothing to
bypass. Say so in the brief: *withholding the signal on ordinary findings is not a valid outcome.*
- **Why the stale wording was worse than merely wrong:** it trained the bypass reflex for a situation
  that can no longer arise, which is exactly the hazard § *NEVER write a `--no-verify` fallback*
  exists to prevent. **Measured the day it was corrected:** at the cap, with all three gates saying
  PUSH and post-review edits having staled every signal, Claude proposed `--no-verify` **citing this
  line**. Tim overruled it and called for a re-signature round instead.
- **And he was right on the substance, not just the procedure.** The cap's licence assumes the
  outstanding findings *stay outstanding*. Once you have **acted** on them, the push contains **new
  unreviewed prose** — a different thing from known debt, and new prose warrants a gate, not a flag.
  Vindicated immediately: four of the next round's six editorial findings landed in the one file no
  gate had yet seen, which existed only because it was edited after the gates finished.
- **The rule that falls out:** *fixing a finding restarts the obligation for the text you changed.*
  If you edit after a STOP-ORDINARY, re-sign — do not bypass. If you do not want another round, then
  do not edit: record the findings as next-touch debt and push what was actually certified.

### Prose about PREVIOUS STATES is redundant. Git holds it. (Tim, 2026-08-08.)

**This project already ratified the argument, for documents, and never applied it to prose.** The
`historical/` folder was retired because *"git history and each release's Zenodo snapshot are records
more complete and authoritative than a hand-maintained archive"* — the archive drifted a month out of
date; those do not. **A retraction record in a docstring is a hand-maintained archive of prior
states.** Same object, same failure mode.

**Measured 2026-08-08: 87 lines across 39 `.lean` files** carry prior-state prose (*"an earlier
draft"*, *"was FALSE"*, *"is retracted"*, *"previously read"*, *"until 2026-…"*). **The distribution
is the finding** — the top six are the files most recently through the gate loop. This prose is not
spread through the corpus; **it is what the review loop deposits**, and nothing prunes it.

**The cost is not tidiness.** In one three-round arc the correction layer grew to ~40% of a 96-line
section guarding **two** declarations, and **generated a new defect in every round** — including a
retraction that misdescribed its own subject, and a "corrected" claim (*"proved by `funext`, not
`rfl`"*) that a gate refuted by running it. **Records about records are unverifiable by construction
and nothing checks them.**

**THE RULE — apply the strip test.** Remove the *"an earlier draft said X, which was wrong"* framing
and read what is left:

* **Something remains, and it is MATHEMATICS** — then that is **content**, and its provenance in an
  error is irrelevant. **State it positively and delete the framing.** Worked examples from that arc,
  all worth keeping and none needing a retraction to say: *`deriv` is not `nfp`, and here is the
  counterexample*; *ε₁ is a fixed point, so it is the one seed that makes the wrong reading look
  supported*; *an all-zero prefix names the same end, so the discriminator is a nonzero digit.*
* **Nothing remains but history** — **delete it.** `git log -p` has it, exactly, permanently, with
  provenance no docstring can match.

**Where history actually belongs:** `.claude-local/DEFECTS.md` while a defect is open, the
gate-findings archive once it is closed. Both are read when choosing work; a docstring is read when
doing mathematics. **The defects that recurred despite earlier fixes did not recur because a docstring
lacked a retraction — they recurred because the ledger was not consulted.**

**YES, THIS MEANS FIX IT SILENTLY — in the file.** (Tim asked directly; an earlier version of this
paragraph said the opposite two sentences after saying this, which is the rule about error-narratives
containing an error-narrative contradiction.) **Delete the false claim, state the true one, and let the
COMMIT MESSAGE be the narrative.** That is its job, it is versioned, and it is where a reader looking
for history will actually go.

**The record is never lost, because it lives in three places that are not the docstring:** the commit
message, `.claude-local/DEFECTS.md` while the defect is open, and the session itself. **The only thing
being removed is a fourth copy — the one that cannot be checked, drifts, and accumulates.**

⚠ **The narrow thing that is NOT permitted:** letting a fix be invisible **everywhere**. Do not skip
the ledger on an open defect, do not bury a substantive correction under a vague commit subject, and do
not decline to surface it — cross-arc patterns are caught by the human, repeatedly and by measurement,
and he cannot catch what he is not told. **Silent in the artifact, recorded in the process.**

⚠ And this does not touch the dated-survey convention (*"none located as of &lt;date&gt;"*), which
records a **measurement**, not a prior state.

### The cap is enforced by the REVIEWER, not by the caller — pass it the round number

**Why: a rule about a loop does not fire from inside the loop.** Each round is locally justified ("a gate
found real defects; fix them"), so the caller never evaluates the trigger — on 2026-07-19 three rounds ran
against a 2-round cap while the rule sat visible in the memory index, because nobody was *counting*. The
fix is structural: the reviewer stands outside the loop, so give it the number and let it decide.

**The CALLER bumps, exactly once, before spawning the round:**
```
python .claude-local/gate_round.py bump --target <what-is-being-re-fixed>   # caller, once per ROUND
python .claude-local/gate_round.py show                                     # reviewers: read-only
```
**Always pass `--target`.** Use a stable slug for the thing being corrected, not the round's topic —
`zpp-remark-veltri-modality`, not `round-3`. It is what makes the revalidation tripwire fire on the
real signal (*the same sentence re-fixed*) rather than on round count alone. A target re-fixed three
times prints the MANDATORY CLAIM REVALIDATION protocol; see the § above, and **follow it before
drafting another fix**.
`reset` at the start of a new arc or after a clean push. State lives in `.claude-local/gate_round.json`,
so it survives compaction.

**Reviewers must NEVER `bump`** — they are handed the number in the brief and may only `show`. Measured
2026-07-19: the caller bumped to round 1, a spawned reviewer ran `bump` itself, and reported round 2. A
double-increment is not cosmetic — it burns the cap early and can force a premature STOP-ORDINARY while a
bedrock defect is still live. If several gates run in one round, they all share that round's number.

**Put this in every review brief, with N substituted:**
> This is **gate round N** against a cap of 2 (ORDINARY) / 5 (BEDROCK). Your verdict must be one of:
> **PASS** — nothing found.
> **FAIL-BEDROCK** — you found a violated core invariant, a FABRICATED external-source claim, or a false
> premise carrying a conclusion. The loop continues.
> **STOP-ORDINARY** — round N is past the ordinary cap and nothing you found is bedrock-tier. Report the
> findings, then state explicitly that the correct action is to PUSH, not to iterate. Do not recommend
> another round.
> If N is past the ordinary cap, you must actively choose between FAIL-BEDROCK and STOP-ORDINARY — a bare
> "FAIL" is not a valid verdict, because it hands the stopping decision back to the party inside the loop.
>
> **If N ≥ 3, or if this text is a passage you are being asked to re-check for the third time: do NOT
> report a wording fix.** Report the CLAIM the passage exists to support, whether anything actually
> establishes it, and what measurement would settle it. Watch specifically for modal claims —
> "not a necessity", "an artifact", "in principle", "removable", "eliminable" — which no footprint
> measurement can establish (accidental needs an EXHIBITED clean proof; essential needs a REDUCTION;
> `#print axioms` follows the STATEMENT, so a TYPE carrying an axiom makes "removable" false for every
> possible proof). **A verdict that only re-words a passage that has already been re-worded twice is
> not a useful verdict.** Recommending DELETION is in scope and is often the right answer when an
> accurate statement already lives in a checkable file.

**Two measured reasons the loop cannot converge, which the cap exists to bound:**
1. **Fixes introduce errors.** Every fix is new prose carrying new claims. Two of round 3's eight
   findings were created by round 2's fixes. A loop whose corrections generate errors asymptotes above
   zero.
2. **Fix-the-site, not-the-class.** Three of round 3's findings were unpropagated instances of round 2's
   fixes. **Before declaring a kill fixed, grep the corpus for the CLAIM, not the named file.** Note that
   retractions quoting an error pollute that search — read hits, do not count them.

## NEVER pipe `git push` through `head`/`tail` — it BYPASSES the pre-push gate. Hard Rule.

**Measured and reproduced 2026-07-26.** The same push, same repository state, same signals:

```
git push --dry-run origin <ref>                    → exit 1   (blocked, correctly)
git push --dry-run origin <ref> 2>&1 | head -5     → exit 0   (SUCCEEDS — gate bypassed)
```

**Mechanism.** `head` exits after N lines and closes the pipe. The hook is still writing (it produces
~90 lines: file-reference resolver, invariants, hash check, font checks, then the review-signal check
*last*). It dies of SIGPIPE **before reaching its `exit 1`**, and git proceeds with the push. The review
gate never runs — and its output is at the END, so any truncation short enough to be useful is long
enough to skip it.

**This actually happened.** A twelve-file push whose `pa_cleared.txt` was stale was blocked on the first
attempt, then went to `origin` on a second attempt run as `git push … 2>&1 | head -40` — issued only to
read the hook's output. Nothing else changed.

**Two defences, both now in place:**
1. **The hook is SIGPIPE-immune.** `trap '' PIPE` on line 2 of `.git/hooks/pre-push` (and the
   version-controlled copy at `.claude-local/proposed_pre_push_hook.sh`). Verified: the truncated push
   above now exits 1, and a nothing-to-push still exits 0. **Hooks live in `.git/` and are NOT
   version-controlled — this fix must be re-installed per clone from the staged copy.**
2. **Do not truncate push output.** Redirect to a file and read that:
   `git push origin <branch> > /tmp/push.log 2>&1; echo $?` then inspect the log. Never
   `| head`, `| tail`, `| grep -m`, or any consumer that exits early. The same hazard applies to any
   hook-running command whose output you truncate.

**Why this is filed as a hard rule and not a footnote:** a gate that can be cleared by re-running the
command with a pipe is not a gate, and it fails *silently* — the push looks green. Anything that reaches
a public remote must pass the gate on its own merits, not because a reader closed the pipe early.

**Scope of the pipe hazard, measured after the fix:** `head` and `grep -q` (and `grep -m`, `sed q`, any
consumer that exits before EOF) all sever the pipe early; `tail` does not, because it reads to EOF. With
`trap '' PIPE` installed the hook survives all of them and still exits 1. **The rule stands anyway** —
do not rely on the trap being present in a fresh clone, since hooks are not version-controlled.

### And NEVER write a `--no-verify` fallback into a push command. Hard Rule.

**Measured 2026-07-26 — self-inflicted, same session as the pipe bypass.** A command of the shape

```
git push origin <branch> ... || git push --no-verify origin <branch> ...
```

was written to "handle" a possible block. **That is an unconditional, silent gate bypass**: if the gate
fires, the fallback pushes anyway, and the transcript shows a successful push. It did not fire that time
only because the push was `CLAUDE.md`-only and therefore gate-exempt. It would have bypassed a real block.

`--no-verify` is legitimate **only** as a deliberate, separately-typed decision for a known-good reason
(the documented case is a `CLAUDE.md`-only change against a stale signal), never as an automatic fallback
and never chained with `||`. If a push is blocked, **read the reason and fix it** — the block is the
control working.

## Staging — `git add` NAMED PATHS, never `-A`, Hard Rule

**`git add -A` stages whatever happens to be in the tree, including files this session did not create.**

**Measured 2026-07-19:** a background review agent wrote a scratch probe into `ZeroParadox/`, and the next
`git add -A` swept it into a commit unnoticed. It is in the permanent history now. Background agents run
*concurrently* with commits, so the working tree is not a stable snapshot of what you intended to change.

**The rule:** stage the specific paths you edited — `git add path/one path/two`. Before committing, run
`git status --short` and confirm every staged path is one you meant to touch. If a path appears that you
did not edit, find out where it came from before committing it.

`-A` is acceptable only when nothing has been spawned since the last commit and `git status` has been
eyeballed. When in doubt, name the paths.

## Rules That Must Reach Spawned Agents — Hard Rules

**Why this section exists (measured 2026-07-19).** A spawned agent receives, automatically: this file in
full, the user-level `CLAUDE.md`, the Lean `.claudecodes` block, the project-standards block — **and the
memory INDEX only, not memory file bodies.** So a rule whose content lives in a memory body reaches a
subagent as one line among ~100 in an index, competing for attention with ninety-nine others, firing at
no particular moment. That is not a control.

**The consequence, verified:** a subagent invented a factual detail about a cited paper while the line
*"Draft from source only — public math claims must trace to a specific source passage"* was sitting in
its index. The rule was visible and did not bind. **A rule that must not be violated belongs HERE or in
the task brief. Memory is for context, not enforcement.** When delegating, carry the relevant rules below
into the brief explicitly — the same way the encoding and glob warnings are already carried.

- **Draft from source.** Never describe the content of a source you have not read. Cite existence (title,
  venue, that it exists) freely; assert specific technical content **only with the passage in hand**. If
  you cannot read it, say so explicitly — do **not** soften a specific into a vaguer assertion about a
  paper nobody opened. Applies to Lean docstrings citing external papers, companion sections, discussion
  comments, and outreach. Before concluding a PDF is unreadable, try `pypdf`/`pdfminer` directly
  (`.claude-local/extract_pdf_text.py`); a fetch tool's failure is not a fact about the source.
- **Start new files from the templates.** Any new `.lean` file starts from `.claude-local/templates/`
  (`TEMPLATE_lean.lean`, `TEMPLATE_experimental_mapping.lean`) and its `README.md`. Note the template's
  namespace line is stale — namespaces are FLAT (`ZeroParadox`), not `ZeroParadox.ZPX`.
- **Never write a bare "bottom."** Always say which level: the structureless referent / a specific
  structured instance (a face) / the family-and-schema. The bare word sliding between senses is the
  project's longest-standing source of confusion. (`/remember-bottom` re-orients.)
- **The literal string `ε₀ = 0`** may appear ONLY as a guard or fence forbidding it, or as a theorem where
  ε₀ is an argument. Never a bare assertion, never in conversation — even to deny it. Canary:
  `epsilon0_ne_zero`.
- **Standard mathematical term first**, ZP term after as a declared shorthand — never the reverse. This is
  the defense against the "ontology built on an equivocation" reading.
- **Verify an API exists before naming it in a plan.** Grep the Mathlib pin; a plan citing a lemma that
  does not exist in the pinned version is worse than no plan.
- **Never delete a Lean file a subagent produced**, even a failed experiment — say so in the brief.
- **NO SCRATCH FILES IN THE REPO.** Any probe, temp script, or measurement file goes in the session
  scratchpad directory, never under `ZeroParadox/` or anywhere else in the working tree. A reviewer that
  needs to measure something writes it to the scratchpad, runs it, and deletes it. **Measured
  2026-07-19:** a review agent left a `ZZTestOrd.lean` probe in the source tree (since deleted, so the
  path no longer exists) and it was committed — a scratch probe is now in the permanent history. Put this
  line in every subagent brief.
- **Reviews are READ-ONLY on the working tree.** A gate reads, measures, and reports; it does not modify
  repo files. The only writes a gate may make are its signal file and its findings note under
  `.claude-local/notes/`.
- **Engineer's Takes are Tim's voice.** Claude never drafts one. The only sanctioned assembly is
  restating Tim's own session statements as declaratives, grammar-cleaned, shown back for approval.
  **Fill the Take BEFORE running the review gates (Tim, 2026-07-20)** — it is public prose in the pushed
  file, so the reviews must cover it. Order: finish the work → insert Tim's Take (with approval) → run
  editorial/adversary/prior-art on the COMPLETE file → push. Gating first and adding the Take after
  leaves it unreviewed and (under the SHA-256-per-file signal scheme) stales every signal, forcing a
  needless re-run.

## Editorial Review Gate — Hard Rule

**Any commit touching document prose requires editorial review to have completed before the commit is made.** This applies to:

- Changes to any build script `body()`, `cbody()`, `sp()`, or box-helper string content
- Changes to README.md, GUIDE.md, RELEASES.md, or any `.md` file in the repo root (except `CLAUDE.md` — see the gate exemption above)
- Changes to any companion or formal document build script
- Changes to register.md

**The protocol:**
1. Before committing any of the above, run `/editorial-review` (pre-commit mode — no arguments needed; it reads `git diff --staged` automatically)
2. Wait for the editorial agent to return a verdict
3. If FAIL: resolve every item in the kill list before committing
4. If PASS: the agent writes `.claude-local/er_cleared.txt` recording the SHA-256 of each reviewed file (see the SHA-256-per-file scheme below) — proceed with the commit

Same-session self-review does not satisfy this requirement. `/editorial-review` spawns a fresh agent with no conversation history.

The pre-push hook validates `.claude-local/er_cleared.txt` and `.claude-local/ar_cleared.txt` (and `pa_cleared.txt` on a `.lean` trigger) using the **SHA-256-per-file scheme** (2026-07-20): each signal records the content SHA-256 of every file the review certified (line 1 = verdict record; lines 2+ = `<sha256>  <path>`), and it is valid iff (a) every recorded file still hashes to its recorded value and (b) every *reviewable* file in the push is covered by a recorded hash. Reviewable = changed files minus pure data/binary (`ssot.json`, PDFs, images, lockfiles), so a data-only commit no longer stales a review — that was the old HEAD-equality scheme's failure mode. If nothing reviewable changed, no signal is required. `--no-verify` should now be genuinely rare; if a signal is stale it is because a reviewed file actually changed (re-run the review) or a new reviewable file is uncovered.

## Adversary Review Gate — Hard Rule

**Any public-facing action requires adversary review to have completed before execution.** This is non-negotiable and applies to every action that puts content in front of an external reader:

- `git push` containing changes to prose in any tracked file (Lean source docstrings, build script `body()` calls, README.md, GUIDE.md, any companion script)
- Sending an email to any external party
- Posting or editing a GitHub Discussion body or follow-up comment
- Posting or editing a GitHub Issue
- Any other action that surfaces content outside this repository

**The protocol:**
1. Before executing any of the above, Claude must explicitly ask: "Adversary review complete for this content?"
2. Wait for Tim's confirmation before proceeding — do not self-assess whether review is needed
3. If review has not been run, offer to run `/adversary-review` on the relevant content first
4. If PASS: the agent writes `.claude-local/ar_cleared.txt` recording the SHA-256 of each reviewed file (see the SHA-256-per-file scheme below)
5. Only after explicit confirmation may the public-facing action execute

Same-session self-review does not satisfy this requirement. The review must be a separate adversarial context (spawned Agent with no conversation history).

**What triggered this rule:** Lean docstring and build script prose changes were pushed on 2026-05-20 before adversary review ran. The review subsequently found two additional precision errors in the already-committed content.

## Prior-Art Search — Trigger Conditions and Gate

The framework's value is its *delta* against prior art, so an uncited closest-prior-art reads as "unaware" — the crank-triage failure mode. Prior-art search is therefore a **gated control**, not an aspiration. It is enforced through the adversary-review gate's **synthesis-layer detection** (the same routing pattern as claim-status → `/claim-review`).

**Scope — synthesis/bridge layers only.** A trigger fires on content that unifies, connects, or identifies a structure across more than one field or framework (e.g. the diagonal-fixed-point keystone, ZP-P, ZP-G/H). It does **not** fire on theorem-backed layers whose central claim is a single named classical theorem the framework merely invokes (ZP-B / Ostrowski, ZP-L/M / Gentzen) — those are already anchored. *Caveat (the ZP-D lesson):* a theorem-backed layer can still carry a distinctive *construction* with its own prior art that the cited theorem does not cover — caught by trigger 5 below, not by synthesis-detection.

### ⚠ TRIGGER 0 — SEARCH BEFORE YOU BUILD. Hard rule, and it is the cheapest one here.

**If you can state the claim in one sentence of standard mathematical English, search for it
BEFORE writing Lean.** Not after. The post-hoc gate below still runs; this sits in front of it.

**Measured 2026-07-27 — three findings in a single day, every one of them searchable beforehand:**

| what was built | what already existed | cost of not looking |
|---|---|---|
| `notEL_unique` (non-terminating element of the final coalgebra of `1 + X` is unique) | **Escardó's `not-finite-is-∞'`** (TypeTopology) — and proved from function extensionality alone, where ours carries `Classical.choice` | a whole build, and a *purer* proof left on the table |
| `HasFirstStep` (a first step above the bottom, nothing between) | **Mathlib's `CovBy`**, over a weaker typeclass, plus `CovBy.unique_right` and `not_covBy` | a false `[ZP-CUSTOM]` registry entry, **and we missed `denselyOrdered_iff_forall_not_covBy` — a BICONDITIONAL stronger than the framework's own claim** |
| the Glauber one-bit probes | **one sentence** of Krapivsky-Redner-Ben-Naim p. 123; the premise of Hajek (1988); five lemmas already in Mathlib as `Real.sigmoid` | 256 lines reduced to 162, proof body to 6 lines; three claims retracted |

**The point is NOT embarrassment-avoidance. Searching first gets you MORE.** In those three cases
it would have handed us a stronger theorem (the density biconditional), a purer proof (Escardó's),
free derivative/analyticity/continuity lemmas (`Real.sigmoid`), and the standard NAME for a thing
described longhand ("critical slowing down").

**The three-step check, ~10 minutes:**
1. **Grep our own corpus.** *This was the cheapest miss and it happened three times in one day* —
   `NatListRegime.lean` already had the `1 + X` coalgebra, `Miniature.lean` already had
   `enat_fp_iff`, `State/ReversibleSpectrum.lean` already had `Reversible` (a third definition of
   detailed balance was written anyway). Not literature. A grep.
2. **Grep the pinned Mathlib** for the concept, not just the name you would have chosen.
3. **One literature search** if the object has a name (Glauber dynamics, coalgebra, covering
   relation). `.claude-local/papers/` FIRST — it is the downloaded-source library.

**⚠ AND WHEN YOU FETCH A SOURCE, FILE IT. The library only works in both directions.**
A **probe or scratch script** goes in the session scratchpad and is deleted. A **fetched SOURCE** is
the opposite: it goes in `.claude-local/papers/`, named `author_topic_year[_id].pdf`. Nothing said this
before, so every scout fetched, used, and abandoned — and the next one re-fetched or wrongly reported
the source unobtainable.
- **Measured 2026-08-02:** 19 PDFs were sitting abandoned across session scratchpads, **15 of them
  genuine and absent from the library** — including **Diaconescu 1975** (cited in five Lean files and
  the subject of its own ledger entry), **Barwise & Moss *Hypersets***, **Paulson's ZF final-coalgebra
  paper**, **Rutten & Turi**, **Hajek 1988** and **Krapivsky–Redner–Ben-Naim ch. 7** (both named in the
  Trigger-0 table above as prior art this project already missed once), and the **Buckingham /
  Castro–de Boer / Villaverde** sources cited by name in `CLAIMS.md`. Filing them took the library from
  55 to 70 files.
- **VALIDATE BEFORE FILING.** 4 of the 19 were correctly discarded: three unreadable failed fetches
  (a 12KB "Aczel", a 3KB "Glauber", a 2KB "Ramsey" — a tiny PDF is an error page, not a paper) and one
  ZP-E build artifact, which is not a source at all. Open it and check the page count and first page.
  A library with junk in it lies in the other direction.
- **Do NOT record a file count anywhere** — this file carried "55 files / 43 PDFs" until the day it
  went stale by 15. Measure: `Get-ChildItem .claude-local\papers -File | Measure-Object`.
- Carry both halves — *check it first* AND *file what you fetch* — into every scout brief.

**The exception, and it is real:** if you *cannot* yet state the claim in one sentence, building
is how you find the shape and searching returns noise. Build, then search before promoting. The
trigger is nameability, not a stopwatch — a rule of "never build first" would be wrong and would
stop real work.

⚠ **"Then search before promoting" is the half that gets skipped — measured 2026-08-08.** A
requirements-class degeneracy audit (a survey, correctly un-searchable in advance) produced a
**theorem**: the valuation axioms force an infinite carrier. The corpus grep run before the audit
covered the **class names** (`ValBridge`, `ValuationStructure`) and never the **claim** —
*one or infinitely many*, *no finite middle*, *orbit*, *periodic point*. `Order/OrbitDichotomy.lean`
already proved that shape and its own header **named the framework's scale map as the checkable
branch of it**; cross-references between the files, both directions, were zero. **When a survey turns
into a theorem, the prior-art clock restarts — the search that justified the investigation does not
cover the mathematics that came out of it.** (The delta was real, so the fix was a pointer, not a
revert: the trunk assumes `Function.Injective s`, which the class does not supply.)

**Standard framing, once found, is ADOPTED — not noted and worked around** (Tim, 2026-07-27:
*"anytime that we have official framing we need to make use of it"*). Keep the framework's own
label as the handle where one exists (the CC-2 / AX-B1 pattern: `HasFirstStep` stayed a name and
became `∃ a, bot ⋖ a`), and take the library's lemmas. **One caveat measured the same day:** check
purity before swapping a proof — adopting `CovBy.unique_right` pushed `firstStep_unique` from
`[propext]` to full choice, so the hand proof was kept and the standard name cited instead.

**Trigger conditions:**
1. **A new synthesis/bridge layer is created** — prior-art search before its first push. (Highest yield; every gap found in the 2026-06-22 arc originated at layer creation.)
2. **A synthesis layer's central/distinctive claim is revised or strengthened** — re-run for that claim.
3. **A layer is prepared for outreach or arXiv** — prior-art search is part of the pre-flight, beside the adversary pre-flight.
4. **Reactive:** an external reviewer asks "have you seen X?" — search, then add the result to the CLAIMS "Convergence with established work" table with attribution.
5. **A new `.lean` file, or a large net addition to one** — a substantial original *construction* is in-scope even if it is not a cross-field synthesis claim (the mechanical complement to synthesis-detection). This is what would have caught ZP-D's `T` (the van der Put / Kozyrev ball-indicator ONB), which the synthesis-only trigger missed.

**The mechanism (how it runs):**
- **Step 0 — grep our own corpus first.** Before any web search, `/prior-art-review` greps the repo + `.claude-local` (notes, **`papers/`**, `external/`, outreach) for an existing reference; much of this project's prior-art knowledge already lives there, so this prevents false-positive "gaps" — e.g. the Bruhat-Tits tree is already cited in `PadicTree.lean`, and a web-first sweep "rediscovered" it. **`.claude-local/papers/` is the downloaded-source library and is the FIRST place to look for a book or paper — check it before concluding a source cannot be obtained; and FILE any source you fetch into it (see the rule under Trigger 0 above).** **No file count is recorded — measure it.** This line carried "55 files, of which 43 are PDFs" (itself a 2026-07-30 correction of an earlier "55 PDFs" that miscounted HTML/txt captures), and on 2026-08-02 it went stale by 15 files at once. A figure quoted rather than regenerated is this project's most reliably recurring defect. Measured 2026-07-26: a scout spent a full search declaring Aczel's *Non-Well-Founded Sets* unobtainable (404s, dead mirrors, lending-restricted archive.org) while `.claude-local/papers/aczel_afa_manuscript.pdf` sat on disk — because this line listed `external/` and omitted `papers/`, and the brief inherited the omission. **Carry `papers/` into every scout brief explicitly.** Note also that scanned books here are OCR'd with spurious intra-word spaces ("depend ent choice s"), so **grep loosely** — a miss on a tight pattern is not evidence of absence.
- The **adversary-review** gate detects synthesis-layer content. If a distinctive cross-field claim lacks a specialist-branch citation (in the content or the CLAIMS Convergence ledger) and there is no `.claude-local/pa_cleared.txt` matching HEAD, it adds a kill-list item — `ar_cleared.txt` is withheld and the pre-push hook blocks. (Detection only; the adversary does not perform the search.)
- The **pre-push hook also checks `pa_cleared.txt` directly** when the push adds a new `.lean` file or a large net `.lean` addition (trigger 5: a new `.lean` file, or ≥50 net `.lean` lines in the push). This closes the library-duplication leak: a non-synthesis `.lean` re-proof of an existing library lemma (e.g. a `lawvere_fixedpoint` duplicating Mathlib's `Function.exists_fixed_point_of_surjective`) carries no synthesis claim for the adversary to detect, so the hook enforces prior-art directly. Synthesis prose still routes through the adversary path above; `.lean` constructions are now hook-gated independent of it. (Hooks live in `.git/`, not version-controlled — per-clone install; staged at `.claude-local/proposed_pre_push_hook.sh`.)
- **`/prior-art-review`** is the deep gate it routes to: a fresh-agent literature scout that states each distinctive synthesis claim in the target field's terms, searches for and **reads from source** the specialist branch, and either cites it (with the honest delta, credit pointing outward) or records "searched, none found." For a new or substantially-expanded `.lean` file the scope also includes a **library-duplication check** on the file's central/named results — a re-proof of an existing Mathlib lemma or a re-built known construction must cite the library/source version (bounded to named/central results, not every helper lemma). On PASS it writes `.claude-local/pa_cleared.txt`; the push clears once both adversary and prior-art-review are satisfied.
- Same-session self-review does not satisfy this. The review must be a separate scout context (spawned Agent with no conversation history).

**The record:** the CLAIMS "Convergence with established work" table is the public ledger of identified prior art; `.claude-local/notes/prior_art_*` notes hold the per-search findings and saved sources. Standing practice: memory `feedback_prior_art_search_baseline.md`.

## Guiding Principles (from Project Instructions)

- **Logical Rigor First:** The primary goal is logical consistency and rigor. 
- **Prose Role:** Use prose only to restate mathematics into accessible language. 
- **Ontology Focus:** Finalized documents must be structured as an ontology. 
- **Persistence:** All completed work must be committed back to the repository immediately to prevent data loss.

## Repository Nature

This is a **mathematical publication repository**, not a software project. There is no build system, test suite, or source code. The repository contains:

- PDF documents (the formal mathematical framework and illustrated companions)
- Markdown documentation (README.md, ABOUTME.md, this file)
- (superseded document versions are preserved in git history and per-release Zenodo snapshots; the `historical/` folder was retired in v3.0)
- A `scripts/` folder with the PDF build tooling (Claude-generated, public, included for transparency)

## Private Working Folder

A `.claude-local/` folder exists locally and is **gitignored** — it does not appear in the public repository. This is intentional. It serves as a private working space for the project's core collaborators during active development, before material is ready for public discourse. It contains:

- Reviewer feedback and correspondence (e.g. `feedback/`)
- In-progress build scripts and draft outputs
- Session notes and development artifacts

Transparency is a core value of this project. The existence of this private folder is acknowledged here precisely for that reason: readers of the public repo can see that private collaboration is occurring, understand its purpose, and know that the mathematical content and editorial decisions will be surfaced publicly as the work matures. Nothing in `.claude-local/` affects the formal mathematics — that lives entirely in the committed PDFs.

## Document Versioning Conventions

- Current documents live at the root with **flat (version-free) filenames**: `ZP-X_Title.pdf`
- Version numbers are tracked in `register.md` (Formal Version column) and in each PDF's title block — not in the filename
- Superseded versions are **not** archived to a folder (the `historical/` folder was retired in v3.0); the flat root PDF is overwritten in place, and git history + each release's Zenodo snapshot are the record
- README.md and GUIDE.md always link to the flat root filename

## GitHub Releases and Zenodo Snapshots

GitHub Releases trigger automatic Zenodo snapshots with permanent DOIs. `RELEASES.md` is the human-readable record of each release.

### Release naming

`v<major>.<minor>` - e.g. `v1.0`, `v1.1`, `v2.0`

### What triggers a release

- **Major version** (`v1.0 → v2.0`): a new formal layer added, or a theorem status changes (candidate → derived), or a significant structural revision to the framework
- **Minor version** (`v1.0 → v1.1`): a substantive reviewer feedback round addressed, or accumulated document/companion updates that represent a meaningful state of the framework

**Do not release on:** every individual PR. Releases should feel like milestones worth timestamping.

**Lean-only changes are an open question, not an automatic trigger (either way).** The release model is document-centric: `RELEASES.md` is built around a "Document versions" table, and the candidate→derived trigger above refers to *tracked, labeled* results in formal documents (carried in `register.md`), not to a placeholder proved only inside a `.lean` file. When a Lean milestone lands without accompanying formal prose (e.g. a conjecture proved only in Lean, no PDF document or companion moved), do not assume it warrants a release, and do not assume it doesn't - raise it as an explicit question for Tim. The two clean resolutions are: (a) bundle it into the next document release, or (b) write the result up as formal prose first, then release. Example: the wheel of fractions (§VIII conjecture → theorem, ZPJ_Wheel/ZPJ_WheelFrac) landed 2026-06-06 as a Lean-only change and was flagged, not auto-released.

### Release workflow

When Tim initiates a release: draft the `RELEASES.md` entry + `.zenodo.json` → PR → after merge, **run the Release-Readiness Gate (`check_release_ready.py <tag>` must exit 0) and confirm its judgment checklist** → draft the GitHub Release body → **wait for explicit approval** → execute:
```
gh release create <tag> --target main --title "<tag> - <title>" --notes-file ".claude-local\release_<tag>_body.md"
```
After release, confirm the Zenodo snapshot minted (query `https://zenodo.org/api/records/<conceptID>`). The README DOI badge is the **concept DOI** (`10.5281/zenodo.20060860`), which auto-resolves to the latest version — so **no per-release badge edit is needed** (confirmed v2.6, 2026-06-24). Only verify the snapshot exists; do not chase a badge update.

**Release-Readiness Gate — mandatory hard gate before drafting the release body / cutting any tag.** Run from the repo root:
```
python .claude-local/check_release_ready.py <tag>
```
It must **exit 0** before the release body is drafted. The script mechanically verifies the deterministic release preconditions and **exits 1 (NO-GO)** on any blocking failure: Engineer's Takes filled (no `TODO (Tim)` / `TODO: Engineer` / empty take section), build-script hash integrity vs `register.md`, the `LEAN_CUSTOM_REGISTRY` invariant (`### ` entries == `[ZP-CUSTOM]` tags), `.zenodo.json` valid JSON, no conflict markers in tracked files, a `## <tag>` entry present in `RELEASES.md`, and every README/GUIDE-linked PDF exists. It also prints WARN-level hygiene checks (register↔script VERSION, `scripts/` mirror currency, untracked root PDFs) and a **judgment checklist** of the non-mechanizable items (editorial/adversary/claim-review/prior-art ran on the PR; companion sync; major-vs-minor decision; release body approved). It **consolidates** the `.zenodo.json` and Engineer's-Take checks below (kept individually documented for context) and adds the rest. The gate cannot hook `gh release create` (no git event for tag creation), so enforcement is procedural: **the gate must exit 0 AND its judgment checklist must be confirmed before the release body is drafted.** Lives in `.claude-local/` (gitignored, like `check_hashes.py`; `check_*` dev tools are not mirrored to `scripts/`); reuses `check_hashes.py` for register parsing. Spec: `.claude-local/notes/release_readiness_gate_2026-06-24.md`. (Added 2026-06-24 after `LEAN_CUSTOM_REGISTRY` went 18 days stale undetected at the v2.6 threshold — the scattered-checks model let it slip.)

**`.zenodo.json` check — mandatory before every release:** Read `.zenodo.json` and verify the `description` field accurately reflects the current layer count and layer list. Update it in the same PR as `RELEASES.md` if anything is stale. Zenodo reads this file at release creation time; it cannot be updated retroactively via the repo (only via the Zenodo web UI).

**Engineer's Take check — mandatory before every release (hard gate):** Before cutting any release, grep the Lean sources for outstanding Engineer's Take placeholders — at minimum `TODO (Tim)` and `TODO: Engineer's Take` across **`ZeroParadox/**/*.lean`** (also scan for any `## Engineer's Take` heading followed immediately by an empty section). **The glob MUST be recursive.** This instruction previously read `ZeroParadox/*.lean`, which post-reorg matches only 3 files out of 187 — a manual check run that way would pass silently on an unfilled Take in any subdirectory. `check_release_ready.py` already uses the recursive form and is correct; only this prose was wrong (fixed 2026-07-19). Every ZP-X Lean file included in the release must have its Engineer's Take filled in Tim's own voice. **A release is BLOCKED until all are filled.** Claude never writes these — they must be Tim's own language (see the Engineer's Take convention) — so this gate catches the omission, it does not fill it. Surface the list of unfilled takes to Tim and wait for his prose. (Added 2026-06-11 after the four ZP-H functor takes plus ZP-L's were almost missed at the v2.4 threshold.)

**RELEASES.md format:** `## vX.Y - YYYY-MM-DD` header, then **Why this release** (one sentence), **What changed** (bullets), **Document versions at this release** (table), **Next threshold**. Match existing entries in RELEASES.md for exact formatting.

## register.md — Canonical Version Registry

`register.md` is the authoritative source for all current document version numbers, filenames, and companion versions. It is committed to the public repository and reachable from the main index via the Claims Ledger (`CLAIMS.md`, which README links to register.md), so it no longer carries an unlinked-transparency notice (removed 2026-06-21).

**Schema:** One row per formal document:
`| Document | Formal Version | Filename | Companion Version | Notes |`

**Rule: update register.md first.** On any version bump — before touching README.md, GUIDE.md, or build script docstrings — update register.md. README.md's Framework table and GUIDE.md's Reading Paths are then verified against it.

**On every version bump, in order:**
1. Update register.md (formal version, filename, companion version if changed)
2. Update README.md Framework table (verify against register.md)
3. Update GUIDE.md Reading Paths links (verify against register.md)
4. Update build script docstring
5. Archive old version per archiving convention

## Companion Document Versioning

Each formal ZP-X document has a paired illustrated companion (`ZP-X_Illustrated_Companion.pdf`). Companion PDFs overwrite in place - no versioned filename, no archiving (git history + Zenodo snapshots are the record). The current companion version lives only in the title block of the PDF and the docstring of its build script.

### Companion sync rule

**Whenever a formal document is updated, review its companion in the same session.** Ask:
- Does the companion describe any result whose label or status changed? (e.g., "Candidate Theorem" → "Theorem T-SNAP", CC-2 added, RP-2 added)
- Does the companion omit a new result a general reader would benefit from? (e.g., L-INF, a new lemma or design principle)
- Does the companion's key result box or closing summary still accurately reflect the framework state?

If yes to any of these, update the companion and bump its internal version number in the same commit as the formal document. Do not leave the companion behind.

### Bumping a companion version

When updating a companion, change:
1. The subtitle paragraph in `build()`: e.g., `'Information Theory | Version 1.4'` → `'Version 1.5'`
2. The docstring at the top of the build script

Companion version numbers are independent of formal version numbers. What matters is that the companion is not materially stale.

### Version numbers and changelogs in rendered PDF content (ALL PDFs)

**This rule applies to every PDF in the project — formal layers, companions, addenda — not just companions.** (Generalized 2026-06-13, Tim: version changelogs in rendered content should be "murdered by the style guide and review." Scope is **rendered PDF content only** — build-script docstrings and `register.md`/`RELEASES.md` are the changelog of record and are exempt; git history is the real changelog.)

**The document's OWN version must appear in exactly one place in rendered PDF content: the subtitle / tagline meta line** (`'... | Version ' + VERSION + ' | ...'`; formal-doc footers via `make_doc()` may also carry it). Nowhere else in rendered content — not in disclaimers, section headers, body prose, title-block notes, endnotes, or status/provenance tags.

**No self-version changelogs or provenance tags in rendered PDF content.** A title-block "note" or endnote narrating `"v1.1: Added X. v1.0: Initial release…"` is a violation — this was the standard formal-doc pattern (e.g. ZP-M) and is now retired. The title-block note must describe what the document *is*, not its version history. Violations include: `"New in v1.6"`, `"In v2.7, DA-1 was upgraded"`, `"End of ZP-X v1.0"`, `"Updated ZP-E v3.0 | …"`, and status/provenance tags such as `[unchanged from v1.0]`, `[new in v1.7]`, `[rebuilt in v1.1]`, `Relabelled in v1.2`, `Supersedes v1.4`. Strip them on discovery and bump the version.

**EXCEPTION — cross-document version citations are ALLOWED (Tim, 2026-06-14).** A reference to *another* document's version (e.g. `"T-SNAP derived in ZP-E v2.0"`, `"Closed in ZP-G v1.1"`) is a legitimate citation, not a self-changelog, and is **not** a violation. The rule targets a document's references to *its own* version history, not citations of where a result landed in a sibling layer.

**Editorial review enforces this as a kill** for any rendered mention of the document's OWN version beyond the single meta line, or any rendered self-version changelog/provenance tag. Cross-document version citations are exempt.

### Companion sync checklist

Run this whenever a formal document version changes:
- [ ] Key result box / closing summary still accurate
- [ ] Changed theorem or claim labels updated in plain language (e.g., "AX-1 is a Candidate Theorem" → "T-SNAP is a proven theorem")
- [ ] New results relevant to a general reader added with plain-language explanation
- [ ] Internal version string bumped if any changes were made
- [ ] Build script docstring updated to match

### Companion prose precision checklist

Apply this when drafting or reviewing any companion section that makes claims about mathematical structures, properties, or comparisons. The same errors can appear in formal document preambles and contextual sections — it does not apply to formal theorem statements, which are held to a separate standard via Lean verification.

**Category 1 — Precision errors:** Using the wrong technical term for the actual mathematical property being claimed. Common risk: describing a valuative property (e.g., v₂(0) = +∞) using topological vocabulary (e.g., "topologically isolated"), or using metric language for an algebraic property. Before using any technical term, verify it names the correct property in the correct sub-field.

**Category 2 — Invented terminology:** Using informal or invented phrases as if they were recognized mathematical concepts. Any non-standard term that sounds technical risks confusing readers who know the actual vocabulary. Use standard terminology or explicitly flag non-standard usage as informal/metaphorical.

**Category 3 — Directional ambiguity:** Claims where it is unclear whether the sentence is describing a property a structure has (and saying that's bad) or prescribing what a structure should have (and saying it falls short). Any sentence of the form "X is Y" near a comparison between two mathematical structures should make the normative/descriptive distinction explicit.

**Category 4 — Context-free structural claims:** Asserting something as universally true that is only true within the ZP framework. Claims about zero or ⊥ that are true in the ZP context may be false in most mathematical frameworks. Scope all such claims explicitly to the ZP setting.

**Category 5 — Scope overclaiming:** A statement implying a broader negative conclusion than intended. Universal quantifiers ("any domain," "every structure") applied to a ZP-specific limitation overstate the claim. Narrow the scope to what is actually proved.

## Vocabulary Reference Guide — Standing Update Rule

A vocabulary reference guide lives at `.claude-local/vocabulary_reference.md`. It is the authoritative list of:
- Terms to avoid or replace (technically loaded words used incorrectly, or invented ZP jargon)
- Terms requiring a plain-language gloss for non-specialist audiences
- ZP-internal vocabulary and how to describe it externally

**Standing rule:** Whenever a vocabulary problem is surfaced — by Dan, by an adversary review kill-list, or by any external reviewer — update `.claude-local/vocabulary_reference.md` in the same session before the session ends. Add a row to the Update Log with the date, source, and term. Do not leave vocabulary fixes as one-off edits without capturing the general rule.

This rule applies to both directions:
- A term flagged as wrong (e.g., "isolated," "membership status") → add to Section 1
- A term flagged as needing a gloss (e.g., "valuation," "clopen") → add or verify in Section 2

## Build Script Hash Integrity

`register.md` records a SHA-256 fingerprint (first 8 chars) of every formal and companion build script in the `formal:XXXXXXXX comp:XXXXXXXX` token embedded in each row's Notes field.

**Line endings are LF, enforced by `.gitattributes`.** Because the fingerprint is a hash of file *bytes*, line endings must be byte-stable across machines or the same script would hash differently (CRLF vs LF). `.gitattributes` declares `* text=auto eol=lf` (all text normalized to LF) and marks PDFs/images `binary` (never converted). Do not commit CRLF in tracked text files, and do not rely on `core.autocrlf` — the attributes override it. `check_hashes.py` hashes the active `.claude-local` scripts (LF); the `scripts/` mirror is the same content under the same LF policy. (Added 2026-06-21 after a CRLF/LF mismatch made the `scripts/` mirror hash differ from the active script for the same content.)

**Standing rule — any script change requires all four steps in the same commit:**
1. Make the change and bump the internal version number
2. Rebuild the PDF and archive the old version
3. Recompute the hash: `python -c "import hashlib; print(hashlib.sha256(open('.claude-local/build_X.py','rb').read()).hexdigest()[:8])"`
4. Update the hash token in `register.md`

**Session start check:** Run `python .claude-local/check_hashes.py` at the start of any session that will touch build scripts. A mismatch means a script was modified without completing the full four-step workflow — version bump and PDF rebuild are overdue.

A hash mismatch is not just a "rebuild needed" signal — it means the version bump step was skipped. Do not rebuild without incrementing the version number.

## PDF Build Standards

**Before building any PDF in this project** — formal layer, companion, or otherwise — read `.claude-local/PDF_Rendering_Standards.md`. It is the single authoritative source for font stack, glyph rendering, table cell formatting, HTML entities, subscript/superscript rules, and pre-build verification. All rules there apply to every PDF build without exception.

## Companion PDF Diagram Layout Standards

These rules apply to every `Drawing` object in every companion build script. Violations cause diagram content to overflow the declared bounding box and render over surrounding text — a recurring issue that has required multiple retroactive fixes.

**Now build-enforced (automatic).** `zp_utils` validates every `Drawing` in the story at `doc.build()` time — no per-function `validate_drawing()` call required. It **hard-fails the build** when content escapes its box (`max_y > dh` or `min_y < 0`, the only case that overlaps surrounding text), and prints a **margin warning** when content is inside the box but within the 10pt-top / 5pt-bottom safety margin. The rules below are still the design discipline (write diagrams that fit), but a forgotten check can no longer ship an escape. The bounds gate cannot see the *internal-collision* class (two elements overlapping inside the box, e.g. a caption over a node box); for that, every build prints a **diagram-page report** (`[diagram pages — eyeball for internal overlaps: …]`) naming the pages to visually check. Eyeball those pages on any diagram-touching build before commit.

**Known deferred tripwire (2026-06-19):** `build_zpc_companion.py`'s surprisal diagram has a pre-existing ~2pt bottom escape (the amber origin marker) — sub-perceptible, no visible overlap. Left unfixed by decision; the gate will block that companion's next rebuild until the diagram's `dh` is bumped a few points. Fix it then, bundled with whatever change prompts the rebuild.

### Diagram height and cy rules

**Rule 1 — Never derive `cy` from `dh` when the diagram contains fixed-size elements (circles, boxes, labels at fixed offsets).** `cy = dh * fraction` is only safe when all content scales with `dh`. If any element has a fixed radius `r` or a fixed offset, use a fixed numeric `cy` instead.

**Rule 2 — Verify bounds before committing.** After placing all elements, check:
- `max_y = max content y` must satisfy `max_y < dh - 10`
- `min_y = min content y` must satisfy `min_y > 5`

The minimum margin is 10 pts top and 5 pts bottom. If either fails, increase `dh` or adjust `cy`.

**Rule 3 — Common overflow sources to check explicitly:**
- Labels below circles: `cy - r - label_offset` — goes negative when `cy` is too small
- Labels above circles: `cy + r + label_offset` — exceeds `dh` when `cy` is too large  
- Internal title strings at `dh - N` — conflict with top circle labels when both are near the top
- Caption strings at fixed `y=10` inside the drawing — safe, but check nothing else sits at the same y

**Rule 4 — Internal title strings are usually redundant.** Diagrams that have both a title string inside the `Drawing` and a `ccaption()` below it should drop the internal title. It adds clutter and occupies the same crowded top zone as circle labels.

### Pre-build checklist for new diagrams

- [ ] `cy` is a fixed value, not `dh * fraction` (unless all elements scale with `dh`)
- [ ] Calculated `max_y < dh - 10` and `min_y > 5` for all content
- [ ] No internal title string that duplicates the caption
- [ ] `dh` expressed in inches with comment: `# N * 72 = M pts; content top = X, content bottom = Y`

## README.md Link Restrictions

The following files exist in the repository but **must not be linked from README.md or GUIDE.md** until the conditions below are met:

| File | Reason | Condition to lift restriction |
|------|--------|-------------------------------|
| `ZP_Gen2_Applications.pdf` | Speculative applications document — depends on Gen 1 being formally complete and bridge documents written. Premature to surface publicly in the index. | All Gen 1 layers (ZP-A through ZP-H) fully tightened; thermodynamic bridge and OQ-E2 resolved; explicit decision by Tim to promote. |
| `ABOUTME.md` | Not ready for prominent public linking from the main index. | Explicit decision by Tim to promote. |

Do not add links to these files in README.md or GUIDE.md under any circumstances without explicit instruction. They may exist in the repo and be committed — they just must not appear in either index.

## scripts/ Folder — Keeping It Current

The `scripts/` folder is a public transparency copy of the active build scripts from `.claude-local/`. It must be kept current: whenever a build script in `.claude-local/` produces a newly committed PDF, copy the script to `scripts/` as part of the same commit.

**Rule:** After committing a new or updated PDF on the `illustrated` branch, copy the corresponding build script:
```
Copy-Item .claude-local\build_X.py scripts\build_X.py
```
Then stage and include it in the commit (or as a follow-up commit on the same branch).

If a script is new (not yet in `scripts/`), add a row for it to `scripts/README.md` at the same time.

The `scripts/` folder is intentionally not a runnable package — the README there sets that expectation explicitly. The goal is source visibility, not distribution.

## Lean↔PDF Consistency — AI-Assisted Workflow

There is no automated tooling that verifies theorem status labels in PDF build scripts (e.g. "Status: DERIVED", "Candidate Theorem") match the actual Lean proof state. This is a known gap.

It is closed by the Claude-assisted session workflow instead. At every session where a Lean proof changes status or a new result is added, Claude cross-checks the corresponding PDF script and companion document as part of the same work. The companion sync checklist and README sync triggers (above) formalize this discipline.

This is a deliberate choice: the mapping between Lean theorem names and PDF prose descriptions is not machine-parseable without a maintained lookup table that would itself require discipline to keep current. The AI workflow catches the same class of errors more flexibly, with lower maintenance overhead, at the project's current scale.

If the framework grows significantly or external contributors join, a lightweight parseable-marker convention (`-- LEAN_STATUS: DERIVED` in Lean files, grepped against PDF scripts) would be worth adding. For now, the session discipline is the mechanism.

**Lean encoding descriptions can also go stale.** The gap above covers theorem *status* labels. A separate gap: prose descriptions of Lean *encodings* (type names, constructor names, how a concept is represented in code) can drift when the Lean source is refactored. Before stating any Lean encoding in a PDF, companion, README, or correspondence — verify it against the actual source file. Do not rely on memory or prior documentation. Example: `Fin 2` was replaced by `OntologicalStates` in ZPB.lean; stale references persisted in README.md, CLAUDE.md, and build scripts until caught by a reviewer question in May 2026.

### File-Reference Citation Convention (standing rule — Tim 2026-07-08, post-reorg)

References to Lean **files** in reviewer-facing / checkable surfaces must carry the **full repository path** (`ZeroParadox/<Domain>/<Name>.lean`), never a bare basename. A full path is grep-verifiable against the filesystem — it resolves or it does not — so a move/rename fails **loud**; a bare basename fails **silent** (plausible but pointing nowhere), which is exactly the stale-citation class the 2026-07-08 reorg sweep had to hunt down. For a "check it yourself" repo, loud is the point.

By reference kind and surface:
- **Declaration names** (`t_snap_derived`, `mc1_correspondence`): keep **bare** — a decl name is globally unique in the codebase and self-locating via `#print axioms ZeroParadox.<name>`. Never prefix a decl with a path or a (dead) per-layer namespace.
- **File references in checkable surfaces** — CLAIMS.md, BOTTOMELEMENT.md, README/GUIDE, and each formal document's "Lean source" box/footer: **full path**, as a markdown link href where the medium supports it. The markdown ledgers already do this; keep it uniform.
- **File references in flowing general-reader companion prose**: a bare basename is acceptable where a full path would clutter the sentence for a non-programmer — the checkable surfaces carry the path and the file is one grep away.

**Rollout is additive, not a big-bang rewrite.** Every new or edited reference uses a full path immediately. Existing formal-doc source boxes upgrade to full paths **as each document is next rebuilt** (the same as-touched model as the companion-sync and vocabulary conventions — do not burn a rebuild round retrofitting). The authoritative old→new file map is `ssot.json` (`new.file`).

**Enforcement:** a `check_paths.py`-style resolver (the one used in the 2026-07-08 sweep, in the scratch/`.claude-local` tooling) verifies every repo-relative file reference in tracked markdown resolves against the filesystem. Run it before any doc-touching commit; it should become a pre-push/CI check so a future reorg cannot silently rot the citation layer again.

## Transparency Notices on Unlinked Public Documents

Any file that is committed to the public repository but intentionally unlinked from both README.md and GUIDE.md **must carry a transparency notice** explaining its status. This is a standing policy — apply it whenever a new unlinked file is added or discovered.

**For Markdown files:** Add a blockquote at the very top of the file:
```
> **A note on transparency:** This file lives in the public repository but is intentionally unlinked from the main project index. [One sentence on why — e.g. speculative content, development artifact, etc.] The main entry point for the Zero Paradox is the [Formal Index](README.md).
```

**For PDF files:** Add an amber callout box as the first element in the document (before the title block), using the `callout(text, bg=AMBER_LITE, border=AMBER)` helper in the build script. Wording should follow the same pattern: explain the document is unlinked, why, and direct the reader to the README.

**If no build script exists for an unlinked PDF:** it is almost always a superseded development artifact - remove it from the root (git history preserves it) rather than leave it unnoticed.

## Development Environment

This project runs on **Windows 11**. Shell commands must use PowerShell syntax, not Unix/Bash.

- **File discovery:** Use the `Glob` tool — never `find` (hangs on this system) or `ls`
- **Shell commands:** Use the `PowerShell` tool — never `Bash` with Unix-style commands
- **Never prepend `cd`:** The working directory is always `C:\Workspace\ZeroParadox` at session start. 
- **Never prepend `cd C:\Workspace\ZeroParadox;` or `Set-Location` to any command — doing so creates command strings that don't match the allowlist and triggers unnecessary permission prompts.
- **File verification:** Use `Get-ChildItem *.pdf` not `ls *.pdf`
- **File moves:** Use `Move-Item` not `mv`
- **Path separators:** Backslash in PowerShell (`C:\Workspace\ZeroParadox`), forward slash in Lean/lake config

## README.md and GUIDE.md Maintenance

The project index is split across two files. README.md is the formal index (for mathematicians and reviewers). GUIDE.md is the general reader hub (plain language, companions, reading paths). Both are public.

### README.md and GUIDE.md Document Structure

Preserve the existing section order in both files. Do not add top-level sections, reorder sections, or remove terminal sections (License, Citation, Contact, Purpose in README.md; footer pointer in GUIDE.md) without agreement. README.md is the formal index for mathematicians; GUIDE.md is the general reader hub. Both must have a cross-pointer to the other near the top.

### Formatting Standards

**File links:**
- Display text uses clean names — no file extensions, no version numbers
  - Correct: `[ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_2.pdf)`
  - Wrong: `[ZP-A Lattice Algebra v1.2.pdf](...)`
- Link targets always point to the current (non-suffixed) version

**Text:**
- Use regular hyphens (`-`), not em dashes (`—`); mathematical arrows (`→`) are fine

**Tables:**
- Consistent column alignment; meaningful headers (File, Document, Version, Contents)
- Version numbers go in the Version column only, not in display text

### Validation Checklist (both files)

Before committing any README.md or GUIDE.md update:
- [ ] All linked files exist (verify with `Glob` tool, pattern `*.pdf`)
- [ ] No file extensions in display text; no version numbers in display text
- [ ] No em dashes — regular hyphens only
- [ ] README.md: Axiomatic Commitments current (AX-1 is T-SNAP, not an axiom); Question Register reflects actual status
- [ ] GUIDE.md: Reading Paths version numbers match register.md; "What This Is Not" section present
- [ ] Cross-pointer to the other file present near top of each

### Document Sync Requirements — Triggers and Checklist

Certain changes require both README.md and GUIDE.md to be audited for consistency. Apply this checklist whenever any of the following occur:

**Triggers:**
- A document is versioned up (e.g. ZP-A v1.3 → v1.4)
- An open question is closed (in any document)
- A claim's status changes (axiom → theorem, candidate → derived, etc.)
- A new document is added or archived

**On each trigger, verify in README.md:**
1. **Framework table** — version number matches the current file in the root and matches register.md
2. **Question Register** — every OQ/item that changed status is updated; newly closed items are added if missing
3. **Document descriptions** — any "Candidate Theorem", "Open", or status language in the Framework table description column still accurately reflects the document's current state

**On each trigger, verify in GUIDE.md:**
1. **Reading Paths links** — all version numbers in Reading Paths match register.md (and therefore the Framework table in README.md)
2. **Companion table** — if a companion was updated, its row reflects current diagram list
3. **Companion staleness note** — still accurate; update or remove if companions are brought current

**Known pattern to watch:** Version numbers now appear in three places: register.md (canonical), README.md Framework table, and GUIDE.md Reading Paths. Updating any one does not update the others. Always update register.md first, then propagate to README.md and GUIDE.md in the same session. Stale reading path version numbers have caused errors before.

### Common Updates

**Adding a new formal document:**
1. Add to the Formal Framework Documents table in README.md
2. Add a companion row to the Illustrated Companion Documents table in GUIDE.md (if companion exists)
3. Add to the Mathematician reading path in GUIDE.md
4. Use clean display name (no extension, no version) in both files
5. Link to the current version (no `-1`, `-2` suffix)
6. Put version number in the Version column only
7. Verify file exists with `Glob` before committing

## Superseding Document Versions

The `historical/` folder was **retired in v3.0**. Superseded versions are preserved by two records more
complete and authoritative than a hand-maintained archive: **git history** (every prior PDF stays in the
commit record) and each release's **Zenodo DOI snapshot** (the full repo - including the then-current root
PDFs - captured at a permanent, browsable DOI). The archive folder had drifted a month out of date; these
do not. Do NOT recreate `historical/`, and do NOT rewrite git history to purge old binaries (SHA-pinned
permalinks and DOI-referenced commits depend on it).

When a document is superseded (cosmetic **or** substantive), overwrite the flat root PDF in place:
1. Rebuild the new version into the flat root name `ZP-X_Title.pdf` (overwrite; do **not** create a versioned copy or a `historical/` entry).
2. Update `register.md` (version number + script hash).
3. Update the version in README.md's Framework table and GUIDE.md Reading Paths.

The prior version is recoverable from git (`git show <commit>:ZP-X_Title.pdf`) and lives permanently in the Zenodo snapshot of the release that last carried it.

## Theorem/Proposition/Lemma Naming Convention

All formal ZP documents use the following hierarchy for naming results. Apply this consistently when drafting or editing any formal layer:

- **Theorem**: The primary result of a section — of major significance for the framework. Reserve for results that drive the dependency chain or that are the central claim of a layer (e.g., T3 Monotonicity, T-SNAP).
- **Proposition**: A derived result that is rigorously proved but subsidiary to the main theorems — true and important, but not the headline claim (e.g., T1 partial order, T2 clopen balls).
- **Lemma**: A technical helper result used as a stepping stone toward proving another result (e.g., L-RUN, T2 global minimum).
- **Corollary**: A result that follows immediately from a theorem, proposition, or lemma with no substantial additional work (e.g., C1, C2, C3, T1b). Mark with "Corollary" label.
- **Conditional Claim (CC)**: A result that holds only given an explicit modelling commitment not derivable from the axioms (e.g., CC-1: S₀ = ⊥).
- **Design Principle (DP)**: A design commitment — well-motivated and explicit — that is chosen rather than derived (e.g., DP-1: orthogonality).
- **Remark (R)**: An observation providing context or clarification; does not require proof.

When assigning a label, ask: "Is this result the central claim of its section, or is it infrastructure for something else?" Central claims are Theorems; infrastructure is Propositions or Lemmas.

### Readable Name Convention — CC-2 is "the Quine atom" (framework-wide, additive)

**Standing rule (Tim, 2026-06-09).** CC-2 (⊥ = {⊥}, the self-containing bottom) is the conceptual keystone of the framework — it is what forces ZF+AFA, makes ⊥ immune to external description, and is the single contact point between ZFC+Foundation and ZF+AFA. The bare label "CC-2" undersells it on two counts: it reads as a minor sequence code, and the "CC = Conditional Claim" prefix is now **stale** — CC-2 was upgraded to a Forced Metatheoretic Commitment (closed via ZP-J T-EXEC), so it is no longer a conditional claim. This is the same situation AX-1 was in before it became T-SNAP.

**The convention — ADDITIVE, never eliminative:**
- Present CC-2 with the readable name **"the Quine atom."** This is a recognized set-theory term (Quine, Aczel) — it carries real gravity and a literature anchor, and it is NOT ZP-invented jargon (avoid inventing a ZP-branded name — that would undo the de-jargoning work).
- **Keep "CC-2" as the formal handle and note it alongside** — e.g., "the Quine atom (CC-2)" on first/significant mention. Do NOT remove or rename the CC-2 identifier anywhere; every existing cross-reference stays valid.
- Gloss once per document as "the self-containing bottom, ⊥ = {⊥}."
- **⚠ SCOPE THE GLOSS — BANKED 2026-08-01 (Tim), NOT YET ROLLED OUT.** `⊥ = {⊥}` is well-formed and
  true **in the ZF+AFA metatheory** — that is anti-foundation's actual content and Aczel's Quine atom
  is a real object, so **do NOT retire it** (a flat retirement would deny a true theorem of a real set
  theory: the `snap_is_frameflip` over-correction pattern). But asserted of the **Lean carrier** it is
  a **cross-type `=`** — `bot : L` against `{bot} : Set L` — which is on this file's bedrock-violation
  list. **Carrier-level statements take the INSTANCE-OF-FAMILY form**, which the corpus already
  proves: `IsQuineAtom q := selfMem q ∧ ∀ x, selfMem x → x = q` (the family predicate),
  `da1_closed_concrete : IsQuineAtom (bot : MachinePhase)` (⊥ as an instance), and
  `selfMem_eq_singleton_bot : {x | selfMemDerived x} = {bot}` (a `Set L` equality, `[propext,
  Quot.sound]`). This is the **QuineHost pattern** — never "⊥ *is* {⊥}", always "here are the
  requirements, and ⊥ is a witness meeting them."
  - **Why it was missed, and it is a measurement error worth copying the lesson from.** The rollout
    note below says *"Lean is clean (CC-2 is never a Lean identifier — 0 occurrences)"*. True of the
    **label** and false of the **claim**: `ZeroParadox/Algebra/Wheel.lean` asserts the bare equation
    many times. **Grep the CLAIM, not the name** — the same rule this file states for
    kill-propagation, missed here at the measurement step. **No count and no line numbers are
    recorded here on purpose**: the figure once said "ten times" with ten line numbers, and both went
    stale as the file was edited. Measure it.
  - **⚠ AND THE ROLLOUT IS NOT A SWEEP — most occurrences are CORRECT.** All were re-read
    individually 2026-08-03: the governing scope note, the correction record, and every site that is
    explicitly ZF+AFA-scoped or hedged as a conjectured counterpart is **right as written**, because
    `⊥ = {⊥}` is a true theorem of a real set theory. Only a **carrier-level consequence** claim is a
    defect. Two have been found and fixed, both the same modality (`forced`, then `structurally
    requires`), and the second was left standing by the pass that fixed the first — which had
    recorded itself as fixing "the one" occurrence.
  - **Provenance, because it is easy to misremember (it was, this session):** the 2026-07-14 ratification
    retired **MC-1**'s identity and cites CC-2 only as the precedent for *keeping a label*. **CC-2's own
    identity was never reviewed.** And the two defects are NOT the same: MC-1's was **ill-typed**
    (cross-category, never a proposition); CC-2's is **well-typed in the metatheory and cross-type in
    the carrier**. Scope it; do not retire it.
- **Do not overclaim status.** It remains a Forced Metatheoretic Commitment, not a Lean theorem. The structural self-application fixed point is Lean-proved (ZP-J T-EXEC); the literal set-membership ⊥ ∈ ⊥ is metatheoretic (lives in the ZF+AFA framing, not the Lean kernel). The readable name conveys significance, not proof-status.

**Rollout (phased, not a 12-PDF marathon):**
- Reader-facing surfaces first: README.md, GUIDE.md, register.md.
- Then apply to each formal document/companion **as it is next revised** (the readable name leads CC-2's introduction). Footprint as of 2026-06-09: 12 build scripts carry CC-2 (build_zpe.py 27, build_zpa.py 13, build_zpc.py 8, etc.); Lean is clean (CC-2 is never a Lean identifier — 0 occurrences).
- **Do not touch** RELEASES.md (release record - never rewrite history).

### The keystone concept — "the diagonal fixed point" (confirmed name)

**Standing rule (Tim, 2026-06-10).** The Quine atom (CC-2) is only the *set-theoretic face* of the
framework's actual keystone: **⊥ is the same self-referential fixed point in every framework, and the
floor of each structure is its point of self-reference** (the Gödel inversion — self-reference located
at the floor, not the ceiling). The confirmed readable name for this keystone is **"the diagonal fixed
point."** This language has recurred across many sessions; it is the real central concept.

- The faces of the one diagonal fixed point: the Quine atom (set theory, CC-2), the Kleene quine
  (computability, ZP-K), v₂(0)=∞ (valuation, ZP-B), the unique fixed point of `selfApp`
  (ZP-J `AbstractSelfApp`), unbounded surprisal / no external description (ZP-C), the categorical
  initial object (ZP-G). MC-1 (the bottom family) is what identifies them as kin.
- **Name it to evoke the recognized phenomenon, do NOT claim the unification as proved.** "Diagonal"
  anchors it to the diagonal argument and Lawvere's fixed-point theorem (the recognized home for
  self-referential fixed points across Russell / Quine / Kleene / Gödel / Tarski / Cantor). What ZP has
  *formalized*: `AbstractSelfApp` + instances, T-COMP (Quine atom = Kleene fixed point = ⊥), ZP-M
  (Kleene quine ∧ ε₀ co-witnessed). That ZP's keystone *is* a manifestation of Lawvere's theorem is a
  CONNECTION / conjecture, not a ZP result — keep that fence.
- Full articulation, faces, and the formal-vs-conjectural split:
  `.claude-local/notes/keystone_self_referential_fixed_point_2026-06-10.md`.

### MC-1 status convention — RETIRED as a commitment; MC-1 = the bottom family (rolled out 2026-07-15)

**Standing rule (Tim, ratified 2026-07-14, rolled out 2026-07-15).** MC-1 no longer names a "modeling
commitment" to one object; it names the **bottom family**. The "MC = Modeling Commitment" prefix is stale
(the same arc as AX-1→T-SNAP and CC-2→FMC). The earlier "correspondence derived / identity a commitment"
split is superseded:

- **Correspondence half — now formally realized.** Each domain bottom is the categorical bottom
  (limit or initial object) of its own *real* Mathlib category: F_B `fB_functor : ℕᵒᵖ ⥤ TopCat`
  (⊥ = inverse limit `⋂ B(0,2⁻ⁿ) = {0}`), F_D `fD_functor : ℕ ⥤ ModuleCat ℂ` (⊥ = initial object
  `StateSpace 0`), F_C `fC_functor : ℕ ⥤ KleisliCat PMF` (⊥ = initial object `Fin 0`, with
  `fC_no_return` = AX-G2 as a theorem). Bundled witness: `mc1_correspondence` (`MC1Bridge.lean`).
  So the bare label "MC = Modeling Commitment" now **undersells** this half.
- **The family — membership proved.** Each domain's bottom satisfies a shared list of criteria (the slots
  in BOTTOMELEMENT); per-domain membership is proved, the choice of criteria a design principle.
- **Identity half — RETIRED as ill-typed.** That the four bottoms are *numerically one object* across
  distinct categories is NOT a commitment the framework holds — `x = y` across distinct categories is not a
  well-formed proposition, so it was never a claim. The members are provably distinct (the walls); the only
  oneness is the shared *shape* (the diagonal fixed point), apophatic, never a formal identity.

**The convention (ADDITIVE, never eliminative):**
- Keep **"MC-1"** as the formal handle everywhere; it now points at the **bottom family** (CC-2 precedent:
  keep the label, retire the framing). Do not rename it; `mc1_correspondence` is unchanged. **Never call the
  cross-category identity a "modeling commitment," "offered," or "one object we commit to"** — it is retired
  as ill-typed. Present the split: membership PROVED, criteria a design principle, identity RETIRED, members
  provably distinct.
- **No new readable name for MC-1.** Unlike CC-2 (which *is* an object = the Quine atom), MC-1 is the
  *identification*; its underlying object already has the confirmed readable name
  [[project_diagonal_fixed_point]] ("the diagonal fixed point"). Coining an MC-branded name would be
  the ZP-invented jargon the CC-2 convention warns against — do not.
- **Do not overclaim.** The real categories are not `ZPCategory` instances (they have terminal
  objects), so ⊥ is the *limit* in `TopCat` and the *initial object* in the other two; state that
  distinction honestly. The cross-category identity is never claimed as proved.
- Canonical definition lives in **BOTTOMELEMENT's opening** ("The family - MC-1"); everything references
  there (draft MC1.md folded in + archived to `.claude-local/notes/` 2026-07-15).
- **Rollout DONE (2026-07-15):** README, CLAIMS, SNAP + BOTTOMELEMENT via their generators. Do not touch RELEASES.md.

## GitHub Issues — Transparency and Engagement Policy

The Zero Paradox project treats GitHub Issues as a public transparency mechanism, consistent with the project's core transparency commitment. Issues are not just a bug tracker — they are the public record of what is open, contested, or unresolved in the framework.

### When to check

- At the start of any session where a PR is being created or merged
- At the start of any session where outreach responses are being processed
- Any time Tim asks about external engagement or project status

### When to file a public issue

- Framework open questions that are genuinely unresolved and would benefit from external input (e.g. OQ-E2 cardinality question, AFA/CH tractability)
- Substantive technical questions that arose in review and were not closed within the session
- Questions where the framework explicitly flags something as open and outside the authors' expertise

### When NOT to file

- Anything sourced from private correspondence (reviewer feedback, outreach responses, academic group correspondence)
- Reviewer identity or feedback details
- Outreach strategy, sending schedules, or draft emails
- Editorial or prose decisions
- Anything that belongs in `.claude-local/`

### Issue framing standard

Public issues should read as genuine open questions to the mathematical community — not as requests for validation. Frame them as specific, honest about uncertainty, and standalone without requiring knowledge of the full framework.

### Identifier tracking — standing requirement

Every outreach item must have its external identifier recorded in `.claude-local/outreach/tracker.md` at the time it is created or sent. No exceptions.

**What counts as an identifier:**
- GitHub Discussion: `#N` (e.g. `#77`)
- GitHub Issue: `#N`
- MathOverflow question: full URL
- Email thread: date sent + recipient (email threads have no stable ID — date + recipient is the key)
- Zulip post: stream + topic slug
- arXiv submission: arXiv ID

**When to record it:** At the moment the item is created or sent — not after the fact. If an identifier is missing from the tracker, add it before doing any other work in that outreach session.

---

## Framework Structure (for context)

The Zero Paradox is a multi-layer mathematical ontology proving the Binary Snap (⊥ → ε₀) as a theorem. The dependency order of the formal layers is:

**ZP-A** (lattice algebra) → **ZP-B** (p-adic topology) → **ZP-C** (information theory) → **ZP-D** (state layer) → **ZP-E** (DA-1/T-SNAP derivation)

**ZP-G** (category theory) → **ZP-H** (categorical bridge) — self-contained; depends on ZP-E conceptually but not formally.

Each formal document has a paired illustrated companion for general readers. AX-G1 and AX-G2 are the two structural commitments of ZP-G's categorical layer. Neither is a novel commitment: AX-G1 is grounded in ZP-A's bottom element ⊥; AX-G2 follows from ZP-A antisymmetry and ZP-B C3 (topological irreversibility). ZP-G is self-contained by design and states them explicitly within that layer. AX-B1 (binary/discrete existence) is the framework's **one substantive modeling commitment** (discrete Boolean existence, not a continuum of partial states) — do NOT call it "directly verifiable / not a novel commitment" (reclassified 2026-07-15): the `decide` proof (`ax_b1_distinct`) only checks the two states are distinct *given* the two-element type, not the choice of a discrete alphabet over a continuum. The ZP-C forcing lemmas (`pmf_subsingleton_isPure` / `binaryState_exhaustive`, `Information/Surprisal.lean`) discharge the no-half-state worry (leaving ⊥ needs a second outcome) but force only the ≥2-outcome lower bound; the residual substantive commitment is that the outcome space is DISCRETE, not a continuum - which those lemmas do not eliminate and which the reals lack (the snap fails there, `f_snap_impossible`). See the CLAIMS AX-B1 row. AX-1 (Binary Snap Causality) is now Theorem T-SNAP, derived in ZP-E — do not refer to it as an axiom.

## Four-Fingerprint Scan — Decision Log Requirement

When a four-fingerprint scan is conducted (see memory: `feedback_reader_orientation.md`), the session notes file in `.claude-local/notes/` must be updated before the session ends with:

1. **Each item reviewed** — the finding, the decision (FIXED / NO FIX / PENDING), and the version bump if fixed.
2. **Rationale for no-fix decisions** — e.g., "already addressed in vX.Y", "standard result in the relevant literature", "Lean scope already disclosed."
3. **Any technique notes** — e.g., "read the Lean file before fixing to confirm the actual proof argument."

This log is the authoritative record of what has been reviewed and why. Future sessions must read it before starting a new scan pass to avoid re-reviewing already-settled items.

**File convention:** `.claude-local/notes/framing_scan_YYYY-MM-DD.md` — one file per scan pass, named by the date the scan was run. The decision log lives at the bottom of that file under a `## Decision Log` header.

**Standing rule:** A scan pass is not complete until all reviewed items have a decision recorded. "PENDING" is a valid decision for items deferred to a future session.

## Communication Quality Feedback

During working sessions, apply the Communication Quality Rubric to evaluate Tim's statements about the framework in real time. Flag anything scoring **7 or below** on the composite scale (35% terminological accuracy, 35% structural accuracy, 15% consistency, 15% clarity). The full rubric with scoring tables and calibration notes lives at `.claude-local/communication_quality_rubric.md`. Key terms requiring extra care: ⊥ (three-way identification), T-SNAP (theorem, not axiom), DA-1 (derived proposition, conditional on DP-2), DP-2 (grounded in D7 — not freely chosen), CC-1/CC-2 (both now derived via ZP-J, not freestanding commitments).

## Session Handoff File

`.claude-local/handoff.md` is the standardized session state file. At the start of every session, read it first. At the end of every session (or before a planned context switch), overwrite it with the current state. It has **two parts, in order**: first, **keeping the conversation thread alive** — the live orientation a fresh session needs to resume mid-thought rather than cold-start; then the **factual ledger** — what was just done, the immediate next action, and anything deferred. The thread leads, the ledger follows; the components, structure, and rationale of the thread part are defined privately (memory `feedback_handoff_thread_first`). Always use this exact filename — one file, always current, always overwritten.

## Development mode — LOAD THE SECTION BEFORE YOU WORK. (Tim, 2026-07-31.)

**Before fresh mathematical development, read the whole relevant subsystem. Do not start from
targeted search.** This is scoped to *development*; error-sweeps have their own discipline and a
different unit (see below).

```
python .claude-local/where.py "<Tim's phrasing, verbatim>"     # -> ranked folders + token cost
python .claude-local/where.py --files "<phrase>"               # + the file list
python .claude-local/where.py --spine                          # what the always-load spine costs
```

Then load: **the ~50k spine** (the five `#check`-only indexes — `BottomCannotBe`, `SnapCannotBe`,
`Epsilon0CannotBe`, `DiagonalFixedPoint`, `ChoiceCannotBe` — plus `MANIFEST.md`, `CLAIMS.md`,
`BOTTOMELEMENT.md`, `SNAP.md`) **plus the one or two folders it names.** Most subfolders are 5k–66k
tokens; the largest, `Valuation/`, is ~123k. Total lands at 80k–170k, comfortably resident.

**Why, and it is not about catching errors.** Every real finding of 2026-07-31 came from **colliding
two facts** — `selfApp` fixes ⊥ *and* `α ↦ ω^α` does not; ⊥'s down-set is empty *and* R1 forbids
subtraction; `nfp` is seed-independent *and* the corpus says "⊥ the seed". **You cannot collide facts
you are fetching one at a time.** Targeted search returns the fact you asked for and nothing adjacent,
which is precisely what a collision needs.

**Two honest limits.** (1) `where.py` scores term distinctiveness — it produces a *shortlist*, not an
answer, and on one of four test queries the right folder ranked third. Load two or three. (2) It
**cannot** route a genuinely new concept with no corpus vocabulary; fall back to `--spine`.

**Tim's Engineer's Takes are the bridge, and `where.py` reports them.** The Lean body says `cx`,
`member`, `infinitude`; Tim says *"bottom itself is infinitely complex."* The Takes are the only
corpus written in the register a question arrives in, they are attached to the file they describe, and
**all 146 together are ~16k tokens.** Measured 2026-07-31: on four separate questions the answering
Take was found *after* the work, never before.

**Not this, for error-sweeps.** A claim-sweep's unit is the **rendered PDF text**, never the source —
a claim survived four vocabulary changes and one split across two Python string literals. See
`vocabulary_reference.md`.

## The open-defect ledger — `.claude-local/DEFECTS.md`. Read it before choosing what to work on.

**A defect's home is this ledger.** Not a note, not a gate-findings archive, not a line in the handoff.
(Opened 2026-08-01, Tim.)

**Why it exists, and it is a gap this file created.** The § below correctly says *"if a finding is a
DEFECT, its home is a gate finding or a fix, never a note that cannot know when it stops being true."*
But the 2026-08-01 notes triage sorted 767 notes into `active` / `future-research` /
`archive{gate-findings, resolved, superseded}` — and **none of those is "open defect."** So the rule
forbade the wrong home without providing a right one, and defects scattered into gate-findings
archives that this same file says to *"write, never expect to read."* Tim's observation on reviewing the
triage: the classification should have been there from the start.

**The standing rule it serves: NO RELEASE IS CUT WHILE THE LEDGER IS NON-EMPTY.** A GitHub Release
mints a permanent Zenodo DOI; four already carry latent flaws that cannot be withdrawn. A defect fixed
before a release costs one gate round; a defect shipped in one is permanent. **Never rank release
readiness above defect elimination, and never let release pressure defer a finding to next-touch debt.**
(Memory `feedback_no_release_until_defects_zero`.) One correction worth carrying: deposited **files** in
a Zenodo snapshot are frozen, but record **metadata** can be corrected through the Zenodo web UI — so a
wrong claim in a release *description* is fixable; a flaw inside a published PDF is not.

**The target is ZERO KNOWN DEFECTS, not zero defects.** The gates always find something — that is why
the severity-tiered cap exists. Do not blur the two, and do not imply a clean sheet.

**Rules for the ledger:**
- **Verify every entry AT THE ARTIFACT** before recording it open or closed. It goes stale exactly like
  the notes it replaces — that is not a reason to distrust it, it is a reason to re-check before acting.
- **GREP LOOSELY.** Measured while building it: two live defects first read as already-fixed because the
  pattern was too tight — one phrase split across a line break, one with markdown bold inside it. A
  tight-pattern miss is **not** evidence a defect is closed.
- **Burn down in FILE-SIZED BATCHES.** Gate rounds are per-push; one file fixed completely and gated
  once costs far less than one item at a time.
- **Fixing an item creates new unreviewed prose** and restarts the review obligation for the text
  changed — fix and re-sign, or push what was certified.
- Keep the ledger the SINGLE copy. Do not re-list its entries in the handoff; two copies drift.

## High-Value Insight Capture — Standing Rule

Any observation made during a session that could lead to a new theorem, new layer,
new conjecture, or significant axiom relationship must be written to `.claude-local/notes/`
immediately — without waiting to be asked. Do not defer to the end of the session.

**Triggers — capture automatically when any of these arise:**
- A structural connection between two existing layers that hasn't been formalized
- An identification of two mathematical objects as "the same fact in different languages"
- A conjecture about axiom derivability or necessity (e.g. deriving a class field from
  upstream structure)
- An argument that could become a new ZP layer or bridge layer
- A DC-free, choice-free, or purity result not yet in a Lean file
- A new justification for an existing axiom or design principle
- Any observation that directly answers or partially closes an open question in the framework

**What the note must contain:**
1. The insight in plain language (one paragraph — legible without session context)
2. The precise mathematical claim (what exactly is being asserted)
3. What is formal vs. what is still philosophical/conjectural
4. Status: open conjecture / partial proof / architecture clear but unbuilt / etc.
5. Connected notes (link to related `.claude-local/notes/` files)

**File naming:** `.claude-local/notes/<topic>_YYYY-MM-DD.md`

**The test:** Would a future session miss something important if this wasn't written down?
If yes, write it now.

### But the note is the DRAFT. The POINTER is the deliverable. (Measured 2026-07-31.)

**Writing the note is not the durable act; being pointed at from a read surface is.** Measured across
767 notes: **only ~10% were referenced from anywhere a future session actually reads** — `CLAUDE.md`,
`.claude-local/handoff.md`, a `.lean` docstring, or a memory file. The other ~90% were write-only. On
the same day, four separate findings were rediscovered the slow way while the relevant note sat
unread, and every piece of context that *did* reach the session came from a Lean docstring, this file,
or a memory — **not one came from a note.**

So the rule above is half a rule. After writing the note, **wire the finding to the artifact**, at the
site the reader lands on — which is what § "unstated adjacency" already demands of findings generally
(*"write it there, at the site the reader lands on, not five sections away"*). Applied to notes: put
the sentence in the `.lean` docstring / `CLAUDE.md` / the memory, and let the note hold the long form.

**⚠ AND A NOTE RECORDING PENDING WORK GOES FALSE THE MOMENT THE WORK IS DONE.** This is worse than
going unread: an unread note is inert, a stale one actively misleads. Measured 2026-07-31:
`zpa_launders_axb1_as_a_metric_result_2026-07-26.md` says **"Not yet fixed"** of a bedrock defect that
ZP-A **v1.21 struck days later** — and a triage pass nearly reopened it on that basis. Two sibling
notes say "pending" and "status at interruption" and are equally unverifiable. **Never act on a note's
self-reported status; verify at the artifact.** If a finding is a *defect*, its home is a gate finding
or a fix, never a note that cannot know when it stops being true.

**Folder layout (established 2026-07-31, 767 notes triaged):**
- `notes/` — **active only.** Live conventions, indexes, corrections that must not be re-introduced.
- `notes/future-research/` — **open work.** A stated conjecture, an identified gap with a route, an
  "architecture clear but unbuilt". The test: *could a future session do mathematics from this?*
  **Read this folder when choosing what to work on.**
- `notes/archive/{gate-findings,resolved,superseded}/` — historical. Gate reports are an audit trail:
  write them, never expect to read them.

When triaging, **prefer KEEP when torn** — this is a research record and over-archiving is the
costlier error.

## Reviewer Feedback Tracking

Reviewer feedback and correspondence are tracked in `.claude-local/feedback/reviewer_feedback_tracking.md`. That file is private and gitignored. Do not include reviewer names or feedback details in this file.

## License

CC BY-NC-ND 4.0 — share with attribution; no modifications; no commercial use.


# .claudecodes instructions for Lean 4 development
- Always run lake build as two separate PowerShell calls: first `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8`, then `Get-Content build.log | Select-Object -Last 1` (or with a `-match` filter). Never combine them with `;` in a single call.
- Ignore PDF rendering assets and website build artifacts in the root.
- Always check 'lake-manifest.json' for dependency updates before adding new imports.

- When searching for Lean source files in this project, always use the pattern ZeroParadox/**/*.lean, never **/*.lean. The .lake/ folder contains thousands of Mathlib library files that aren't mine."

# Zero Paradox Project Standards

## Development Branch

All work — Lean 4 proofs and PDF rendering — happens on the `illustrated` branch. This is the single active development branch. `main` is production/public. The `lake_testing` branch is retired; do not switch to it or push to it.

## Operational Rules
1. **Single branch:** All Lean and PDF work happens on `illustrated`. No branch switching required.
2. **Math Workflow:** Verify theorem changes with two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`.
3. **PDF Workflow:** Use existing rendering scripts and strictly follow the document versioning and archiving conventions defined above.
4. **Transparency:** Maintain the `.claude-local/` folder for in-progress scripts and internal notes as a private "collaboration buffer."
5. **Sync before starting work:** At the start of any session, always run `git fetch origin main` then `git merge origin/main` before making any changes. Never make edits against a stale base.
6. **Verify no conflict markers after any merge:** Before committing after a merge, run `git diff --check` to confirm no conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`) remain in any file. A file with unresolved markers will commit silently and corrupt the document. This has happened twice on this project.
7. **5-minute timeout on all external tool calls:** Every `PowerShell` or `Bash` call that invokes an external process (PDF build scripts, `lake build`, `python <script>`, long-running `git` or `gh` operations) must use `timeout: 300000` (5 minutes). If the command exceeds this limit, kill it and report back — never wait indefinitely. If it times out, diagnose the cause rather than retrying blindly.
8. **Pull request body — always use `--body-file`:** PowerShell cannot reliably pass multiline PR bodies inline (special characters, arrows, backticks, and asterisks all cause parse errors). Always write the body to `.claude-local\pr_body_<name>.md` first, then create the PR with:
   ```powershell
   gh pr create --title "..." --body-file ".claude-local\pr_body_<name>.md"
   ```

9. **Keep PR description current:** If additional commits are pushed to a branch after the PR is opened, update the PR body to reflect the new content. Update `.claude-local\pr_body_<name>.md` first, then run:
   ```powershell
   gh pr edit <number> --body-file ".claude-local\pr_body_<name>.md"
   ```

10. **GitHub Discussion body updates — always use `-F body=@file`:** Passing Unicode body content through PowerShell string interpolation (`$body = Get-Content -Raw; -F body="$body"`) corrupts multi-byte UTF-8 characters (arrows, subscripts, math symbols). Always write the body to `.claude-local\temp_body.md` first, then pass the file directly:
   ```powershell
   gh api graphql -F query=@.claude-local\mutation_update_discussion.graphql -F id="NODE_ID" -F body=@.claude-local\temp_body.md
   ```
   After every update, verify the live body via `mcp__github__get_discussion` before proceeding to the next thread. This issue was discovered 2026-05-23 when ZP-C (#69) was posted with garbled math.

## File Priority
- Both `.lean` files and PDF build scripts are first-class on `illustrated`.
- All other conventions (versioning, archiving, scripts/ sync) apply as documented above.

## Lean 4 Proof Development: Stub-First Protocol

As proofs grow more complex (ZP-D onward), always use a stub-first approach before writing full proofs. This prevents session hangs caused by heavy import chains and typeclass resolution.

**The workflow for every new ZP-X Lean file:**

1. **Symbol map** — before writing any Lean, map each PDF symbol to its Lean 4 / Mathlib equivalent. Identify which imports are required and which are dangerously heavy (p-adics + EuclideanSpace together, for example, can cause elaborator hangs).
2. **Stub file** — write the complete file with all definitions and theorem statements, but use `sorry` for every proof body. Add `set_option maxHeartbeats 400000` at the top. Do not write proof bodies during the planning or stub step — output the stub file and stop. Wait for a clean build before proceeding.
3. **Build the stub** — run `lake build` and confirm 0 errors on the skeleton. This validates that types elaborate correctly before any proof work begins.
4. **Commit the stub** — commit the sorry-stubbed file immediately after a clean build. This creates a rollback point before any proof work begins.
5. **Fill proofs incrementally** — prove one theorem at a time, building after each. Commit after each theorem is successfully proved. Do not attempt to write all proofs before checking.
6. **Final clean build** — once all `sorry`s are removed, run a final build to confirm 0 errors and 0 warnings, then proceed to the documentation workflow below.

**When to abstract away heavy dependencies:** If a layer imports both p-adic numbers and Hilbert space machinery, consider whether the cross-layer dependency can be replaced with an abstract typeclass or index type (e.g., `Fin (2^k)` instead of `ℚ_[2]`) for the purposes of the proof. Decoupling reduces elaboration load significantly.

## Proof Documentation Workflow

When a ZP-X document is successfully proved in Lean 4, the following steps are **mandatory** before the work is considered complete:

1. **Build clean** — run as two separate calls: `lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8` then `Get-Content build.log | Select-Object -Last 1`. Confirm zero errors and zero warnings.
2. **Purity check** — add a `#print axioms` block at the bottom of every ZP-X Lean file (inside a `section PurityCheck ... end PurityCheck`), one call per proved theorem. The expected result is `'theorem_name' does not depend on any axioms`. Any kernel axiom that appears (`Classical.choice`, `propext`, `Quot.sound`) must be explicitly noted and justified in a comment in the Lean file.
3. **Update README.md** — add or update a row in the `### Formal Verification (Lean 4)` subsection of The Framework, and update the Question Register row for `Formal verification (Lean/Rocq)`.
4. **Sync the SJV registry (SSOT) — mandatory, see the standing rule below.**
5. **Commit all changes together** on `illustrated`.

### SJV Registry Sync — Standing Rule (mandatory on any Lean declaration change)

**Any change that adds, renames, removes, or splits Lean declarations at HEAD — including a new `.lean` file — must update the SJV `declarations` store and re-export `ssot.json` in the SAME change, never deferred.** The SSOT is only trustworthy if it tracks HEAD 1:1; every un-synced decl re-introduces registry drift (the recurring "SJV is a whole reorg behind" problem the ontology-revamp arc eliminated). Treat this as the same reflex as `lake build` and the purity check.

The sequence (via the SJV MCP; tools reload in any session started after the MCP loaded):
1. `migrate_batch` — `add_new` for new decls (`{qualified, file, namespace, short}`); `reconcile` for renames/moves (id-keyed `new.*` + `disposition`) with `remap_deps=true` (or an explicit `deps` list) so deps edges follow; drops for removed decls.
2. `annotate_many` — ontology tags on new/changed entries (no `domain=[]`; a `role:face` needs an `object`). Refine later via `/tag-review` if unsure.
3. `validate` + `verify_integrity` (both green).
4. `export_full(dest="C:/Workspace/ZeroParadox/ssot.json")` — ABSOLUTE path (a relative dest lands beside the MCP).
5. Confirm file paths resolve N/N, then commit `ssot.json` with the change.

Memory: `feedback_sjv_sync_on_lean_change`.
