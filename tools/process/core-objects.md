# Core objects — the full argument, the measured corrections, and the auxiliary indexes

**Body for `CLAUDE.md` §§ `R-COREOBJ` and `R-BEDROCK`.** The rules and the bedrock invariants
are there; the mu/nu fork, the standard names, the choice and computation indexes, the claims
mirror, and every dated correction are here.

---

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

**`Idiom:` (Tim, 2026-08-09) is NOT a third gloss label — the two-label rule above is untouched.** It
is for **running prose that NAMES a phenomenon** rather than describing any declaration: *"the 0=∞
inversion"*, *"the 0=∞ antipodality"*, *"the pole"*. A gloss says what a theorem proves or how the
framework reads it; an idiom is **vocabulary**, and neither existing label fits a handle. **The test
before applying it: does the sentence USE the equation, or does it NAME something?** *"the 0 = ∞
pole"* names. *"0 = ∞ under `rInv`"* asserts, and stays a defect no matter how it is labelled.

⚠ **It is a SUPPRESSION MECHANISM.** It sits in the source where a reader sees it, never in a
baseline file, and `check_poles.py` reports how many sites carry it on every run — so rubber-stamping
shows up as a rising number instead of going quiet. **Apply it only after verifying the site**; a
label applied in bulk is worth less than no label, because it launders the unread ones.

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
wall/floor (μ/ν) carving; and the reframe section of `ZeroParadox/Settheory/Wall.md`.

The engine (`negation_no_fixedpoint` → `lawvere_fixedpoint`) forks: **μ** — the map is fixed-point-free, no
object forms; **ν** — a fixed point exists. The well-founded family then renders a **verdict on ν**: a
well-founded host refuses it (`no_quine_atom`), a host carrying it is thereby not well-founded
(`quineHost_not_wellFounded`, `floor_not_wellFounded`). Same theorem (`wf_no_selfloop`), two hosts — so
well-foundedness is **not a third root of self-reference; it is the axis of the host's verdict**.

**Use the STANDARD NAMES — all four are published and all four sources are in `.claude-local/papers/`:**
- the ν direction is **"the Diagonal Theorem"** (Lawvere & Schanuel, via Yanofsky 2003 p. 5 Remark 3,
  p. 14 Thm 3 — Yanofsky was already cited in `ZeroParadox/Settheory/Wall.md`; the names were not);
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
`floor_not_wellFounded_via_descent`. `ZeroParadox/Settheory/Wall.md` already says "Now adopted."
**This line said "Adopting it is open work worth doing" until 2026-07-30 — while § "unstated adjacency"
BELOW, in this same file, already listed the descending-chain form among the CLOSED finds. One file,
two contradictory answers.** That is the exact trap that produced the `HostVerdict.lean`
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
findings: `.claude-local/notes/archive/gate-findings/prior_art_hostverdict_2026-07-29.md`; the
reframe itself (Tim's) is
`.claude-local/notes/future-research/wall_one_root_or_two_trinary_2026-07-29.md`.

**The choice index (NOT a fourth core object — read it before writing about choice or constructivity):** `ZeroParadox/Category/ChoiceCannotBe.lean` — the `#check`-only index of the framework's **relationship to `Classical.choice`**. `Classical.choice` is an ambient kernel axiom, **not** a framework object, so this index is scoped differently from the three above: where choice is provably not needed, what it must not be confused with, and what is actually established. **Read it before writing any prose, docstring, note, or outreach copy touching choice, constructivity, purity, axiom footprints, or the "choice = point of view / chart selection" reading.** Three standing traps it exists to stop:
- **The equivocation (hit four separate times on 2026-07-19).** The ordinary English "choice" — an act of picking, a point of view, a chart selection — is **not** the axiom `Classical.choice`. Every evocative "choice = which way you view the split" reading is a **model** of the choice-vs-no-choice distinction, never the axiom. State it as a model or not at all. **Attribution, stated precisely — an earlier version of this bullet had it wrong and seeded the error into five Lean files:** Diaconescu (1975) proves an **EQUIVALENCE** — a coequalizer of two nonintersecting monomorphisms has a section *iff* subobjects have complements (p. 176), the choice direction being his corollary (p. 178); in modern terms, choice for inhabited subobjects of a two-element object **IS** excluded middle. That **full** AC is strictly stronger is **Cohen 1963** / Fraenkel-Mostowski independence, **not** Diaconescu — never attribute strictness or a failing converse to him. That the restricted fragment nonetheless *appears* not to follow from excluded middle in Lean — the natural construction fails to elaborate and closes only under `classical`, which is **strong evidence, never a proof of unprovability** — looks like a fact about **Lean's `Prop`/`Type` stratification** (the fragment selects into `Bool`, making it data-valued excluded middle), which a topos lacks; that reconciliation is the framework's own finding. **Never state the Lean gap as a negative result**: a failed elaboration is not an independence theorem, and claiming one would need a metatheoretic argument outside Lean. Full statement: `ZeroParadox/Category/ChoiceCannotBe.lean`.
- **NO COUNT — measure on demand, never record one.** Do **not** write a figure for how many declarations carry `Classical.choice` into this file, into any `.lean` docstring, or into any note. `ZeroParadox/Category/ChoiceCannotBe.lean` deliberately records none and gives the three reasons: a corpus total mostly measures how classically **Mathlib** is built rather than anything about this framework (**mostly, not entirely — `Category/Lawvere.lean:70`'s bare `classical` is the framework's own and is ESSENTIAL**, so do not write "none of it is ours"); it reads as "most of this is non-constructive" when the load-bearing fact is that **T-SNAP is axiom-free**; and the number has already been wrong three times (once quoted rather than measured, once measured and gone stale inside a single session — this bullet itself carried the stale one). That index supplies the PowerShell to measure on demand. **The framework is not choice-free; the core is (`t_snap_derived`, no axioms at all); most examined footprints proved removable; and TWO ARE PROVABLY NOT** (§ IV of the choice index). **Date the claim** — see the lesson below.
  - **⚠ CORRECTED 2026-08-01. This line previously read "every examined footprint has been removable — that statement does not go stale, and it is the one to use." BOTH HALVES WERE FALSE**, and the second half is what made the first durable. The two **essential** cases were committed 2026-07-20, one day after the choice index was last touched: `em_of_wellOrder_comparable` (`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` — comparability of well-orders implies excluded middle; prior art Kraus-Nordvall Forsberg-Xu arXiv:2104.02549 **Thm 38(d)**, there in the data form) and `wem_of_fixedPointFree` (`ZeroParadox/Category/LawvereTaboo.lean` — the general fixed-point-free principle implies **weak** excluded middle, and this one sits on the **keystone**, not on an imported order instance). Both are **taboo reductions**, not failed elaborations, so they clear this file's own bar for a negative result. **Fixed in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV.**
  - **State the shape correctly or not at all.** Each theorem is itself a **choice-free reduction**: the classical content is entirely in the **hypothesis**. What is established is about the **PRINCIPLE** — re-proving it constructively would decide a taboo, so no choice-free re-proof exists — **not** about any particular proof, and **not** an independence result. `#print axioms` reports a proof's footprint and can never witness necessity; that is precisely why the essential side needs a **reduction** where the accidental side needs a **measurement**.
  - **The defect was bigger than this line and was fixed AS A CLASS (closed 2026-08-01).** `ZeroParadox/Category/ChoiceCannotBe.lean` — the index this file *mandates reading* before any prose about choice — had asserted at `:91` *"No essential case has ever been found"* and at `:142` *"**No essential case has been found anywhere in the framework**"* while referencing **neither** theorem (`#check` count: 0). Meanwhile `RELEASES.md:425`, the **published** record, already advertised that index as containing "the two essential cases". The index was written honest and went false **one day later**. **Now closed:** both universal negatives are gone from the corpus (grep the claim: 0 hits) and both witnesses are `#check`ed in § IV. **Residual debt, not yet swept:** several dated notes still repeat the claim — `notes/choice_essential_vs_accidental_2026-07-18.md:31,122,134` and `notes/future-research/roots_enumeration_category_2026-07-20.md:295`. Dated records are deliberately not rewritten (they cite the tree as it stood), so **verify at the artifact, never from a note** — which is this file's standing rule anyway.
  - **The lesson, which is this file's own warning arriving at full scale:** the `#check` lines cannot overclaim; the **prose** can, and here the overclaim is not a gloss on one theorem but a **global negative** ("nowhere in the framework") in an index whose stated premise is that it cannot overclaim. **A universal negative in a `CannotBe` index is the most dangerous sentence shape in this corpus — it is falsified by any single future commit and nothing mechanical notices.** Prefer "none located as of &lt;commit&gt;" over "none exists".
- **The instance hazard.** Choice often enters at the **instance** level, invisible in the lemma: `Prop.instBooleanAlgebra` carries `Classical.choice` while `Prop.instHeytingAlgebra` is `[propext]`. A `Prop`-scoped statement that does not PIN its instance silently acquires choice and every purity claim about it becomes vacuous. Measure the instance and the tactic, not just the lemma.
  - ⚠ **AND THE `PurityCheck` CONVENTION DOES NOT COVER INSTANCES.** It is a per-file section of `#print axioms` over *theorems*. Measured 2026-08-08: **52 of 73 named instances had no `#print axioms` anywhere**, and a further **57 instances are anonymous**, so they cannot be `#print axioms`'d by name at all. All three hand-built `ZPCategory` instances carry `Classical.choice` and none had ever been measured — the hazard this bullet names, live and unnoticed in the corpus that names it.
  - ✅ **USE `python .claude-local/axioms.py <pattern>` — DO NOT PROBE.** `ZeroParadox/Meta/Snapshot.lean` already runs `Lean.collectAxioms` over **every** declaration in every tracked module on each build — 2494 of them, anonymous instances included — and files them in `translation_matrix/golden_master.json`. **Nothing read it for months.** So "is X choice-free?" cost several `lake env lean` probes, and because it was expensive **it got assumed instead** — which is exactly how a wrong purity claim entered this session. `--instances` groups the whole instance surface by footprint; `--summary` gives corpus totals **computed now**, never recorded. ⚠ The snapshot only regenerates where `.claude-local/translation_matrix/` exists, so it does **not** regenerate in CI; the tool prints its own age for that reason. **An empty result is evidence about your pattern or a stale snapshot, never about the corpus.**

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

**Why this rule exists (2026-07-17):** a run of prose/figure errors — fencing ε₀ = 0, "co-locating ⊥ and ε₀," flattening min≡max to one face, calling ε₀ "a large ordinal / ceiling" — all came from reconstructing these objects from working memory instead of reading the Lean. The fix is mechanical: read the `CannotBe` index first, cite the theorem, never gloss.

---

## Routed from `CLAUDE.md`, 2026-08-23

## ⭐⭐ BEFORE YOU EDIT ANY `.lean` FILE: read `ZeroParadox/MANIFEST.md` AND grep the identifiers you are about to touch. Hard Rule. (Tim, 2026-08-15.)

**The trigger is an ACTION, not a category. If you are about to change a `.lean` file — one character, a
docstring, a comment — this fires.** No judgement call, nothing to classify, no exception for "it's only
prose".

1. **Read `ZeroParadox/MANIFEST.md`** — the by-folder index of the whole corpus, **~7k tokens**, cheaper
   than the Engineer's Takes and far cheaper than loading a folder. **104 `.lean` files already point at
   it**; until today this file mentioned it once.
2. **Grep the IDENTIFIER of every declaration you are touching**, not the wording of the claim. Then read
   the hits.

**⚠ WHY THIS EXISTS, AND IT IS A DIAGNOSIS RATHER THAN A RESOLUTION.** § *Development mode* below already
says to load the subsystem. **It did not fire on 2026-08-15 and the reason is its trigger:** *"before
fresh **mathematical development**"* is a **category that has to be adjudicated**, and the adjudication is
where it leaks — *"this is a docstring edit, not development"* is how the rule was talked past, in this
session, by someone who had read it. **Compare § *Core Objects* directly below, which binds reliably: its
trigger is an unmissable TOPIC and it NAMES THREE EXACT FILES.** A rule you must first decide applies is a
rule that does not.

**What it cost, measured the same day.** A `l_inf` docstring was rewritten after grepping three theorem
names. The wording survey found **4** citing sites; `grep -n "l_inf"` returns **9**. And the appended
paragraph re-committed an overclaim that had **already been made and corrected** — the correction sits on
`machine_trichotomy` (`ZeroParadox/Computability/Occurrence.lean` § II), which fences that the
function-vs-relation choice is not the ONLY encoding of the modality, in the very file the new text
cited and never opened. **FAIL-BEDROCK, reverted in
full.** Ledger: `PROC-2`, `OCC-2`.

⚠ **Searching the CLAIM is not the same as searching the NAME, and this file already says the first
half.** § *Review-Loop Cap* says *"grep the corpus for the CLAIM, not the named file"* — correct, and
**insufficient**: a paraphrase search misses every site that cites the identifier without repeating the
phrasing. **Do both. The identifier sweep is the mechanical one, so it is the one that cannot be talked
past.**

⚠⚠ **AND A RULE ADDED MID-SESSION DOES NOT REACH AGENTS SPAWNED LATER IN THAT SESSION.** Measured
2026-08-15, hours after this section was written: a read-only control agent was given the exact task
that had just failed. It performed the reconnaissance correctly and **reported that the `CLAUDE.md`
injected into its context did not contain this section** — its snapshot predates the edit. It found
the rule **by accident**, through an unrelated grep that happened to return a `CLAUDE.md` line. Had
its search been scoped to `ZeroParadox/` (this project's own stated convention for Lean searches) it
would never have seen it. **So an edit here binds FRESH sessions, which read this file from disk, and
silently does not bind the current one's subagents.** Two consequences: **carry a new rule into the
BRIEF explicitly** for the rest of the session in which it is written — briefs are the only thing a
spawned agent reliably reads — and **do not treat a same-session agent's compliance as evidence the
rule works**, because it may never have received it.

⚠ **This is the EIGHTH convention of this shape and the previous seven leaked**, which is the argument for
the narrow mechanical half over the broad remembered one. The durable fix is a tool that prints reverse
references at edit time (`refs.py`, wired into a `PreToolUse` hook and the `precommit` manifest) so it
fires whether or not anyone remembers — the `guards.py` pattern, where the registry is the deliverable and
the discipline is not. **Until that exists, this rule is remembered, and this file records that remembered
rules fail here by construction.**
