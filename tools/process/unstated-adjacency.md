# Unstated adjacency — the four measured cases, and the one-line-plus-pointer resolution

**Body for `CLAUDE.md` § `R-ADJACENT`.** The rule is there; the oscillation / min-max /
Turing / descending-chain cases, the two corollaries, and the `l_inf` paraphrase measurement
are here.

---

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

### ⭐ THE TWO RULES ABOVE AND BELOW PULL OPPOSITE WAYS. The resolution: ONE LINE at the site, the FULL STATEMENT at the canonical home. (Tim, 2026-08-15.)

*"Write it **there**, at the site the reader lands on"* pushes toward restating it locally.
*"Never enumerate in prose what the artifact defines"* pushes toward a bare pointer. **Both are rules
on this page and they disagree.** The resolution is the shape the corpus already uses in its
`Statement:` / `Reading:` glosses:

- **ONE LINE of consequence at the site** — what a reader standing here needs in order to keep reading.
- **A POINTER to the canonical home** for the full statement.
- **NEVER a bare pointer** (*"see `l_inf`"* makes the site worse to read, which is what the
  write-it-there rule is protecting).
- **NEVER a paraphrase.** A paraphrase is a copy, and a copy goes stale the instant the original moves.

**⚠ THE TEST, and it is the operative part: WOULD THIS SENTENCE BECOME FALSE IF THE CANONICAL
STATEMENT CHANGED?** If yes, it is a copy — replace it with a line plus a pointer. If no, it is a
consequence and it belongs where it is.

**Measured 2026-08-15 — this is not hypothetical.** `l_inf`'s docstring is already canonical by
adoption: **25 sites depend on it**, six build-script changelogs call it *"the designated honest
stopping point"*, and four retraction commits were written against it as their anchor. **But 10 of the
25 PARAPHRASE it** — *"`l_inf`'s docstring states that the step … is an ontological bridge"* — and a
rewrite of the docstring **falsified four of them immediately**. Ledger: `BLAST-1`, `OCC-2`.

⚠ **A canonical statement can have a copy that can NEVER be updated, and that must be recorded rather
than discovered.** `scripts/build_zpc.py:142` reproduces this docstring's closing paragraph, rendered
into **ZP-C v1.21 — already deposited with a Zenodo DOI.** The build script can be converted so future
rebuilds point rather than copy; **the deposited PDF is frozen and always will be.** That is correct
behaviour for a snapshot, and it means *"one canonical definition everywhere"* has permanent
exceptions. Name them at the canonical site.

**Rollout is AS-TOUCHED, never big-bang** — the same model as the file-path citation convention. A
25-site conversion in one round is the shape that generates new defects; 2026-08-15 is the evidence.

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
