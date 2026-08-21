# Prior art — the measured cases, the three-step check in full, and how the gate runs

**Opens when:** you are about to build something you could state in one sentence of standard
mathematical English, you are writing a scout brief, or you are asking why the prior-art gate
blocked a push.

`CLAUDE.md` carries Trigger 0, the five trigger conditions and the papers-library rules. This is the
evidence behind them.

## 1. Trigger 0 — the measured cases

**2026-07-27, three findings in a single day, every one searchable beforehand:**

| what was built | what already existed | cost of not looking |
|---|---|---|
| `notEL_unique` (the non-terminating element of the final coalgebra of `1 + X` is unique) | **Escardó's `not-finite-is-∞'`** (TypeTopology) — proved from function extensionality alone, where ours carries `Classical.choice` | a whole build, and a *purer* proof left on the table |
| `HasFirstStep` (a first step above the bottom, nothing between) | **Mathlib's `CovBy`**, over a weaker typeclass, plus `CovBy.unique_right` and `not_covBy` | a false `[ZP-CUSTOM]` registry entry, **and we missed `denselyOrdered_iff_forall_not_covBy` — a BICONDITIONAL stronger than the framework's own claim** |
| the Glauber one-bit probes | **one sentence** of Krapivsky-Redner-Ben-Naim p. 123; the premise of Hajek (1988); five lemmas already in Mathlib as `Real.sigmoid` | 256 lines cut to 162, proof body to 6 lines; three claims retracted |

**The point is not embarrassment-avoidance — searching first gets you MORE.** In those three cases
it would have handed us a stronger theorem (the density biconditional), a purer proof (Escardó's),
free derivative/analyticity/continuity lemmas (`Real.sigmoid`), and the standard NAME for a thing
described longhand ("critical slowing down").

## 2. The three-step check, ~10 minutes

**1. Grep our own corpus.** *The cheapest miss, and it happened three times in one day* —
`NatListRegime.lean` already had the `1 + X` coalgebra, `Miniature.lean` already had `enat_fp_iff`,
`State/ReversibleSpectrum.lean` already had `Reversible` (a third definition of detailed balance was
written anyway). Not literature. A grep.

**2. Grep the pinned Mathlib for the CONCEPT, not the name you would have chosen — and if the claim
is a Lean statement, RUN `exact?`.**

⚠⚠ **`exact?` beats grep and it is the only step here whose verb is *RUN*.** Grep searches **names**;
`exact?` searches **statement shape**, so it finds the lemma even when the library's chosen name is
one you would never have guessed — exactly the case where grepping "the concept" also fails. Same
authority argument as *"grep is not the authority; `#check` is"*, and it reaches the
attribute-generated siblings (`@[to_dual]`, `@[simps]`) that have **no source line to grep**.

**Measured 2026-08-12:** a ten-line hand proof was written for the generic
connected-vs-totally-disconnected wall, having run steps 1 and 2 that same session on a neighbouring
thread. **`subsingleton_of_preconnected_totallyDisconnected` was already in Mathlib**, found by an
adversary gate with `exact?` and by no grep. Adopting it cut the proof body from seven lines to one
**and corrected the mathematics**: the library states the result as `Subsingleton α`, so the
obstruction is a **cardinality floor** — connected plus totally disconnected forces *at most one
point*, and `Nontrivial` forbids it — not the topology fact the hand proof's route through
`connectedComponent` implied. **The standard framing was not merely shorter; it was the honest
statement of what the theorem obstructs.** Purity was checked before swapping, per the `CovBy`
precedent: no regression.

**3. One literature search** if the object has a name (Glauber dynamics, coalgebra, covering
relation). `.claude-local/papers/` FIRST — it is the downloaded-source library.

## 3. The papers library works in both directions

A **probe or scratch script** goes in the session scratchpad and is deleted. A **fetched SOURCE** is
the opposite: it goes in `.claude-local/papers/`, named `author_topic_year[_id].pdf`.

**Measured 2026-08-02.** Nothing said this before, so every scout fetched, used and abandoned — and
the next one re-fetched or wrongly reported the source unobtainable. 19 PDFs were sitting abandoned
across session scratchpads, **15 of them genuine and absent from the library**: **Diaconescu 1975**
(cited in five Lean files and the subject of its own ledger entry), **Barwise & Moss *Hypersets***,
**Paulson's ZF final-coalgebra paper**, **Rutten & Turi**, **Hajek 1988** and
**Krapivsky-Redner-Ben-Naim ch. 7** (the last two named in the Trigger-0 table above as prior art
this project had already missed once), and the **Buckingham / Castro-de Boer / Villaverde** sources
cited by name in `CLAIMS.md`.

**Measured 2026-07-26, the other direction.** A scout spent a full search declaring Aczel's
*Non-Well-Founded Sets* unobtainable — 404s, dead mirrors, lending-restricted archive.org — while
`.claude-local/papers/aczel_afa_manuscript.pdf` sat on disk. The cause was a routing omission:
`CLAUDE.md` listed `external/` and not `papers/`, and the brief inherited the omission. **Carry
`papers/` into every scout brief explicitly.**

⚠ **VALIDATE BEFORE FILING.** 4 of the 19 were correctly discarded: three unreadable failed fetches
(a 12KB "Aczel", a 3KB "Glauber", a 2KB "Ramsey" — a tiny PDF is an error page, not a paper) and one
ZP-E build artifact, which is not a source at all. Open it; check the page count and the first page.
A library with junk in it lies in the other direction.

⚠ **Never record a file count.** `CLAUDE.md` carried "55 files / 43 PDFs" — itself a 2026-07-30
correction of an earlier "55 PDFs" that miscounted HTML/txt captures — until the day it went stale
by 15 at once. Measure: `Get-ChildItem .claude-local\papers -File | Measure-Object`.

⚠ **Grep loosely.** Scanned books here are OCR'd with spurious intra-word spaces ("depend ent
choice s"). A miss on a tight pattern is not evidence of absence.

## 4. The exception, and the half of it that gets skipped

**If you cannot yet state the claim in one sentence, building is how you find the shape** and
searching returns noise. Build, then search before promoting. The trigger is nameability, not a
stopwatch — a rule of "never build first" would be wrong and would stop real work.

⚠ **"Then search before promoting" is the half that gets skipped — measured 2026-08-08.** A
requirements-class degeneracy audit (a survey, correctly un-searchable in advance) produced a
**theorem**: the valuation axioms force an infinite carrier. The corpus grep run before the audit
covered the **class names** (`ValBridge`, `ValuationStructure`) and never the **claim** — *one or
infinitely many*, *no finite middle*, *orbit*, *periodic point*. `Order/OrbitDichotomy.lean` already
proved that shape, and its own header **named the framework's scale map as the checkable branch of
it**; cross-references between the files, in both directions, were zero.

**When a survey turns into a theorem, the prior-art clock restarts.** The search that justified the
investigation does not cover the mathematics that came out of it. (The delta was real there, so the
fix was a pointer, not a revert: the trunk assumes `Function.Injective s`, which the class does not
supply.)

## 5. Standard framing is ADOPTED, not noted and worked around

Tim, 2026-07-27: *"anytime that we have official framing we need to make use of it."* Keep the
framework's own label as the handle where one exists — the CC-2 / AX-B1 pattern, where
`HasFirstStep` stayed a name and became `∃ a, bot ⋖ a` — and take the library's lemmas.

⚠ **One caveat, measured the same day: check purity before swapping a proof.** Adopting
`CovBy.unique_right` pushed `firstStep_unique` from `[propext]` to full choice, so the hand proof
was kept and the standard name cited instead.

## 6. Scope of the gate, and how it runs

**Synthesis/bridge layers only.** A trigger fires on content that unifies, connects, or identifies a
structure across more than one field or framework (the diagonal-fixed-point keystone, ZP-P, ZP-G/H).
It does **not** fire on theorem-backed layers whose central claim is a single named classical
theorem the framework merely invokes (ZP-B / Ostrowski, ZP-L/M / Gentzen) — those are already
anchored.

*Caveat, the ZP-D lesson:* a theorem-backed layer can still carry a distinctive **construction** with
its own prior art the cited theorem does not cover. That is caught by trigger 5, not by
synthesis-detection.

**Step 0 — grep our own corpus first.** `/prior-art-review` greps the repo plus `.claude-local`
(notes, `papers/`, `external/`, outreach) before any web search. Much of this project's prior-art
knowledge already lives there, so this prevents false-positive "gaps" — the Bruhat-Tits tree is
already cited in `PadicTree.lean`, and a web-first sweep once "rediscovered" it.

**The adversary gate detects, it does not search.** If a distinctive cross-field claim lacks a
specialist-branch citation — in the content or in the CLAIMS Convergence ledger — and there is no
`pa_cleared.txt` covering the push, it adds a kill-list item; `ar_cleared.txt` is withheld and the
pre-push hook blocks.

**The pre-push hook also checks `pa_cleared.txt` directly** on trigger 5 — a new `.lean` file, or
≥50 net `.lean` lines in the push. This closes the library-duplication leak: a non-synthesis `.lean`
re-proof of an existing library lemma (a `lawvere_fixedpoint` duplicating Mathlib's
`Function.exists_fixed_point_of_surjective`) carries no synthesis claim for the adversary to detect,
so the hook enforces prior art independently of it.

**`/prior-art-review` is the deep gate.** A fresh-agent literature scout states each distinctive
synthesis claim in the target field's terms, searches for and **reads from source** the specialist
branch, and either cites it — with the honest delta, credit pointing outward — or records "searched,
none found". For a new or substantially-expanded `.lean` file the scope also includes a
**library-duplication check** on the file's central and named results, bounded to those rather than
every helper lemma. On PASS it writes `.claude-local/pa_cleared.txt`.

**Same-session self-review does not satisfy this.** The review must be a separate scout context with
no conversation history.

**The record:** the CLAIMS "Convergence with established work" table is the public ledger of
identified prior art; `.claude-local/notes/prior_art_*` holds the per-search findings.
