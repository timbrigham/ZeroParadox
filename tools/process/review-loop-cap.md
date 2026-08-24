

---

## Routed from `CLAUDE.md`, 2026-08-23

## Review-Loop Cap — Severity-Tiered, Hard Rule

**The gates will always find something. Stopping is a decision about SEVERITY, not a wait for silence.**

⚠ **THE NUMBERS BELOW ARE A HUMAN-READABLE ECHO. `tools/verify/gate_round.py` IS AUTHORITATIVE**
(`BEDROCK_CAP` / `ORDINARY_CAP`), and `gate_round.py show` prints the current round beside both caps.
**Change a cap THERE, in one place, and never here alone** — this paragraph is prose and cannot check
itself. The four gate briefs used to restate the figures too; as of 2026-08-15 they instruct the
reviewer to run `show` and obey it, so a cap change no longer has to be chased across five files.
**What stays written out everywhere is the SEVERITY TIERING below, because that is semantics a
reviewer must act on rather than a number that drifts.**

- **BEDROCK severity → up to 5 iterations.** A violated core invariant (`ε₀ ≠ 0`, `ε₀ ≠ ⊥`, min≡max
  flattened, the snap-arc returning to the same ⊥, a cross-type `=`), a **fabricated** claim about an
  external source, or a false premise carrying a conclusion. These must not ship — keep iterating.
- **ORDINARY severity → 2 iterations, then STOP and push normally.** Citation scope, a mischaracterized
  lemma, hedging a tier too strong, path-convention drift, wording. These never reach zero.

**The stopping question is "did this round find anything BEDROCK?" — if no, stop**, even on ten ordinary
findings. Ratified 2026-07-19 after three rounds; memory `feedback_er_ar_max_iterations` carries the
detail.

**⚠ NO `--no-verify` IS INVOLVED AT THE CAP.** A **STOP-ORDINARY reviewer WRITES ITS SIGNAL**, so the
hook clears **on its own merits** and there is nothing to bypass. Put it in the brief:
*withholding the signal on ordinary findings is not a valid outcome.*

**⭐ AND FIXING A FINDING RESTARTS THE OBLIGATION FOR THE TEXT YOU CHANGED.** The cap's licence assumes
the outstanding findings *stay outstanding*; once you have **acted** on them the push contains **new
unreviewed prose**, which is a different thing from known debt and warrants a gate rather than a flag.
**So: edit after a STOP-ORDINARY ⇒ re-sign. Do not want another round ⇒ do not edit** — record the
findings as next-touch debt and push what was actually certified. Measured 2026-08-01: four of the
next round's six editorial findings landed in the one file no gate had yet seen, which existed only
because it was edited after the gates finished.

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
* **Nothing remains but history** — **delete it.** `read(op='log', args=['-p','--','<path>'])` has it, exactly, permanently, with
  provenance no docstring can match.

**Where history actually belongs:** `.claude-local/DEFECTS.md` while a defect is open, the
gate-findings archive once it is closed. Both are read when choosing work; a docstring is read when
doing mathematics. **The defects that recurred despite earlier fixes did not recur because a docstring
lacked a retraction — they recurred because the ledger was not consulted.**

**YES, THIS MEANS FIX IT SILENTLY — in the file** (Tim asked directly). **Delete the false claim,
state the true one, and let the COMMIT MESSAGE be the narrative.** That is its job, it is versioned,
and it is where a reader looking for history will actually go.

**The record is never lost, because it lives in three places that are not the docstring:** the commit
message, `.claude-local/DEFECTS.md` while the defect is open, and the session itself. **The only thing
being removed is a fourth copy — the one that cannot be checked, drifts, and accumulates.**

⚠ **The narrow thing that is NOT permitted:** letting a fix be invisible **everywhere**. Do not skip
the ledger on an open defect, do not bury a substantive correction under a vague commit subject, and do
not decline to surface it — cross-arc patterns are caught by the human, repeatedly and by measurement,
and he cannot catch what he is not told. **Silent in the artifact, recorded in the process.**

⚠ And this does not touch the dated-survey convention (*"none located as of &lt;date&gt;"*), which
records a **measurement**, not a prior state.

📖 **ROUND MECHANICS AND THE VERBATIM BRIEF BLOCK — `tools/process/review-loop-cap.md`.** Who bumps
the counter and who may only read it; `--target` slugs; and the block that goes into **every** review
brief with N substituted. **Open it before spawning any gate.** Why it matters: a rule about a loop
does not fire from inside the loop — on 2026-07-19 three rounds ran against a 2-round cap because
nobody was counting, and a reviewer that bumped the counter itself burned the cap a round early.
