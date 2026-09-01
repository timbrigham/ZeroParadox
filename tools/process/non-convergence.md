# Non-convergence and rung 5 — what may be downgraded, and what pays for it

**Body for `CLAUDE.md` § `R-NOCONV`.** The rule and the fail-open fence are there; the
measured round counts, the leg table, the guard and its two probes, the oracle test and
the DC-17 numbers are here.

---

**⭐⭐ RUNG 5 — WHEN THE MECHANICAL CHECK ITSELF FAILS THREE TIMES, STOP WIDENING IT AND PUT AN LLM ON
THAT LAYER. (Tim, 2026-08-19.)** Rung 4 says build the checker; it never said what to do when the
checker keeps missing. The tell is unmistakable and it is not "more patterns are needed": **each fix
closes the holes its author thought of, and the next reader finds different ones.** Measured
2026-08-19 on `check_paths.py --claim`, which failed three times in one session — first on markdown
emphasis, then on HTML entities and escaped apostrophes, then on line-start markers where five of ten
were blind and the sixth was covered *by accident*. A `/rely` pass watched the second fix land and
reported that both of its routes were **still** blind in the new version.

**⭐⭐ NON-CONVERGENCE IS A SECOND, INDEPENDENT TRIGGER — AND IT FIRES THE DOWNGRADE. (Tim,
2026-08-21: *"anytime a loop fails to converge stop attempting to write a script and use AI fuzzy
logic instead — treat as a warning instead of a hard gate."*)** Rung 5 above triggers on a check that
**misses** three times. This triggers on a **LOOP that never settles**, which is a different
observation and was measured separately: four `/rely` rounds on `tools/verify/` ran **10 → 4 → 6 → 9**
findings and never quiesced, because each round reviewed code written in response to the last. On
2026-08-21 the same layer deadlocked outright — a one-line, mechanically-verified, zero-judgement fix
demanded by `check_figures` re-staled the `/rely` signature and blocked the push it was made to
unblock. **A loop whose own repairs land inside its own scope cannot terminate, and no amount of
further script will make it.**

**THE TWO MOVES, and the second is the new one:**
1. **STOP WRITING SCRIPT.** Put an LLM screen on the layer, subject to every fence below.
2. **DOWNGRADE THE GATE TO A WARNING.** It reports, it does not block. Enforcement moves to the
   human read, which is where the judgement already was.

**⚠ WHAT MAY BE DOWNGRADED, AND WHAT MAY NOT — this is the whole safety of the rule.** The unit is
still the defect class (§ below), so ask what the gate DOES:
- **An ENUMERATION gate — "have all sites been enumerated / do all hashes match / is everything
  covered".** Its failure mode is *incompleteness*, it can never prove itself done, and its own
  repairs re-arm it. **→ DOWNGRADE. It becomes a warning and a reading list.**
- **A FAIL-OPEN gate — one that catches bad work getting THROUGH.** A check that can be walked past, a
  signal that can be forged, an exemption anything can grant itself, a gate reporting success it has
  not earned. **→ NEVER DOWNGRADE, no matter how many rounds it takes.** Non-convergence in an
  enumeration is a fact about the enumeration; a fail-open is a fact about the work. `guards.py`, the
  bedrock cap, the quarantine check and the hook-armed check are all this kind.

**⚠⚠ SPLIT AT THE LEG, NEVER AT THE CHECK — the first draft of this rule got that wrong and the
error was silent.** A single check routinely has legs of both kinds. The `/rely` routing check is the
worked example: *"a routed `.md` changed since the signature"* is enumeration and downgrades, while
*"a checker's executable LOGIC changed since the signature"* guards against unreviewed weakening of
the verification layer and **must keep blocking**. Downgrading the check wholesale carries the second
across with the first.

**⚠⚠ AND ASK WHAT THE DOWNGRADE UN-PRICES. AN EXEMPTION BOUGHT WITH A BLOCK IS UNPAID THE MOMENT THAT
BLOCK BECOMES A WARNING.** ⭐ **LANDED 2026-08-21, AND THE PRICE IS NOW SPLIT THE SAME WAY THE LEGS
ARE.** `tools/verify/**` and `tools/process/**` skip editorial and adversary, and what pays for that
depends on WHAT changed:

| what changed under the prefix | `/rely` routing | what pays for the exemption |
|---|---|---|
| **executable logic** (`.py`, hooks) | **BLOCKS** | `/rely` covers it and blocks. Unchanged. |
| **exemption switches** (baselines, whitelists, pins) | **BLOCKS** | as above — a fail-open surface, never downgradable |
| **routed prose** (`.md`) | **WARNS** | **no longer a block** — see the warrant below |

**The prose leg's warrant is now an ARGUMENT, not a gate, and it has to stand on its own.** It is
this: routed `.md` is operating instruction of the same kind as `CLAUDE.md`, which is exempt from
both prose gates **and routed nowhere at all, by design**. So advisory `/rely` coverage is strictly
*more* review than the parent file gets, not less. **The fence is what makes that hold — anything
asserting mathematics belongs in the corpus and is gated normally** (`tools/process/README.md` states
the criterion). If that fence ever slips, this warrant fails and the prose must go back to editorial
and adversary; that is the trigger to watch, and it is a content question, not a tooling one.

**⚠ THE MECHANICAL HALF IS BUILT AND CONTROLLED.** `guards.py` § *the router the exemption is priced
on still BLOCKS* walks five routes: the fail-open legs are declared blocking, `check_routing` emits
those flags, every consumer of it honours them, `routing_bad` computes correctly, and `cmd_prepush`
still calls it. Two probes in `.claude-local/tools_wip/` are its controls —
`probe_warrant_blocks.py` neuters enforcement three ways and requires `guards.py` to go red on each
(it does), and `probe_docs_only_clears.py` exercises both halves: a docs-only edit clears as a
warning, a checker edit still blocks.

**Why the guard had to exist first, in one line:** enforcement mode used to be a literal at one call
site (`bad += 0 if ran else 1`), so no control could read it — a probe measured `guards.py` printing
`ok` over a router that had stopped blocking, the **fifth** warrant-satisfied-while-empty in that same
code (rounds 1–4: sampling, narrowing, a three-probe set, unchecked regex flags). The warrant tested
COVERAGE and the exemption is priced on coverage **and** enforcement. The mode is now data
(`_LEG_BLOCKING`, `routing_bad`), which is the entire reason it is testable.

⚠ **The rule this instance satisfied, kept for the next one: before any downgrade lands, the guard
asserting what still BLOCKS lands with it — or the exemption it warrants is given up in the same
change.**

**⚠ NON-CONVERGENCE MUST BE MEASURED, NOT ASSERTED — or this rule becomes a licence to downgrade any
gate that is currently inconvenient.** Name the rounds and their finding counts, as the `10 → 4 → 6 →
9` above does. *"This keeps blocking"* is not evidence; it is usually the gate working. And this does
**not** touch § *If a stage BLOCKS, fix the cause* — downgrading a gate's declared enforcement mode,
deliberately and in writing, is a different act from `--no-verify`-ing past one that still blocks.
**This project has two recorded bypass incidents and neither would have been legitimised by this
paragraph.**

**⚠ AND A DOWNGRADED GATE MUST GET LOUDER, NOT QUIETER.** A warning nobody reads is strictly worse
than a block, because it manufactures the appearance of coverage — which is `RLY25-1` exactly: a
report publishing `pass` for a property it no longer checks. So a downgrade obliges the manifest to
say **WARN** at every entry point (`report.py` already formats this), and obliges the count to be
printed on every run, blocked or clear, the way `check_poles.py` prints its suppression count so
rubber-stamping shows up as a rising number instead of going quiet.

**⚠ THE DISCRIMINATOR — AND THE UNIT IS THE DEFECT CLASS, NEVER THE TOOL.** Both gates caught the
first draft on this: `--claim` is *itself mixed* — locating a phrase is enumeration, judging that the
located sentence misdescribes the section it cites is ground truth, and the second is what the fix
that triggered this rule actually turned on. Escalating "the tool" would carry the second across with
the first.

**THE TEST — name the ORACLE, not the failure type: does deciding ONE candidate site require opening
another artifact?**
- **NO — self-contained.** The sentence in front of you settles it. Formatting shapes, phrasing,
  fragments, "does this paragraph contradict the one above it". **→ AN LLM SCREEN IS THE RIGHT
  LAYER.** It reads the sentence and does not care whether the line began with `>`.
- **YES — you must go and read something else.** Does this citation say what we claim; does this
  locator resolve; what is this declaration's real footprint. **→ DO NOT ESCALATE.** `DC-17` measured
  it: 10/10 on the self-contained slice, **0/8** on the citation slice. Fix the tool, or hand it the
  source.
- **BOTH SURFACES AT ONCE — a THIRD category, and the first draft routed it wrongly.**
  Cross-surface consistency ("README under-names relative to CLAIMS") *reads* like enumeration and is
  not: deciding it means holding two artifacts simultaneously, and `DC-17` measured that context lines
  **hurt** here. **→ HUMAN OR GATE. Neither the checker nor the screen.**

**⚠⚠ THE SCREEN MAY REPLACE THE ENUMERATION. IT MAY NEVER REPLACE THE VERDICT.** `DC-17` measured
precision as *unstable* — 1, 4, 4, 3 false positives across four runs over the same twelve negatives —
and this file's own rule is that a false positive is the more expensive error, because it manufactures
work that looks urgent. So the screen widens the candidate set and a human or a gate adjudicates,
which is exactly what makes `fragment_screen.py` work. Two operational rules come with it, or it gets
run once and believed: **take sites flagged in ≥2 of 3 runs**, and **ignore self-reported confidence**
— `DC-17` measured `UNSURE` used **zero times** on the slice the screen got wrong.

**⚠ AND THE MISAPPLICATION FAILS SILENTLY, WHICH IS WHY THE FENCE MUST BE AN ARTIFACT.** Point a screen
at a ground-truth question and it does not refuse — it returns a confident PASS, because it accepts the
sentence's own label as its warrant. Prose cannot stop that, and prose is what this rung exists to stop
relying on. **Any screen must run `deepseek/pole_groundtruth.json` — the recorded slice it should get
wrong — and be disqualified mechanically when it scores well on it.** That is the `check_checkers.py`
move: the control is the deliverable.

⚠⚠ **AND RUNG 5 IS NOT "PREFER AN LLM".** Measured in the round that produced it: all three prose kills
came from *reading*, and the one finding neither gate's reading caught — a register fingerprint
attesting a hash that matched nothing — came from **running a two-line comparison**. No screen would
ever have caught it. **Where a mechanical check is possible at all, it still beats this rung.** Rung 5
is for where enumeration has been *demonstrated* unbounded, three times, not for where it is merely
tedious.

⚠ **The screen is a READING LIST, exactly as the mechanical version was** — it locates, a human or a
gate judges. And it is a SCREEN, not a replacement: keep the mechanical check for the shapes it does
catch, because it is free and it runs on every push. `.claude-local/deepseek/` is the existing bulk
tier (memory `feedback_llm_screen_for_grammar`, Tim 2026-08-02, where a whitespace rule corrupted 61
files and **the damage checker written to catch it had the identical bug**, so it certified the
damage). That memory has never bound anything, because memory bodies do not load — which is why the
rule is here.

**⚠⚠ DO NOT SKIP TO STEP 3 AND WRITE A NEW SECTION.** That is the reflex, it feels like progress, and it
is how this file grew past the point where its tail fires. A recurrence usually needs a **trigger
changed**, not a rule added.
If you are about to add a section, first find the one that already says it and ask why it did not fire.

---

## Never trade falsifier sensitivity for fewer false alarms

*Migrated from a private memory, 2026-08-28.*

When a gate OVER-flags — flagging result identifiers like `T-SNAP`, `MC-1`, `DA-1` as possible
"coinage" — **do not carve an exemption into the falsifier to stop it.**

**The asymmetry:** a false positive is CHEAP — the human glances and dismisses in seconds (Tim,
2026-06-26, overruling the adversary's `T-SNAP` "coinage" flag). A false negative is EXPENSIVE — a
genuine coinage ships and crank-triage fires on a real reader. **A falsifier should err toward
over-flagging.**

**Why not relax it, in Tim's words:** an exemption ("identifiers are fine / labels are exempt") is
**the exact hole a real coinage hides behind** — *"we could potentially end up leaking the other
direction."* Relaxing sensitivity to cut false alarms re-opens the failure mode the gate exists for.

**The division of labour:** the distinction belongs in the **document**, as positive framing (the
GUIDE's "On vocabulary" note: result IDENTIFIERS, labels for specific results as any formal
development assigns, are not vocabulary COINAGE for existing structures). **The falsifier stays
liberal and skeptical, untouched. The human adjudicates each flag.** The adversary flagging and Tim
dismissing IS the system working, not a bug to engineer away.

⚠⚠ **THIS DOES NOT CONTRADICT THIS FILE'S OTHER RULE ABOUT FALSE POSITIVES, AND THE TWO MUST NOT BE
CROSS-CITED.** The rule above ("a false positive is the more expensive error") is about an **LLM
SCREEN standing in for an ENUMERATION**, where a false positive is never adjudicated by anyone and so
**manufactures coverage that was never earned**. The rule here is about a **REVIEW GATE producing a
reading list a human adjudicates**, where the same event costs seconds. **The discriminator is
whether a person is guaranteed to look at each flag.** If yes, over-flag. If the flags are counted
rather than read, a false positive is the expensive one.

---

## Screen prose with an LLM, not a regex — and verify the detector before believing a zero

*Migrated from a private memory, 2026-08-28.* Tim, 2026-08-02: after a mechanical find-and-replace
over prose, screen the result with DeepSeek — *"a quick and excellent tool for finding stuff like
sentence fragments… we could run corpus wide without it costing anything substantial."*

**Why regex structurally cannot do this:** it cannot tell an opening `**` from a closing one, and it
cannot tell a subject from a verb. Both failures were measured the same day — a whitespace-tidy rule
matched a *closing-then-opening* `**` pair across a sentence and **corrupted 61 files**, and the
damage checker written to catch it **had the identical bug**, so it validated broken text. Meanwhile
the real defects open on `(` or on a lowercase continuation, so a verb-anchored pattern misses every
one.

**Measured on the first run** (475 changed lines, one 58k-token call): SUBJECTLESS 8/8 real, HOLE 6/6
real, **DECAPITATED 82 reported and ~0 real** — that category flags legitimate `**Bold — text**` and
is noise, so ignore it. **All 11 genuine findings had already survived a regex pass over the same
lines, three gate rounds, and a purpose-built before/after checker.**

Prompts are built by `fragment_screen.py` (`diff <range>` for "what did my pass break", or `files`
corpus-wide) and looped by `run_fragment_screen.py` against the API directly, so batches never route
through the calling model's context.

⚠ **VERIFY THE DETECTOR BEFORE BELIEVING A ZERO.** A clean run returned 0 immediately after one that
returned 96 — a swing not credible on its face. Inject two or three known-broken lines into a **copy**
of the prompt, never the repo, and confirm they come back: measured 3/3 caught with 0 false positives
on the clean text, which is what made the 0 trustworthy. This is the standing rule generalised —
**before acting on an absence, check that the test could have found the thing.**
