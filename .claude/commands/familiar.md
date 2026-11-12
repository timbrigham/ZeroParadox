---
description: Sweep the corpus, the notes and the memory for earlier work on the current topic BEFORE building further (Tim's "this feels familiar" tripwire)
---

# `/familiar` — have we been here before?

**Invoke this when** Tim says something feels familiar, when anyone asks "have you seen X?", or
before any scratch probe or `.lean` work on an idea you can state in one sentence. It is step (1) of
`R-PRIORART` ("grep our own corpus"), run as a delegated sweep so the main thread keeps the
conclusion and not the file dumps. Run it at the FIRST familiar-sounding turn, never after building.

**What an old ruling or "never say X" line is, when the sweep finds one.** A tripwire, not a ban
(Tim, 2026-11-11: *"those old claims are a warning to do exactly that right research what we already
have before continuing"*). No idea is off-limits to explore. What the sweep decides is whether the
work is new, partly new, or already done, and which of the old lines are Tim's own words.

**Caller's job before spawning:** write `$ARGUMENTS` as the topic in one or two plain sentences, plus
the claims made in this session that you want checked, one per line. If `$ARGUMENTS` is empty, write
that list yourself from the conversation; never spawn with an empty topic.

**Caller's job after:** relay the verdicts in plain language, name anything the session would
DUPLICATE, and turn duplicated work into pointers at the existing declarations, never second copies
(`R-TOLEAN` step 1). Carry Tim's verbatim rulings to him; revise a Claude-authored line when a
measurement contradicts it.

Spawn the Agent with this prompt (`subagent_type: Explore`, thoroughness "very thorough"; substitute
the topic list for `$ARGUMENTS`):

---

## HARD CONSTRAINTS

- READ-ONLY. Do not create, modify or delete any file anywhere. No scratch files in the repository.
- Search `ZeroParadox/**/*.lean`, never `**/*.lean`: `.lake/` holds the whole of Mathlib.
- Windows: use the Grep and Glob tools; never `find`. Direct `git` and `gh` are blocked and not needed.
- Read every hit before you report it. A grep line you have not opened is not a finding.
- An unfound topic is "not located as of <date>, searched as follows", with the searches listed. A
  failed grep is evidence about the search, never about the corpus.

## The task

Find where the following topic, and each listed claim, already appears in the Zero Paradox
repository at the current working directory:

$ARGUMENTS

Search all four places:
1. the public corpus: `ZeroParadox/**/*.lean`, `ZeroParadox/**/*.md`, root `*.md`;
2. the private notes: `.claude-local/notes/**` (including `future-research/` and `archive/`),
   `.claude-local/queue/**`, `.claude-local/DEFECTS.md`, `.claude-local/DEFECT_CLASSES.md`;
3. Tim's rulings: `.claude-local/notes/tim_rulings_*.md`;
4. the memory files: `C:\Users\timbr\.claude\projects\C--Workspace-ZeroParadox\memory\*.md`.

Use at least three phrasings per claim, varied by POLARITY (how the corpus would say it if it
DISAGREED), PART OF SPEECH (the verb that builds it, not the noun), and VOCABULARY (the standard
mathematical term and the ZP shorthand both). Search declaration NAMES as well as wording.

## Report

For each claim: the earlier appearances that matter (file:line, the date if the file carries one,
one line on what it says), then ONE verdict:

- **(a) ALREADY IN THE CORPUS** — name the declaration(s) the new work restates.
- **(b) PARTIALLY** — say exactly what is new.
- **(c) DISCUSSED IN NOTES ONLY** — the earlier conclusion, and whether the current work agrees with
  it or contradicts it.
- **(d) NOT LOCATED** — with the searches run.

Then two lists:
- **Would duplicate:** existing declarations the current work would re-declare.
- **Earlier lines it touches:** each old ruling, fence or "never say" line the current work runs
  into, marked **TIM VERBATIM** (a quoted sentence of his) or **CLAUDE-AUTHORED** (a fence, a
  "how to apply" line, or a paraphrase). Quote the line. Do not judge whether it still binds; that
  is the caller's job.

Keep the report short: it goes to the caller, not to Tim.
