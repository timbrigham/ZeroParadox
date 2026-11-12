---
description: Sweep the corpus, the notes and the memory for earlier work on the current topic BEFORE building further (Tim's "this feels familiar" tripwire)
---

# `/familiar` — have we been here before?

**Invoke this when** Tim says something feels familiar, when anyone asks "have you seen X?", or
before any scratch probe or `.lean` work on an idea you can state in one sentence. It is step (1) of
`R-PRIORART` ("grep our own corpus"), run as a delegated sweep so the main thread keeps the
conclusion and not the file dumps. Run it at the FIRST familiar-sounding turn, not after building on it; and again before promoting.

**What an old ruling or "never say X" line is, when the sweep finds one.** A tripwire, not a ban
(Tim, 2026-11-11: *"those old claims are a warning to do exactly that right research what we already
have before continuing?"*). No idea is off-limits to explore. What the sweep decides is whether the
work is new, partly new, or already done, and which of the old lines are Tim's own words.

**Caller's job before spawning:** write `$ARGUMENTS` as the topic in one or two plain sentences, plus
the claims made in this session that you want checked, one per line. If `$ARGUMENTS` is empty, write
that list yourself from the conversation; never spawn with an empty topic.

**Caller's job after:** relay the verdicts in plain language, name anything the session would
DUPLICATE, and never write a second copy of an existing declaration; in prose, one line and a
pointer (`R-TOLEAN` step 1). Carry Tim's verbatim rulings to him; revise a Claude-authored line when a
measurement contradicts it.

Spawn the general-purpose Agent (omit `subagent_type`) with this prompt, substituting the topic
list for `$ARGUMENTS`:

---

## HARD CONSTRAINTS

- READ-ONLY. Do not create, modify or delete any file anywhere. No scratch files in the repository.
- Search `ZeroParadox/**/*.lean`, never `**/*.lean`: `.lake/` holds the whole of Mathlib.
- Windows: use the Grep and Glob tools; never `find`. Direct `git` and `gh` are blocked and not needed.
- `.claude-local/` is gitignored and Grep honours `.gitignore`. A Grep from the repository root, or
  one given `.claude-local/**` as its `glob`, returns NOTHING from the private notes (measured
  2026-11-11: 0 hits that way, 381 occurrences of `DC-53` with `path` set to `.claude-local`). Pass
  each place in the list below as Grep's `path`, never as its `glob`. A Grep over the whole of
  `.claude-local` timed out on 2026-11-12: search `.claude-local/notes` and `.claude-local/queue` as
  separate paths.
- Before reporting any claim as not located, run a positive control in each place: a Grep with that
  place as `path` for a token known to be there (`DC-53` with `path` set to `.claude-local/notes`,
  `theorem` in `ZeroParadox`, and in the memory folder a Glob for `feedback_verify_pointer_status.md`,
  a file only this project's memory holds). A place whose control returns nothing was not searched;
  say so instead of reporting "not located".
- Read every hit before you report it. A grep line you have not opened is not a finding.
- An unfound topic is "not located as of <date>, searched as follows", with the searches listed. A
  failed grep is evidence about the search, never about the corpus.

## The task

Find where the following topic, and each listed claim, already appears in the Zero Paradox
repository at the current working directory:

$ARGUMENTS

If the topic above is empty or only a placeholder, do not search: report "SCOPE UNKNOWN — no topic
given" and stop. Be exhaustive: every place below, every phrasing below.

Search all four places:
1. the public corpus: `ZeroParadox/**/*.lean`, `ZeroParadox/**/*.md`, the Markdown files at the
   repository root (list them with Glob, then pass each as Grep's `path`), and the PDF build scripts
   `scripts/*.py`, which carry the shipped PDF prose;
2. the private notes: `.claude-local/notes/**` (including `future-research/` and `archive/`),
   `.claude-local/queue/**` (including `queue/wip/`), `.claude-local/DEFECTS.md`,
   `.claude-local/DEFECT_CLASSES.md`, `.claude-local/handoff.md`, `.claude-local/outreach/`,
   `.claude-local/autobiography/`;
3. Tim's rulings: `.claude-local/notes/tim_rulings_*.md`;
4. the memory files: `C:\Users\timbr\.claude\projects\C--Workspace-ZeroParadox\memory\` (its index is
   `MEMORY.md`; the other project memory folders beside it are not this one).

Use at least three phrasings per claim, varied by POLARITY (how the corpus would say it if it
DISAGREED), PART OF SPEECH (the verb that builds it, not the noun), and VOCABULARY (the standard
mathematical term and the ZP shorthand both), and by DISPLAY: never conclude absence from truncated
output (Grep's default `head_limit` truncates; re-run with `head_limit: 0` or a higher limit before
reporting a count or an absence). Search declaration NAMES as well as wording.

## Report

For each claim: the earlier appearances that matter (file:line, the date if the file carries one,
one line on what it says), then ONE verdict:

- **(a) ALREADY IN THE CORPUS** — name the declaration(s) the new work restates.
- **(b) PARTIALLY** — say exactly what is new.
- **(c) DISCUSSED IN NOTES ONLY** — the earlier conclusion, and whether the current work agrees with
  it or contradicts it.
- **(d) NOT LOCATED** — name the set of places searched and the searches run.

Then two lists:
- **Would duplicate:** existing declarations the current work would re-declare.
- **Earlier lines it touches:** each old ruling, fence or "never say" line the current work runs
  into, marked **TIM VERBATIM** (a quoted sentence of his) or **CLAUDE-AUTHORED** (a fence, a
  "how to apply" line, or a paraphrase). Quote the line. Do not judge whether it still binds; that
  is the caller's job.

Keep the report short: it goes to the caller, not to Tim.
