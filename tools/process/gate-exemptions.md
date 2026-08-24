# Gate exemptions, where things live, and the three-tier publishability boundary

**Body for `CLAUDE.md` §§ `R-EXEMPT` and `R-CONTEXT`.** The rules are there; the full
exemption argument, the three-tier layout table, the retired mirrors and the public
reader position on the private working folder are here.

---


**Gate exemption — this file and operational meta.** `CLAUDE.md` itself (and other internal operating-instruction / meta files, as opposed to the mathematical publication content) is **exempt from the Editorial Review Gate and the Adversary Review Gate** below. The review gates are scoped to externally-facing publication prose — formal documents, companions, README.md/GUIDE.md, build-script prose. `CLAUDE.md` is the operating manual, not publication content, so it needs **version control only**: commit and push normally, and use `git push --no-verify` if the pre-push hook blocks on a stale review signal for a `CLAUDE.md`-only change.

**The exemption covers the VERIFICATION CODE (2026-08-15).** `tools/verify/**` is operating
machinery on the same argument: a checker makes no claim about the mathematics, so there is nothing
for an editorial or adversary gate to review. **`/rely` reviews that layer instead, and it BLOCKS** —
the two are a pair, so weakening the routing re-opens this exemption as a hole.

**AND IT COVERS `tools/process/**` — DECLARED, NOT DERIVED (2026-08-20).** That directory is **this
file's body**: `CLAUDE.md` is a routing table (a condition, the exact file to open, the cost of
skipping) and `tools/process/` holds what the routing points at. Same argument, same price —
operating instructions asserting nothing about the mathematics, so editorial and adversary have no
claim to review, and **`/rely` covers it and BLOCKS.** The carve is written here **because the
paragraph below forbids inferring it**; do not extend it to a further directory by analogy — write
the next one down too, or it is not exempt. **Fence: anything asserting mathematics belongs in the
corpus and is gated normally.** Criterion for what may live there, and the two sections that
deliberately may not: `tools/process/README.md`.

⚠ **IT DOES NOT COVER `.claude/commands/`, AND THE DISTINCTION IS THE POINT.** The gate briefs are
now published deliberately, as the artifact showing how this project reviews itself, so they are
**publication content and both gates fire on them** — `VERIFICATION_BUILDOUT.md` Phase 7 lists "the
gate command files" under publishing the method and calls the review non-discretionary. `CLAUDE.md`
is exempt because it is an internal manual that happens to live in a public repo; a gate brief is
being surfaced *on purpose*. **Published-and-exempt is not a category you may reason your way into
from "it is operating instructions" — CLAUDE.md is the exception, not the rule.** Same for
`DEFECT_CLASSES.md`, `vocabulary_reference.md` and the protocols, which is why those stayed private
when the code went public.

## ⭐⭐ DIRECT `git` AND `gh` ARE BLOCKED FOR AGENTS. USE `gitRobot`. (2026-08-22.)

**TRIGGER — an action, so there is nothing to adjudicate: you are about to type `git` or `gh`.** A
`PreToolUse` hook inspects the **whole command string** for a word-boundary `git` or `gh` and denies
it — bare, `cd`-chained, `&&`-chained, `git -C`, absolute `git.exe`, shelled out of Python. It
**fails closed**: empty or unparseable input denies.

**Why, measured the day it landed:** `illustrated` had **no branch protection at all**, `main`
required **zero status checks**, `.claude/settings.json` was `Bash(*)`/`PowerShell(*)` with no deny
rules, there are **two recorded bypass incidents**, and `reset --hard` / `checkout -- .` / `clean` /
`stash` **fire no hook at all** — which is how the most expensive incident here destroyed an
uncommitted edit and then correctly reported success.

| you want | use |
|---|---|
| status, unpushed count, **what would block a push** | `status()` — one call, more than `git status` + `git log ..HEAD` gave |
| any read — `log` `diff` `show` `ls-files` `rev-parse` `blame` `cat-file` | `read(op=..., args=[...])` — tier 3, no gate, no audit, always available |
| stage | `stage(paths=[...])` — **named paths only**; `-A` is refused on the main repo and permitted for `.claude-local` |
| commit | `commit(message_file=...)` — message from a FILE, never argv; runs `precommit` first |
| push | `preflight()` → poll `preflight_status()` → `push(branch, reason)` |
| sync before work | `fetch()` then `merge(branch, reason)` |
| a private checkout to mutate in | `worktree(action='add')` → path; `'remove'` tears it down |
| move HEAD, drop a branch, untrack a file, tag | `switch` · `branch_delete` (safe only) · `remove_files` (named, no `-f`) · `tag_create` (no deletion verb) |
| why was I refused | `explain(refusal_id)` · `history(limit)` for the audit log |
| a **release** | **Tim.** Releases mint permanent DOIs; that is not an agent decision |

⚠ **DO NOT WORK AROUND IT** — no aliases, no wrapper scripts, no shelling out from Python. If you
believe you genuinely need direct git, **say so and let Tim decide**.

⚠ **THE MATCHER SEES ARGUMENTS, NOT JUST COMMANDS.** A path containing the standalone token blocks
the whole command — a file named `...-direct-git-migration.md` cannot be passed to *any* shell
command, **including the one that would rename it**; the only escape is a glob avoiding the literal.
**Never put a bare `git` in a filename.** (Measured 2026-08-22, on a file this project created that
same day.)

⚠ **TOOLS THAT USE GIT INTERNALLY ARE UNAFFECTED.** The hook intercepts **agent tool calls**, not
subprocesses spawned by a Python process. `batch.py`, `hooks.py`, all 21 checkers that shell git,
`check_frozen.py`'s upstream-ref basis and every build script keep working untouched. **Do not
"migrate" them** — there is nothing wrong with them, and rewriting them onto an MCP server the
pipeline cannot depend on would break the gates.

⚠ **`gitRobot` IS LAYER 2 OF 3, AND LAYER 3 DOES NOT EXIST.** Local enforcement raises friction
against drift; it cannot bind an actor who controls the machine. **The only sound layer is remote
branch protection with required status checks, and it is still not configured.** Do not read this
section as the hole being closed.

📖 **What is denied, why, and what would REOPEN each item — `.claude-local/notes/access_controls_2026-08-22.md`.**
Several are provisional. **The server's own definition, including the tier model and the
absent-by-design parameters, is `C:\temp\gitRobot.md`.**

## ⭐⭐ WHERE THINGS LIVE. Three tiers, and the boundary is PUBLISHABILITY, not convenience. (2026-08-15.)

| tier | what | tracked? |
|---|---|---|
| **`tools/verify/`** | every checker, the pipeline (`batch.py`, `hooks.py`, `guards.py`, `report.py`, `vendored.py`), the **baselines**, the **git** hook sources + `install_hooks.py` | **yes — public** |
| **`tools/verify/claude_hooks/`** | the **Claude Code** `PreToolUse` hooks — `block_git_gh.ps1` and its 24-case control, the two enforcement shims. Wired from the tracked `.claude/settings.json`, so a clone inherits the guards rather than an appearance of them (2026-08-23, `GUARD-1`) | **yes — public** |
| **`scripts/`** | every PDF build script, `zp_utils.py`, `scan_pdfs.py`, `PDF_Rendering_Standards.md` | **yes — public** |
| **`tools/process/`** | `CLAUDE.md`'s body — the argument behind each routed rule | **yes — public** |
| **`.claude/commands/`** | the review-gate definitions Claude Code reads | **yes — public** |
| **`.claude-local/`** | signals (`*_cleared.txt`), `batch_state.json`, `gate_round.json`, `DEFECTS.md`, `notes/`, `feedback/`, `outreach/`, `papers/` | **not tracked by THIS repo — it is its OWN repository**, with its own history, a `master` branch and a private remote (`ZeroParadoxLocal`). The parent additionally ignores the path |

**The line: artifacts of VERIFICATION are public; artifacts of PROCESS-IN-FLIGHT are private.**
A checker and its baseline are reproducible from the public corpus, so withholding them protected
nothing and only made the claims unauditable. A signal recording what this session reviewed is
per-push state that churns on every commit.

⚠ **THERE ARE NO MIRRORS ANY MORE, AND RE-CREATING ONE IS A DEFECT.** Three existed and **two had
silently drifted**: the build scripts, duplicated between `scripts/` and the private folder
(`scan_pdfs.py`, adrift three months), and the gate definitions, which existed in the user-level
Claude directory *and* as a private backup copy — 4 of the 8 had diverged. If something must exist in
two places, that is the signal to change the layout — **not** to add a copy step and a rule asking
someone to remember it. Every old path now holds a tombstone that **exits 2**, and
`python tools/verify/check_moved.py --block` fails if anything still points at a relocated path.

⚠ **A tool NEVER writes its own invocation path down.** Each derives `SELF` from `__file__` and
prints that, so usage text cannot go stale — a hardcoded `python <dir>/tool.py` in a docstring is a
COPY of the path and drifts exactly like a mirrored file. Baselines resolve relative to the checker
for the same reason, so they travel with it. **This file is the one place a literal path is
correct**, because a human reads it and nothing computes on their behalf.

⚠⚠ **NEVER PUT A NON-COMMAND `.md` FILE IN `.claude/commands/`.** Claude Code registers **every**
`.md` in that directory as a slash command, so a `README.md` there silently creates `/readme`. The
directory is an interface, not a folder — anything explaining it goes here instead. (Tim, 2026-08-15,
catching exactly that proposal.)

**What a public reader should know about the published gate briefs, since they cannot follow all of
it:** the 11 files in `.claude/commands/` are the real briefs, run verbatim, and the published
surface as a whole references a substantial number of artifacts inside `.claude-local/` —
measure it rather than quoting a figure; an earlier count here said 66 and an adversary pass
measured considerably more across the wider surface — the notes, the defect ledger, the papers library, the DeepSeek
screening scripts, and the per-push signal files. Those are deliberately private (see § *Private
Working Folder*), so a reader can see exactly what each gate is instructed to do and cannot open
every artifact it names. That is the honest position and it should be stated rather than discovered:
**the method is public; some of the material it operates on is not.**
