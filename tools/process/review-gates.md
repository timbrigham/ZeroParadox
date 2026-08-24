# The editorial and adversary gates — protocol, signal scheme, and what triggered them

**Body for `CLAUDE.md` §§ `R-ER` and `R-AR`.** The rules are there; the SHA-256-per-file
signal scheme, the hash-from-disk correction, the `MIG-3` fail-open, and the incident that
created each gate are here.

---

## Editorial Review Gate — Hard Rule

**Any commit touching document prose requires editorial review to have completed before the commit is made.** This applies to:

- Changes to any build script `body()`, `cbody()`, `sp()`, or box-helper string content
- Changes to README.md, GUIDE.md, RELEASES.md, or any `.md` file in the repo root (except `CLAUDE.md` — see the gate exemption above)
- Changes to any companion or formal document build script
- Changes to register.md

**The protocol:**
1. Before committing any of the above, run `/editorial-review` — ⚠ **and PASS IT THE FILE PATHS
   EXPLICITLY (Targeted mode) until `MIG-3` is fixed.** Pre-commit mode discovers its own scope with
   `git diff --staged`, which is now denied, and **the denial FAILS OPEN**: the empty result reads as
   *"nothing staged"*, the brief falls back to Full Scan, reviews a scope nobody asked for, and
   **still writes a signal** hashing whatever it opened. A gate certifying the wrong file set while
   reporting success. Same pattern in `/adversary-review` and `/claim-review`. Ticket:
   `.claude-local/queue/tooling-briefs-gitcall-migration.md`.
2. Wait for the editorial agent to return a verdict
3. If FAIL: resolve every item in the kill list before committing
4. If PASS: the agent writes `.claude-local/er_cleared.txt` recording the SHA-256 of each reviewed file (see the SHA-256-per-file scheme below) — proceed with the commit

Same-session self-review does not satisfy this requirement. `/editorial-review` spawns a fresh agent with no conversation history.

The pre-push hook validates `.claude-local/er_cleared.txt` and `.claude-local/ar_cleared.txt` (and `pa_cleared.txt` on a `.lean` trigger) using the **SHA-256-per-file scheme** (2026-07-20): each signal records the content SHA-256 of every file the review certified (line 1 = verdict record; lines 2+ = `<sha256>  <path>`), and it is valid iff (a) every recorded file still hashes to its recorded value and (b) every *reviewable* file in the push is covered by a recorded hash. Reviewable = changed files minus pure data/binary (`ssot.json`, PDFs, images, lockfiles), so a data-only commit no longer stales a review — that was the old HEAD-equality scheme's failure mode. If nothing reviewable changed, no signal is required. `--no-verify` should now be genuinely rare; if a signal is stale it is because a reviewed file actually changed (re-run the review) or a new reviewable file is uncovered.

⚠ **EVERY hash in this scheme is of the FILE ON DISK. Never a git value** (Tim, 2026-08-09). Not `git show "HEAD:<path>"`, not the index, not the blob — `Get-FileHash -Algorithm SHA256 <path>` or `sha256sum <path>`. **Why it is a rule and not a preference:** the four command files used to say *"compute each hash from the committed content … `git show "HEAD:<path>" | sha256sum`"*, and that is one command meaning two different things depending on when it runs. At push time HEAD is the new commit, so it matched and the instruction looked correct for months. But editorial and claim-review are **pre-commit** gates, so there HEAD holds the **OLD** content: the reviewer certifies the pre-edit file, the commit lands, and the hook compares against a hash of content that no longer exists. **Measured 2026-08-09** with both controls — on a clean tree the two forms agree (which is why nothing ever caught it), and on a dirty tree they diverge, with the `git show` form returning the hash of the *unmodified* file. Fixed in `.git/hooks/pre-push` and its staged copy (`file_hash` now hashes the path), and in all four command files. `batch.py check_signals` already hashed the file on disk, so all three components now agree. **CRLF is not a hazard here:** `.gitattributes` declares `* text=auto eol=lf`, which overrides `core.autocrlf`, so working files are LF on every clone. ⚠ Hooks live in `.git/` and are **not** version-controlled — re-install from `tools/verify/proposed_pre_push_hook.sh` per clone or this fix is absent.

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
