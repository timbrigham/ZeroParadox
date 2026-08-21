"""THE hook pipeline. The shell hooks are three-line shims that call in here.

WHY (Tim, 2026-08-10): *"the shell variants are legacy and should be retired... just the python
version should remain."* The pipeline had TWO partial implementations — a shell hook and
`batch.py` — and they measurably disagreed three ways (PIPE-1): what counts as reviewable
(`CLAUDE.md`), whether signals are required when nothing reviewable changed, and whether a
gate-exempt file recorded in a signal can stale it. They also checked disjoint things: the `/rely`
routing existed only in `batch.py`, the four checkers and the path resolver only in the hook.
Neither was the pipeline.

Shell and Python cannot share a module, so the only way to have one definition is for one of them
to go. The shell went. Everything it orchestrated was already Python (`gatelock`, `check_paths`,
`check_invariants`, the four checkers, `check_hashes`, `scan_pdfs`); the shell was sequencing, and
sequencing is what drifted.

⚠ THIS FIXES REL-1 AS A SIDE EFFECT, AND THAT IS THE POINT OF DOING IT THIS WAY ROUND. The hook
knows the refs being pushed; `batch.py` alone did not, so it computed "what changed" from the
working tree and went vacuous the moment a commit landed. `pre_push` parses stdin and hands the
ranges to `batch.cmd_prepush`, so the shared code is correct at the only moment that matters.

Install (hooks live in .git/ and are still NOT version-controlled — per clone). The hook SOURCES
now are tracked, which is the half that used to be missing:
    python tools/verify/install_hooks.py
"""
import os
import subprocess
import sys

# TWO roots, and keeping them apart is the point of the 2026-08-15 move. `BASE` used to be
# `.claude-local` and served both purposes at once, which is why publishing the bundle was not a
# copy: HERE is the tracked, public tool bundle; PRIV is per-push private state (signals, locks,
# batch state) that deliberately did NOT move and MAY BE ABSENT ENTIRELY in a public clone.
# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3). SELF is
# derived from `__file__`, never written down: a hardcoded invocation path is a copy of the path and
# drifts exactly like a mirrored file does.
#
# ⚠ COERCED TO `str`, not re-derived. This module speaks `os.path`; `common` speaks `pathlib`. A
# line of type conversion is not a second definition — change the layout and there is still exactly
# one place to edit.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

HERE = str(common.HERE)
REPO = str(common.REPO)
PRIV = str(common.PRIV)
SELF = common.self_rel(__file__)
BASE = HERE   # retained: existing call sites below mean "where the tools live"

if HERE not in sys.path:
    sys.path.insert(0, HERE)

import report      # noqa: E402  the one formatter every entry point announces itself with
import vendored    # noqa: E402  the one exemption definition

EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
ZERO = "0" * 40

# SIGPIPE immunity. CLAUDE.md records `git push ... | head` bypassing the gate: head closed the
# pipe and the shell hook died before reaching its `exit 1`. Python raises BrokenPipeError in the
# same situation, so both ends are handled — the signal where it exists, the exception always.
try:
    import signal
    signal.signal(signal.SIGPIPE, signal.SIG_IGN)   # POSIX only
except (ImportError, AttributeError, ValueError):
    pass


def run(*cmd):
    """Run a child, streaming its output, and return its exit code.

    ⚠ Never captures. The whole point of a gate is that the operator SEES why it fired, and a
    captured-then-reprinted stream loses interleaving with anything else that writes."""
    try:
        return subprocess.call(list(cmd), cwd=REPO)
    except OSError as e:
        print("  hook: could not run %s (%s)" % (" ".join(cmd), e))
        return 1


def py(script, *args):
    return run(sys.executable, os.path.join(BASE, script), *args)


def git_out(*args):
    try:
        r = subprocess.run(["git"] + list(args), cwd=REPO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        return r.returncode, (r.stdout or "")
    except OSError:
        return 1, ""


# ------------------------------------------------------------------ pre-commit

PRE_COMMIT_PLAN = [
    ("check_pov", "BLOCK", "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", "BLOCK", "modal claims carry a measurement or a reduction"),
    ("check_classes", "BLOCK", "a new requirements class records a degeneracy verdict"),
    ("check_prose", "BLOCK", "prose caps: block size, docstring vs decl, gloss labels"),
    # ⚠ AT COMMIT, NOT ONLY AT PUSH, AND FOR A REASON THE OTHER FOUR DO NOT SHARE. Double-encoded
    # text is valid UTF-8, so it survives every other check, renders plausibly in a diff, and the
    # window in which the author still knows which write did it is minutes long.
    ("check_encoding", "BLOCK", "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    ("gatelock", "warn", "a review round left open (harm is EDITING, not committing)"),
]

PRE_PUSH_PLAN = [
    ("hooks armed", "BLOCK", "the installed hooks match their tracked sources"),
    ("quarantine", "BLOCK", "private/* branches never reach a remote"),
    ("gate lock", "BLOCK", "no push while a review round is open or files are frozen"),
    ("guards", "BLOCK", "every enumerated ROUTE to a guarded property still behaves"),
    ("check_paths", "BLOCK", "every repo-relative reference in tracked markdown resolves"),
    ("check_moved", "BLOCK", "nothing points at a path that was relocated"),
    ("check_negatives", "BLOCK", "a universal negative carries a date or a search record"),
    ("check_figures", "BLOCK", "an artifact count carries a date, or is measured on demand"),
    ("check_checkers", "BLOCK", "every checker has passing controls, and something invokes it"),
    ("check_invariants", "BLOCK", "Engineer's Takes filled; LEAN_CUSTOM_REGISTRY count matches"),
    ("check_pov", "BLOCK", "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", "BLOCK", "modal claims carry a measurement or a reduction"),
    ("check_classes", "BLOCK", "a new requirements class records a degeneracy verdict"),
    ("check_prose", "BLOCK", "prose caps, baselined; NEW sites only"),
    ("check_encoding", "BLOCK", "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    ("decls", "BLOCK", "every new declaration has #print axioms + an ssot.json row"),
    ("check_hashes", "BLOCK", "build-script fingerprints match register.md"),
    # ⚠ NOT advisory: scan_pdfs' exit code IS the hook's when everything else passes, so it
    # can block a push on its own. Calling it "report" while it did exactly that is a
    # manifest that lies, which is worse than no manifest (/rely pass 3 and 4).
    ("scan_pdfs", "BLOCK", "PDF asset scan — its exit code becomes the hook's"),
    ("batch prepush", "BLOCK", "trigger 5, /rely routing, and the three review signals"),
]


def pre_commit():
    """The four checkers BLOCK; the gate lock warns.

    The stub-first protocol commits `sorry`-stubbed files on purpose, so BUILD state must never
    gate here — and none of these four reads `sorry`, the build, or completeness. They are
    baselined, sit at zero new, and already block at push, so blocking here adds no new failure
    class; it moves an identical, already-mandatory failure earlier, where the fix is cheap."""
    report.banner("pre-commit pipeline", [
        ("entry", ".git/hooks/pre-commit -> hooks.py pre_commit"),
        ("scope", "the WORKING TREE as it stands (checkers scan the corpus on disk)"),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
        ("not run", "lake build / purity / ssot — stub-first commits incomplete work on purpose"),
    ])
    report.plan(PRE_COMMIT_PLAN)

    failed = []
    for script in ("check_pov.py", "check_modal.py", "check_classes.py", "check_prose.py",
                   "check_encoding.py"):
        if py(script, "--block") != 0:
            failed.append(script)

    # Gate lock: WARN only. The harm it guards is EDITING files mid-round, not committing; a commit
    # during a round is a signal worth seeing, not a reason to refuse.
    py("gatelock.py", "guard")

    if failed:
        print("")
        print("Commit blocked — NEW violations in: " + " ".join(failed))
        print("These are baselined checkers, so a hit is a genuinely new site, and each one")
        print("already blocks at push. Fix it now, or ledger it in .claude-local/DEFECTS.md.")
        print("Bypassing here only defers the identical block to the push.")
        return 1
    return 0


# ------------------------------------------------------------------ pre-push

def parse_refs(stream):
    """git feeds '<local_ref> <local_sha> <remote_ref> <remote_sha>' per ref on stdin.

    Returns (ranges, quarantined). `private/*` branches are permanently local and must never reach
    any remote, in either the local or the remote ref position."""
    ranges, quarantined, malformed = [], [], []
    for line in stream:
        if not line.strip():
            continue
        parts = line.split()
        if len(parts) != 4:
            # ⚠ FAIL CLOSED. This used to `continue`, so a ref line git fed us in a shape we did not
            # expect vanished — and a push whose every line was dropped got an EMPTY range set,
            # which reads downstream as "no reviewable change, signals not required". A parse we do
            # not understand is not permission to skip the review (measured, /rely pass 4).
            malformed.append(line.rstrip())
            continue
        local_ref, local_sha, remote_ref, remote_sha = parts
        if local_ref.startswith("refs/heads/private/"):
            quarantined.append("BLOCKED: '%s' is a quarantined branch — never push it." % local_ref)
        if "/private/" in remote_ref:
            quarantined.append("BLOCKED: refusing to push to quarantined remote ref '%s'."
                               % remote_ref)
        if local_sha == ZERO:
            continue                                  # branch deletion: nothing to inspect
        if remote_sha == ZERO:                        # new ref on the remote
            base = ""
            for cand in ("origin/main", "main"):
                rc, out = git_out("rev-parse", "--verify", "--quiet", cand)
                if rc == 0 and out.strip():
                    base = out.strip()
                    break
            ranges.append("%s..%s" % (base or EMPTY_TREE, local_sha))
        else:
            ranges.append("%s..%s" % (remote_sha, local_sha))
    if malformed:
        quarantined.append(
            "BLOCKED: %d unparseable ref line(s) on stdin; refusing to infer a push scope from a "
            "format this hook does not understand:\n    %s"
            % (len(malformed), "\n    ".join(malformed[:3])))
    return ranges, quarantined


def pre_push(stream):
    ranges, quarantined = parse_refs(stream)
    if quarantined:
        for m in quarantined:
            print(m)
        print("Quarantine guard: push aborted. private/* is intentionally local-only.")
        return 1

    rc0, branch = git_out("rev-parse", "--abbrev-ref", "HEAD")
    report.banner("pre-push pipeline", [
        ("entry", ".git/hooks/pre-push -> hooks.py pre_push"),
        ("branch", branch.strip() or "(unknown)"),
        ("scope", ["%d ref(s) being pushed" % len(ranges)] + ["range %s" % r for r in ranges]
                  or ["nothing to push"]),
        ("basis", "the PUSHED RANGES, not the working tree — see REL-1"),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
        ("not run", "lake build — CI at the PR owns build state (stub-first pushes stubs)"),
    ])
    report.plan(PRE_PUSH_PLAN)

    # Ordered cheapest-first: there is no reason to run PDF builds for a push that cannot be
    # allowed. The gate lock is ~0.15s over ~350 tracked files.
    print("\n=== Gate lock check ===")
    if py("gatelock.py", "guard") != 0:
        print("\nPush blocked: a gate lock is held, or tracked files are still frozen.")
        print("Release the round (or sweep the orphans) and push again.")
        return 1

    # ⚠ THE CHECKERS BELOW ARE ONLY WORTH THEIR EXIT CODES IF THEY CANNOT BE WALKED AROUND.
    # `guards.py` plants a known violation and then tries EVERY enumerated route to suppressing it.
    # It runs here, before the checkers it protects, because a green checker whose exemption surface
    # has a new hole is a false zero — and this project's own record is that a false zero costs more
    # than a red one. ~10s, once per push.
    print("\n=== Property guards (exemption surface) ===")
    if py("guards.py") != 0:
        print("\nPush blocked: a guarded property can be walked, or a guard left files mutated.")
        print("Read the FAIL lines above — each names the ROUTE. Fix the route, do not skip the run.")
        return 1

    print("\n=== File-reference check ===")
    # ⚠ 3 means "skipped part of my scope", not failure — see check_paths.EXIT_SKIPPED.
    # Locally the pinned Mathlib checkout is present, so this is normally 0; the branch
    # exists so a developer without a built .lake is not blocked by an unrunnable check.
    _rc_paths = py("check_paths.py", "--all", "--warn-private")
    if _rc_paths not in (0, 3):
        print("\nPush blocked: a repo-relative reference in TRACKED markdown does not resolve.")
        print("Fix the path, or word the line so the resolver skips it (e.g. 'no longer exists').")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1
    print("===========================")

    # ⚠ WIRED IN 2026-08-15, AFTER BEING BUILT AND LEFT UNCONNECTED FOR A DAY. `check_moved.py` is
    # the control that proves the tools/verify migration is complete — a tombstone only helps a
    # human browsing the folder, while this fails when ANY file still points at a relocated path.
    # It was written, tested, given controls, and run only by hand and in CI: the exact "fires only
    # if someone remembers" shape it exists to eliminate, in the tool built to eliminate it.
    # REL10-4. `install_hooks --check` asks "are the gates actually armed?" — a question its own
    # docstring said had NEVER been asked mechanically. It still had not: nothing invoked it.
    #
    # ⚠ A hook cannot detect its own absence — if it is not installed, none of this runs. What it
    # CAN detect is DRIFT: an installed hook that no longer matches its tracked source, which is a
    # hand-edited or half-updated gate. That is the catchable half, and it is worth catching here
    # because everything downstream assumes the shim it was invoked through is the current one.
    if py("install_hooks.py", "--check") != 0:
        print("\nPush blocked: the installed hooks do not match their tracked sources.")
        print("Run: python tools/verify/install_hooks.py --force")
        return 1

    if py("check_moved.py", "--block") != 0:
        print("\nPush blocked: something still points at a relocated path.")
        print("Update the reference, or record the file as a dated record in check_moved.py.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    if py("check_negatives.py", "--block") != 0:
        print("\nPush blocked: an undated universal negative.")
        print("Write 'none located as of <date>, searched as follows' — a universal negative")
        print("is falsified by any single future commit and nothing mechanical notices.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    if py("check_figures.py", "--block") != 0:
        print("\nPush blocked: an artifact count recorded in prose with no date.")
        print("Prefer measuring on demand. If it must be written down, date it -")
        print("the papers count went stale by 15 in a day, and nothing noticed.")
        return 1

    if py("check_checkers.py", "--block") != 0:
        print("\nPush blocked: a checker cannot fail, or nothing runs it.")
        print("This suite's characteristic defect is a check that could not have failed;")
        print("every instance so far was found by probing, never by reading.")
        return 1

    if py("check_invariants.py") != 0:
        return 1

    # The gating checkers. Each exit code captured on its own line — HK-1 was a `$?` read one call
    # too late, which meant check_modal had never blocked a push in its life.
    # ⚠ COUNT THE TUPLE, DO NOT TRUST A WORD. This comment said "The four checkers" and the tuple
    # held four; adding `check_encoding` made the sentence false in the same edit that would have
    # left it. A number written in prose beside the list it describes is a second copy.
    checker_fail = False
    for script in ("check_pov.py", "check_modal.py", "check_classes.py", "check_prose.py",
                   "check_encoding.py"):
        if py(script, "--block") != 0:
            checker_fail = True
    if checker_fail:
        return 1

    # Purity + SSOT. Safe at push in a way `lake build` is not: neither touches `sorry`, so neither
    # conflicts with stub-first. Build state stays CI's job at the PR.
    if py("batch.py", "decls", "--block") != 0:
        print("\nPush blocked: a declaration is missing its #print axioms entry or its ssot.json row.")
        print("Add the purity line, run the SJV sync, then re-push.")
        print("If the baseline is merely stale: python %s/batch.py decls --baseline"
              % os.path.dirname(SELF))
        return 1

    if py("check_hashes.py") != 0:
        print("\nPush blocked: build-script hash mismatch vs register.md.")
        print("A script changed without completing the four-step workflow")
        print("(change + version bump + PDF rebuild + hash update).")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    # ⚠ scan_pdfs lives in `scripts/`, NOT in this bundle. It is a BUILD-side tool (it checks
    # PDF assets and font registrations), and it moved with the build scripts on 2026-08-15
    # while this call kept looking here. Measured by /rely: `py("scan_pdfs.py") -> 2`, and
    # `pre_push` returns that, so EVERY push exited 2 with a bare [Errno 2] at the end of an
    # otherwise-green run. It failed CLOSED, which is why it is ordinary rather than bedrock —
    # but an unexplained exit 2 on a green run is precisely the shape that trains the
    # `--no-verify` reflex, which this project has already had fire twice.
    scan_exit = run(sys.executable, os.path.join(REPO, "scripts", "scan_pdfs.py"))

    # Routing + review signals, computed from the RANGES BEING PUSHED. This is the one call that
    # `batch.py` could not make correctly on its own (REL-1): it had only the working tree, which
    # is empty post-commit, so coverage was vacuous exactly at push time.
    rc = py("batch.py", "prepush", "--ranges", ",".join(ranges))
    if rc != 0:
        print("\nPush blocked: the pre-push pipeline reported a failure above.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        # ⚠ This line used to read "This gate is mirrored in CI: a local bypass only defers the
        # block to the PR." That is FALSE and was measured false 2026-08-10: grepping all four
        # workflows for any checker returns nothing — CI runs `lake build`. Telling the operator a
        # backstop exists when it does not is the worst possible failure mode for a deterrent, and
        # the true statement deters harder.
        print("⚠ CI re-runs these checkers on `main` (.github/workflows/verify.yml) but")
        print("  REPORT-ONLY — it publishes findings and does not fail the run. This hook is")
        print("  the last check that STOPS a change; bypassing it ships the change unchecked.")
        return 1

    return scan_exit


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else ""
    try:
        if what == "pre-commit":
            return pre_commit()
        if what == "pre-push":
            return pre_push(sys.stdin)
        print("hooks.py: expected 'pre-commit' or 'pre-push', got %r" % what)
        return 1
    except BrokenPipeError:
        # Output was truncated (`git push | head`). The GATE still decides; a closed pipe must
        # never be able to turn a block into a pass.
        try:
            sys.stdout.close()
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    sys.exit(main())
