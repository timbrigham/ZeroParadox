"""THE hook pipeline. The shell hooks are three-line shims that call in here.

WHY (Tim, 2026-08-10): *"the shell variants are legacy and should be retired... just the python
version should remain."* The pipeline had TWO partial implementations — a shell hook and
`batch.py` — and they measurably disagreed three ways (PIPE-1): what counts as reviewable
(`CLAUDE.md`), whether signals are required when nothing reviewable changed, and whether a
gate-exempt file recorded in a signal can stale it. They also checked disjoint things: the `/rely`
routing existed only in `batch.py`, the four checkers and the path resolver only in the hook.
Neither was the pipeline.

Shell and Python cannot share a module, so the only way to have one definition is for one of them
to go. The shell went. Everything it orchestrated was already Python (`check_paths`,
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
        rc = subprocess.call(list(cmd), cwd=REPO)
    except OSError as e:
        print("  hook: could not run %s (%s)" % (" ".join(cmd), e))
        return 1
    # ⚠⚠ RECORDED HERE, AFTER THE CHILD HAS ACTUALLY RUN, AND NOWHERE ELSE. `/rely` R3-1: the
    # previous version appended in `py()` on the line BEFORE the call, which records the INTENT to
    # launch rather than the launch -- "a receipt vs an invoice, and reconcile audits invoices".
    # Three one-line mutations went green against it: deleting the `run(... scan_pdfs)` call while
    # leaving its hand-written append (20 of 20, rc 0), and stubbing this function to `return 0`
    # (0 children, still 11 of 11 and 20 of 20, rc 0). Both are impossible from here: no
    # `subprocess.call` return, no entry. An OSError returns above without recording, because a
    # child that could not start did not run.
    EXECUTED.append((_invocation(cmd), rc))
    return rc


def _invocation(cmd):
    """Normalise a launched argv to (script basename, *args) — what the manifest names.

    `cmd` is (python, /abs/path/to/script.py, *args); the manifest speaks in basenames.
    """
    parts = list(cmd)
    for i, p in enumerate(parts):
        if str(p).endswith(".py") and i > 0:
            return (os.path.basename(str(p)),) + tuple(str(x) for x in parts[i + 1:])
    return tuple(str(x) for x in parts)


# ⚠⚠ WHAT ACTUALLY RAN, IN ORDER. `/rely` R2-1 measured why a generated manifest is not enough:
# generating the plan from the same TABLE the loop iterates still leaves the LOOP a separate
# statement, so replacing its iterable with `[]` printed `11 check(s): 11 BLOCK`, named all eleven
# rows, ran nothing and exited 0. Deriving one hand-written list from another moves the divergence;
# it does not remove it. The only thing that cannot be faked is an observation of the invocation
# itself, so every child this process launches appends here and `reconcile()` compares the manifest
# against THIS, not against the table it was printed from.
EXECUTED = []

# Every ref name seen on stdin this run, recorded where they are PARSED rather than where they are
# judged — see `reconcile`'s independent quarantine re-test (R4-2).
REFS_SEEN = []


def py(script, *args):
    # ⚠ No recording here — `run()` records, and only after the child actually returns (R3-1).
    return run(sys.executable, os.path.join(BASE, script), *args)


def _found(expect):
    """The (invocation, rc) whose argv starts with `expect`, or None. Prefix, so flags may vary."""
    n = len(expect)
    for inv, rc in EXECUTED:
        if tuple(inv[:n]) == tuple(expect):
            return inv, rc
    return None


def reconcile(phase, expected, refs=()):
    """Block unless every advertised check LAUNCHED and its exit code was ACCEPTABLE.

    `expected` is [(label, argv_prefix_or_None, ok_codes)]. `ok_codes` of None tolerates any code
    (a WARN row). A None argv marks a row handled inline; those are re-tested here INDEPENDENTLY
    where that is possible, and reported as unverified where it is not.

    ⚠⚠ THE SECOND HALF IS THE POINT, AND IT IS WHY THE DECISION LIVES HERE RATHER THAN BESIDE THE
    LOOP. `/rely` R4-1: `pre_commit` was two statements — launch, then score — and `reconcile`
    observed only the first. Replacing the scoring block with `if False: pass` and forcing
    `check_pov` to exit 1 gave: the finding printed, `11 of 11` reconciled, and the commit MADE.
    Round 2's `_mode` closes a different route (widening `ok_codes`) and cannot see the scoring
    deleted, because it computes `BLOCK` correctly over a column nothing reads. So the verdict is
    now DERIVED from the recorded exit codes: delete the scoring and the block still happens,
    because there is no longer a second place where the decision lives.
    """
    missing, bad, inline = [], [], []
    for label, argv, ok_codes in expected:
        if not argv:
            inline.append(label)
            continue
        hit = _found(argv)
        if hit is None:
            missing.append(label)
            continue
        _inv, rc = hit
        if ok_codes is not None and rc not in ok_codes:
            bad.append("%s (exit %d)" % (label, rc))

    named = sum(1 for _l, argv, _o in expected if argv)
    print("")
    print("  manifest reconciliation: %d of %d advertised check(s) launched; %d bad exit(s)%s"
          % (named - len(missing), named, len(bad),
             ("; %d inline row(s): %s" % (len(inline), ", ".join(inline))) if inline else ""))

    # ⚠ R4-2: `quarantine` was the only push row with NO observer — deleting its inline branch let
    #   a `private/*` ref push green while the manifest printed the row's name. Re-tested here
    #   INDEPENDENTLY rather than observed, because a second enforcement survives deleting the
    #   first and an observer of a deleted branch sees nothing.
    # Both shapes `parse_refs` refuses: a quarantined LOCAL branch, and any REMOTE ref under
    # a `private/` path. Matching one and not the other would re-open half the hole.
    leaked = sorted({r for r in refs
                     if r.startswith("refs/heads/private/") or "/private/" in r})
    if leaked:
        print("")
        print("%s BLOCKED — a private/* ref reached the push: %s" % (phase.upper(), ", ".join(leaked)))
        print("These branches never leave this machine. This is the second of two checks on that")
        print("property; if the first did not fire, that is itself a defect to report.")
        return 1

    if missing or bad:
        print("")
        if missing:
            print("%s BLOCKED — the manifest advertised %d check(s) that never ran: %s"
                  % (phase.upper(), len(missing), ", ".join(missing)))
            print("This is the gate lying about itself, which is worse than any finding it could")
            print("report. Do not bypass: fix the wiring so the advertised check executes.")
        if bad:
            print("%s BLOCKED — %d advertised check(s) exited badly: %s"
                  % (phase.upper(), len(bad), ", ".join(bad)))
            print("Derived from the recorded exit codes, not from a second list beside the loop,")
            print("so deleting the scoring does not delete the block.")
        return 1
    return 0


def recorded(script, *args):
    """Run a push-time checker WITH `--record`, and keep exit 2 distinct from exit 1.

    ⚠ EXIT 2 IS NOT EXIT 1. A checker that PASSED but could not write its verdict leaves the key
    MISSING, so the ledger refuses the push with nothing local explaining why — while the operator
    has just watched every check go green. Collapsing the two prints "the check failed" over a
    check that did not fail, which is the shape that trains the `--no-verify` reflex.

    ⚠ WHY THE PUSH PATH RECORDS AT ALL. `--record` was wired into `pre_commit` and not here, so the
    nine checkers that run only at push earned keys ONLY when someone ran them by hand. They went
    STALE at every commit and stayed that way, which meant the skip helped exactly the five that
    needed it least and the gate was satisfiable only after a manual sweep. Measured 2026-08-23:
    15 of 24 steps needed a re-run on a tree whose checks had all just passed.
    """
    rc = py(script, *(args + ("--record",)))
    if rc == 2:
        print("\n⚠ %s ran but its verdict was NOT RECORDED." % script)
        print("  The ledger will report this step MISSING and refuse the push. This is a RECORDING")
        print("  failure, not a check failure — the check itself may have passed. Fix the ledger")
        print("  connection; do not go looking for a defect in the corpus.")
    return rc


def git_out(*args):
    try:
        r = subprocess.run(["git"] + list(args), cwd=REPO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        return r.returncode, (r.stdout or "")
    except OSError:
        return 1, ""


# ------------------------------------------------------------------ pre-commit

# ⚠⚠ ONE TABLE DRIVES BOTH THE MANIFEST AND THE LOOP, AND THAT IS THE WHOLE POINT OF ITS SHAPE.
# Until 2026-08-30 the printed plan was a hand-written SECOND COPY of the execution list, and
# `/rely` RLY27-1 measured what that buys: with the entire checker loop DELETED, this hook still
# printed `plan 11 check(s): 11 BLOCK, 0 advisory`, listed all eleven rows by name, ran nothing,
# and exited 0 -- and `check_checkers --block` reported `violations: 0` over that neutered gate,
# because its "is invoked" property is satisfied by the pre-push call site and cannot see a
# commit-time call disappear. The realistic variant reproduced too: dropping one entry from the
# tuple while leaving its manifest row gave eleven advertised, ten executed, exit 0.
# A manifest that CAN disagree with the loop is a claim about the loop, not a description of it.
#
# Each row is (label, argv, ok_codes, description). `ok_codes` is the exit codes that are NOT a
# finding -- see check_paths below for the one entry that needs more than (0,).
PRE_COMMIT_CHECKS = [
    ("check_pov", ("check_pov.py",), (0,),
     "POV claims declare a KIND; DENIALs never allowed"),
    ("check_modal", ("check_modal.py",), (0,),
     "modal claims carry a measurement or a reduction"),
    ("check_classes", ("check_classes.py",), (0,),
     "a new requirements class records a degeneracy verdict"),
    ("check_prose", ("check_prose.py",), (0,),
     "prose caps: block size, docstring vs decl, gloss labels"),
    # ⚠ AT COMMIT, NOT ONLY AT PUSH, AND FOR A REASON THE OTHER FOUR DO NOT SHARE. Double-encoded
    # text is valid UTF-8, so it survives every other check, renders plausibly in a diff, and the
    # window in which the author still knows which write did it is minutes long.
    ("check_encoding", ("check_encoding.py",), (0,),
     "BOM + undecodable BLOCK; suspected double-encoding WARNS"),
    # ⚠⚠ THE SIX BELOW WERE PUSH-ONLY UNTIL 2026-08-30, AND THAT WAS A HOLE, NOT A SAVING.
    # gitRobot admits 20 keys for a push and 18 for a commit; this hook emits 11. The other six ran
    # only in `pre_push`, against the TIP -- so a second commit silently invalidated the first, and
    # no intermediate commit could EVER reach the bar through ordinary work. Measured: a 2-commit
    # range read 11/19 with both commits made through the full pipeline, hook green each time.
    # The remedy on offer was `squash`, i.e. rewriting history on every push to satisfy a rule
    # that exists BECAUSE intermediate commits are fetchable, bisectable and citable forever.
    # ⚠ They already BLOCK at push, so this adds NO new failure class -- same argument
    # `pre_commit` makes for the original five, one paragraph down. Cost 16.1s (~5.9s -> ~22s).
    # ⚠ NOT the whole gap: `build`, `check_checkers`, `check_claude_md`, `check_hashes`,
    # `claim_review`, `guards` and `pdf_coupling` still have no pre-commit producer. Narrowed, not
    # closed (RLY27-5).
    #
    # ⚠⚠ EXIT 3 IS "SKIPPED PART OF MY SCOPE", NOT A FINDING -- `check_paths.EXIT_SKIPPED`, and
    # `pre_push` has always allowed it (see the File-reference check below). When these six were
    # added here on 2026-08-30 the loop treated every non-zero as a violation, so in any clone or
    # worktree WITHOUT a built `.lake` the pinned Mathlib is absent, `check_paths` returns 3, and
    # every commit was refused naming a defect that does not exist -- with `--no-verify`, which
    # skips all eleven, as the only escape. Measured by `/rely` RLY27-7 in a fresh worktree.
    # ⚠ SCOPE IS MARKDOWN + LEAN, AND SAYING MORE IS THE WORSE ERROR. Round 1 (RLY27-4) found this
    # row UNDERSTATED its scope; the repair overshot and claimed `scripts/**.py` too, which round 2
    # (R2-3) measured false: the only `scan()` calls that can set `failed` are markdown and Lean,
    # `tracked_scripts()` is reached from the selftest pin and `--claim` alone, the build-script
    # block prints "INFORMATIONAL: does not fail the run", and the ledger subject list is
    # `tracked_markdown() + tracked_lean()`. Live: 10 hits under `scripts/`, exit 0. An overstated
    # manifest is worse than an understated one -- it is a claim of coverage nobody has.
    ("check_paths", ("check_paths.py",), (0, 3),
     "every repo-relative reference in tracked markdown and Lean resolves "
     "(3 = scope skipped for want of a built .lake, not a finding; scripts/ scanned INFORMATIONALLY)"),
    ("check_moved", ("check_moved.py",), (0,),
     "nothing points at a path that was relocated"),
    ("check_negatives", ("check_negatives.py",), (0,),
     "a universal negative carries a date or a search record"),
    ("check_figures", ("check_figures.py",), (0,),
     "an artifact count carries a date, or is measured on demand"),
    ("check_invariants", ("check_invariants.py",), (0,),
     "Engineer's Takes filled; LEAN_CUSTOM_REGISTRY count matches"),
    # ⚠ `decls` lives in `batch.py` behind a subcommand rather than being a `check_*.py`, which is
    #   the only reason its argv has two elements. Same handling in every other respect.
    ("decls", ("batch.py", "decls"), (0,),
     "every new declaration has #print axioms + an ssot.json row"),
]

# ⚠ THE MODE COLUMN IS DERIVED, NOT ASSERTED. `/rely` R2-2: it was the literal "BLOCK" on every
# row, so widening an entry's `ok_codes` to swallow exit 1 left all eleven rows still advertising
# BLOCK while nothing could block. A row blocks exactly when the universal failure code is not
# tolerated, so that is what the column now computes.
def _mode(ok_codes):
    return "BLOCK" if 1 not in ok_codes else "WARN"


# The manifest is GENERATED from the table above -- but see `reconcile()`: generation alone only
# moves the divergence from "two lists" to "a list and a loop". The manifest is BINDING because
# every advertised row is checked against what actually launched.
PRE_COMMIT_PLAN = [(label, _mode(ok), desc) for label, _argv, ok, desc in PRE_COMMIT_CHECKS]

PRE_PUSH_PLAN = [
    ("hooks armed", "BLOCK", "the installed hooks match their tracked sources"),
    ("quarantine", "BLOCK", "private/* branches never reach a remote"),
    ("guards", "BLOCK", "every enumerated ROUTE to a guarded property still behaves"),
    ("routing control", "BLOCK", "the behavioural mutation probe: 9 neuters of the routing routes, "
                                 "each required to turn its named ROW red (~225s; fails CLOSED on a "
                                 "moved anchor). Does NOT yet cover RLY28-1 — a tenth mutation is owed"),
    ("check_paths", "BLOCK", "every repo-relative reference in tracked markdown resolves"),
    ("check_claude_md", "BLOCK", "CLAUDE.md shape contract: rooted paths resolve, named checkers exist "
                                 "(3 legs still PENDING — it says so on every run)"),
    ("check_moved", "BLOCK", "nothing points at a path that was relocated"),
    ("check_negatives", "BLOCK", "a universal negative carries a date or a search record"),
    ("check_figures", "BLOCK", "an artifact count carries a date, or is measured on demand"),
    # ⚠ WARN, NOT BLOCK, AND THE RETIREMENT IS THE REASON (Tim, 2026-08-23). The freeze comparison
    # is from the topology that preceded the independent-git-spaces rewrite, so its snapshot cannot
    # correspond to anything now and it fails PERMANENTLY — measured, 5 failing subjects on a clean
    # tree. The ledger retired it as a gate the same day (`actions: []`, stated reason) while keeping
    # it REGISTERED so it still records. This row said BLOCK for eight commits after that, so the
    # hook refused every push the ledger was willing to allow: a manifest telling the truth about a
    # gate the server had already stood down.
    # ⚠ It still RUNS and still RECORDS. What is retired is the freeze comparison's authority to
    # stop a push, never the emitter — `claim_review` is emitted by this file alone, and killing the
    # run would leave that key permanently MISSING and block every push forever, which is strictly
    # worse than the failure being removed.
    ("check_frozen", "WARN", "RETIRED as a gate (dead topology) — still runs, still records; "
                             "claim_review rides on it and must keep being emitted"),
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
    # ⚠ "/rely routing" is no longer one mode: the logic and exemption-switch legs BLOCK, the
    # routed-prose leg WARNS (downgraded 2026-08-21, rung 5). Said here too, because a manifest that
    # over-states at ONE entry point is the same defect as over-stating at all four.
    ("batch prepush", "BLOCK", "trigger 5, the three review signals, and /rely routing — logic and "
                               "exemption switches BLOCK, routed prose WARNS"),
]


def _bind_push_modes(plan, expect):
    """Replace each push row's asserted mode with the one its tolerances actually imply.

    ⚠⚠ R3-2, closed here rather than by editing twenty strings. The column was 20 literal
    "BLOCK"s, so deleting a single `return 1` left a row advertising a block it no longer
    performed — measured three times, once against the row whose own text reads "its exit code
    becomes the hook's". Now the same `ok_codes` that `reconcile` enforces also decides what the
    row is allowed to CLAIM, so the manifest and the enforcement cannot disagree: there is one
    fact and two readers of it.
    """
    tol = {label: ok for label, _argv, ok in expect}
    out = []
    for label, _asserted, desc in plan:
        ok = tol.get(label, (0,))
        out.append((label, "WARN" if ok is None or 1 in ok else "BLOCK", desc))
    return out

# ⚠⚠ WHAT EACH PUSH ROW MUST ACTUALLY LAUNCH. `/rely` R2-4: the commit manifest was made binding
# and this one was left a hand-written second copy -- the same defect fixed at ONE of its TWO
# sites, which is the recurring shape (`SH-3`) this project keeps paying for. Deleting the
# `check_hashes` call site, and separately `guards.py`'s, left the manifest printing every row it
# prints today (measured 2026-08-30) and naming both, exit 0. `guards.py` is the exemption-surface
# control that runs FIRST precisely
# because a green checker over a holed surface is a false zero -- so its silent disappearance is
# the worst single case in the file.
#
# `None` marks a row handled INLINE with no child process. `reconcile` reports those as unverifiable
# rather than counting them as satisfied: an honest gap beats a false tick.
# ⚠⚠ THE FLAGS ARE PART OF THE EXPECTATION, NOT DECORATION. `/rely` R3-3: matching on the script
# name alone let a four-character edit disable the check while reconciliation still reported
# success -- strip `--block` from the commit loop and eleven children launch, findings print, and
# the run exits 0. That was measured on real violations, not hypothetically: a BOM in `GUIDE.md`
# gives `check_encoding` exit 0 without `--block` and exit 1 with it; a theorem with no
# `#print axioms` entry gives `batch.py decls` exit 0 without and exit 1 with. The flag IS the
# enforcement, so an expectation that ignores it is checking the wrong thing.
# Third element is `ok_codes`: the exit codes that are NOT a finding. `None` means "any code
# tolerated" and is reserved for the one row the manifest itself declares WARN. Everything else
# names its tolerances explicitly, so the push verdict is derived from recorded exit codes rather
# than from twenty hand-written `return 1` statements (R4-1 at the push site; R3-2's real fix).
PRE_PUSH_EXPECT = [
    ("hooks armed", ("install_hooks.py", "--check"), (0,)),
    # ⚠ Launches nothing — but NOT unobserved any more: `reconcile` re-tests the property itself
    #   from `REFS_SEEN`. R4-2 measured the hole: delete the inline branch and a `private/*` ref
    #   pushed green while the manifest printed this row's name.
    ("quarantine", None, None),
    ("guards", ("guards.py", "--record"), (0,)),
    ("routing control", ("probe_routing_behavioural.py",), (0,)),
    # ⚠ 3 = scope skipped for want of a built .lake, tolerated at both phases (RLY27-7).
    ("check_paths", ("check_paths.py", "--all", "--warn-private", "--record"), (0, 3)),
    ("check_claude_md", ("check_claude_md.py", "--record"), (0,)),
    ("check_moved", ("check_moved.py", "--block", "--record"), (0,)),
    ("check_negatives", ("check_negatives.py", "--block", "--record"), (0,)),
    ("check_figures", ("check_figures.py", "--block", "--record"), (0,)),
    # ⚠ The manifest says WARN and means it: RETIRED as a gate (dead topology), still runs, still
    #   records, because `claim_review` rides on its emitter. Any exit is tolerated HERE, and that
    #   is the one row where `None` is correct rather than lazy.
    ("check_frozen", ("check_frozen.py", "--record"), None),
    ("check_checkers", ("check_checkers.py", "--block", "--record"), (0,)),
    ("check_invariants", ("check_invariants.py", "--record"), (0,)),
    ("check_pov", ("check_pov.py", "--block", "--record"), (0,)),
    ("check_modal", ("check_modal.py", "--block", "--record"), (0,)),
    ("check_classes", ("check_classes.py", "--block", "--record"), (0,)),
    ("check_prose", ("check_prose.py", "--block", "--record"), (0,)),
    ("check_encoding", ("check_encoding.py", "--block", "--record"), (0,)),
    ("decls", ("batch.py", "decls", "--block", "--record"), (0,)),
    ("check_hashes", ("check_hashes.py", "--record"), (0,)),
    ("scan_pdfs", ("scan_pdfs.py",), (0,)),
    ("batch prepush", ("batch.py", "prepush"), (0,)),
]


def pre_commit():
    """The eleven checkers BLOCK; nothing here warns.

    The stub-first protocol commits `sorry`-stubbed files on purpose, so BUILD state must never
    gate here — and none of these reads `sorry`, the build, or completeness. They are
    baselined, sit at zero new, and already block at push, so blocking here adds no new failure
    class; it moves an identical, already-mandatory failure earlier, where the fix is cheap.

    ⚠⚠ SIX WERE ADDED 2026-08-30 SO THAT EVERY COMMIT EARNS ITS OWN ADMISSION KEYS. Recording
    them only in `pre_push` meant they were keyed to the TIP, so an intermediate commit could
    never satisfy the commit bar and `can_push` refused every multi-commit range. The fix is
    HERE rather than in `batch.py precommit` for the reason the comment below already gives:
    that command is MANUAL, and the path that fires on every commit is this hook."""
    report.banner("pre-commit pipeline", [
        ("entry", ".git/hooks/pre-commit -> hooks.py pre_commit"),
        ("scope", "the WORKING TREE as it stands (checkers scan the corpus on disk)"),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
        ("not run", "lake build / purity / ssot — stub-first commits incomplete work on purpose"),
    ])
    report.plan(PRE_COMMIT_PLAN)

    failed = []
    # ⚠⚠ RECORDING BELONGS HERE, NOT IN `batch.py precommit` — measured 2026-08-23 and it was a
    # silent miss. `batch.py precommit` is a MANUAL command; the path that actually fires on every
    # commit is this hook. Wiring `--record` there meant every ledger record came from someone
    # typing the command, never from a commit — so the recorded basis was an index tree that no
    # commit ever had (`cbac5acb` recorded, `HEAD^{tree}` = `292ac861`), and six to fifteen paths
    # per step read STALE for content nobody had changed. Caught by mcp-mayhem, REQ-1.
    #
    # ⚠ INDEX, NOT HEAD. Git has already prepared the index by the time this hook runs, so the
    # staged tree IS the tree the pending commit will carry. HEAD is still the PARENT here.
    # ⚠⚠ ASSIGNMENT, NOT `setdefault` — changed 2026-08-30, `/rely` RLY27-3. `setdefault` let the
    # CALLER'S environment win: exporting `ZPLEDGER_RUN=whatever-i-say` and `ZPLEDGER_BASIS=HEAD`
    # both reached every checker unchanged, which defeats V9's run-id provenance at the commit gate
    # and, under `HEAD`, makes `ledger_subjects` drop exactly the paths just staged — the ledger
    # then reports narrowed coverage WITHOUT blocking. `pre_push` has always used assignment, for
    # the reason stated at its own call site: the environment here could only ever be wrong.
    os.environ["ZPLEDGER_BASIS"] = "INDEX"
    os.environ["ZPLEDGER_RUN"] = "pre-commit"
    for label, argv, ok_codes, _desc in PRE_COMMIT_CHECKS:
        rc = py(*argv, "--block", "--record")
        # ⚠ EXIT 2 IS "COULD NOT BE RECORDED", NOT "FAILED". A checker that ran and could not reach
        # the ledger produced no key, so the commit must not proceed as though it had — but the
        # reader needs the outage named, not a phantom finding.
        # ⚠ A checker MISSING FROM DISK also surfaces as 2 today and is reported with the same
        #   wording, which fails closed but diagnoses wrong (RLY27-6, ledgered, not fixed here).
        if rc == 2:
            failed.append("%s (ran; verdict NOT RECORDED — no key exists for this content)"
                          % label)
        elif rc not in ok_codes:
            failed.append("%s (exit %d)" % (label, rc))

    # ⚠⚠ THE MANIFEST IS BINDING. Every row above named a child; this is where we confirm each one
    # actually launched. Run BEFORE the findings report, because "the gate did not run" outranks
    # "the gate found nothing" -- a neutered loop produces an empty `failed` list, which is exactly
    # what a clean run produces.
    # ⚠ The expectation carries `--block --record`, not just the script name (R3-3): those flags
    #   ARE the enforcement, and a name-only match passes a run that launched every child with the
    #   teeth removed.
    # ⚠ `ok_codes` travels with the row, so the accept/reject decision is made from the RECORDED
    #   exit code. Exit 2 stays distinguishable: it is not in any row's `ok_codes`, so it blocks
    #   here too, and the loop above has already named it as a recording failure rather than a
    #   finding.
    if reconcile("commit",
                 [(label, tuple(argv) + ("--block", "--record"), ok)
                  for label, argv, ok, _d in PRE_COMMIT_CHECKS]):
        return 1

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
        # ⚠ Recorded BEFORE and INDEPENDENTLY of the quarantine test below, so `reconcile`'s
        #   second check on the same property survives that branch being deleted (R4-2).
        REFS_SEEN.append(local_ref)
        REFS_SEEN.append(remote_ref)
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
    report.plan(_bind_push_modes(PRE_PUSH_PLAN, PRE_PUSH_EXPECT))

    # ⚠ `gatelock` RETIRED 2026-08-23 — deliberately, not dropped. It froze reviewed paths with the
    # read-only bit while a gate round ran. Three reasons it went: the worktree rule makes the
    # shared-tree concurrent-edit hazard structural rather than policed; its own header recorded the
    # bypass it could not close (git unlinks and recreates, so `checkout`/`reset --hard` silently
    # un-froze a locked path, measured); and the harm it aimed at is already DETECTED downstream,
    # because editing a reviewed file changes its SHA-256 and stales the signal at this very gate.
    # Prevention by an advisory attribute, replaced by detection that cannot be walked past.

    # ⚠ THE CHECKERS BELOW ARE ONLY WORTH THEIR EXIT CODES IF THEY CANNOT BE WALKED AROUND.
    # `guards.py` plants a known violation and then tries EVERY enumerated route to suppressing it.
    # It runs here, before the checkers it protects, because a green checker whose exemption surface
    # has a new hole is a false zero — and this project's own record is that a false zero costs more
    # than a red one. ~10s, once per push.
    # ⚠ SET, NOT `setdefault`, AND THE DIFFERENCE IS A WRONG-TREE RECORD. At push the basis is
    # unambiguous — the tip being pushed, which is HEAD — so a value inherited from the caller's
    # environment could only be wrong, and would attach every verdict on this run to a tree nobody
    # examined. `run.id` comes from the pipeline by V9 and is refused if absent; pre_commit sets
    # both and pre_push set neither, so every push-time record was refused with
    # "run.id is required ... not the caller's imagination" and the whole point of wiring
    # `--record` here was lost at the first checker.
    os.environ["ZPLEDGER_BASIS"] = "HEAD"
    os.environ["ZPLEDGER_RUN"] = "pre-push"

    print("\n=== Property guards (exemption surface) ===")
    _rc_guards = recorded("guards.py")
    if _rc_guards == 2:
        return 1                      # `recorded` already said why; do not also blame the guard
    if _rc_guards != 0:
        print("\nPush blocked: a guarded property can be walked, or a guard left files mutated.")
        print("Read the FAIL lines above — each names the ROUTE. Fix the route, do not skip the run.")
        return 1

    # ⚠⚠ THE CONTROL FOR THE TWO ROUTES ABOVE, AND UNTIL NOW NOTHING RAN IT. `guards.py` green is
    # not evidence: ROUTE 3 and ROUTE 5 have been defeated FOUR times (whole-file substring →
    # windowed substring → AST shape → AST name), and each repair moved the hole rather than
    # closing it, because every attempt asked "does the consumer's SOURCE look like it honours the
    # flag?" — a static approximation with an escape every time. `probe_routing_behavioural.py`
    # asks the behavioural question instead: it drives the consumer with synthetic rows in its own
    # detached worktree and requires the named ROW to go red. It was written, it works, and it had
    # ZERO automatic callers — so the one artifact that can falsify the guard ran only when a human
    # remembered. Measured 2026-08-24 by `/rely`: 9 of 9, 225s, and it was the only thing in the
    # layer that reacted to a live neuter of `cmd_prepush`.
    #
    # ⚠ IT ASSERTS THE ROW, NOT THE EXIT CODE, and it fails CLOSED — a mutation whose anchor has
    # moved reports `MUTATION DID NOT APPLY` rather than passing, so a refactor that slides the
    # anchor blocks the push instead of silently retiring the control.
    #
    # ⚠ `RLY28-1` IS CLOSED AT THE SHAPE, NOT HERE. The router's producer now records its own count
    # in `batch`'s verdict registry and the push verdict is read from that, so multiplying the
    # returned count by zero at the call site — the neuter that took the gate from exit 1 to exit 0
    # on 2026-08-23 while three FAIL rows sat on screen — is now INERT rather than merely
    # detectable. Two mutations here pin both directions: annihilating the return must stay GREEN,
    # and deleting the producer's record must go RED. What THIS wiring closes is `RLY29-1`: the
    # control had no caller, so nothing ever ran the one artifact that can falsify the guard.
    print("\n=== Routing control (behavioural mutation probe) ===")
    _rc_probe = py("probe_routing_behavioural.py")
    if _rc_probe != 0:
        print("\nPush blocked: the routing control did not behave as required.")
        print("Each row above names the mutation and the ROW that had to go red. A row reading")
        print("MUTATION DID NOT APPLY means the anchor moved — the control is no longer testing")
        print("what it claims, which is a fail-open in the making. Fix the control, never skip it.")
        return 1

    print("\n=== File-reference check ===")
    # ⚠ 3 means "skipped part of my scope", not failure — see check_paths.EXIT_SKIPPED.
    # Locally the pinned Mathlib checkout is present, so this is normally 0; the branch
    # exists so a developer without a built .lake is not blocked by an unrunnable check.
    _rc_paths = recorded("check_paths.py", "--all", "--warn-private")
    if _rc_paths not in (0, 3):
        print("\nPush blocked: a repo-relative reference in TRACKED markdown does not resolve.")
        print("Fix the path, or word the line so the resolver skips it (e.g. 'no longer exists').")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1
    print("===========================")

    print("\n=== CLAUDE.md shape contract ===")
    # ⚠ THE COMMENT HERE SAID "CALLED WITHOUT `--record`, DELIBERATELY" WHILE THE LINE BELOW PASSED
    # `--record` AND THE KEY EXISTED IN THE LEDGER. Corrected 2026-08-30, `/rely` RLY27-9: the
    # ledger support was added and the comment describing its absence was left behind. It IS
    # recorded and it IS audited. Kept as a warning rather than deleted, because a comment that
    # outlived its subject is how "wiring it in is the follow-up" reads as still-open work.
    # ⚠ Its manifest declares 3 PENDING legs on every run. A clear result here is evidence
    # about two legs, never about the shape contract as a whole.
    if py("check_claude_md.py", "--record") != 0:
        print("\nPush blocked: CLAUDE.md names a path or a checker that does not exist.")
        print("Fix the pointer. Body: tools/process/claude-md-maintenance.md.")
        return 1
    print("================================")

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

    if recorded("check_moved.py", "--block") != 0:
        print("\nPush blocked: something still points at a relocated path.")
        print("Update the reference, or record the file as a dated record in check_moved.py.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    if recorded("check_negatives.py", "--block") != 0:
        print("\nPush blocked: an undated universal negative.")
        print("Write 'none located as of <date>, searched as follows' — a universal negative")
        print("is falsified by any single future commit and nothing mechanical notices.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1

    if recorded("check_figures.py", "--block") != 0:
        print("\nPush blocked: an artifact count recorded in prose with no date.")
        print("Prefer measuring on demand. If it must be written down, date it -")
        print("the papers count went stale by 15 in a day, and nothing noticed.")
        return 1

    # ⚠ THE ACCEPTED-DEFECT BASELINES ARE FROZEN (2026-08-22). The ordinary path already refuses —
    # `--baseline` on any of the six exits 2 with an explanation — so this is the backstop for a
    # HAND EDIT, which no refusal can intercept. It prints the backlog total on every run, clear or
    # not, because a debt figure that surfaces only on failure cannot show progress.
    # ⚠ RUN AND RECORD, DO NOT BLOCK — see the manifest row. `--block` is deliberately NOT passed:
    # the freeze comparison is retired (dead topology), and the run is kept because `claim_review`
    # is emitted here and nowhere else. A downgraded gate must get LOUDER rather than quieter, so
    # the outcome is printed on EVERY push, clear or not, instead of surfacing only on failure.
    _rc_frozen = py("check_frozen.py", "--record")
    if _rc_frozen == 2:
        print("\n⚠ check_frozen ran but its verdict was NOT RECORDED — claim_review is emitted")
        print("  here and nowhere else, so a missing record blocks the push at the ledger.")
        return 1
    print("  check_frozen: WARN-only (retired 2026-08-23, dead topology). Ran and recorded;")
    print("  claim_review emitted. A finding here is a reading list, not a block.")

    if recorded("check_checkers.py", "--block") != 0:
        print("\nPush blocked: a checker cannot fail, or nothing runs it.")
        print("This suite's characteristic defect is a check that could not have failed;")
        print("every instance so far was found by probing, never by reading.")
        return 1

    if recorded("check_invariants.py") != 0:
        return 1

    # The gating checkers. Each exit code captured on its own line — HK-1 was a `$?` read one call
    # too late, which meant check_modal had never blocked a push in its life.
    # ⚠ COUNT THE TUPLE, DO NOT TRUST A WORD. This comment said "The four checkers" and the tuple
    # held four; adding `check_encoding` made the sentence false in the same edit that would have
    # left it. A number written in prose beside the list it describes is a second copy.
    checker_fail = False
    for script in ("check_pov.py", "check_modal.py", "check_classes.py", "check_prose.py",
                   "check_encoding.py"):
        if recorded(script, "--block") != 0:
            checker_fail = True
    if checker_fail:
        return 1

    # Purity + SSOT. Safe at push in a way `lake build` is not: neither touches `sorry`, so neither
    # conflicts with stub-first. Build state stays CI's job at the PR.
    if py("batch.py", "decls", "--block", "--record") != 0:
        print("\nPush blocked: a declaration is missing its #print axioms entry or its ssot.json row.")
        print("Add the purity line, run the SJV sync, then re-push.")
        print("If the baseline is merely stale: python %s/batch.py decls --baseline"
              % os.path.dirname(SELF))
        return 1

    if recorded("check_hashes.py") != 0:
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
    # ⚠ No hand-written append: `run()` records it, like every other child. The hand-patch that
    #   used to sit here was exactly the R3-1 defect -- delete the call below and the append
    #   claimed the row anyway.
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

    # ⚠⚠ LAST, AND ONLY ON THE OTHERWISE-GREEN PATH. Every branch above returns 1 before reaching
    # here, so a short run is a REPORTED failure, not a silent one; reconciling early would report
    # rows "missing" that were simply never reached. What this catches is the dangerous case: a
    # green run whose manifest advertised a check that no longer launches.
    if reconcile("push", PRE_PUSH_EXPECT, refs=REFS_SEEN):
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
