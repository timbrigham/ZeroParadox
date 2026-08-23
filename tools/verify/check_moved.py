"""Fail when anything still points at a path that was relocated.

WHY THIS AND NOT A TOMBSTONE. The 2026-08-15 migration left a shim at every old executable path,
which is useful to a human who runs one. It is useless to the far larger set of references that are
never executed: hook shims, command briefs, usage examples, a docstring naming a sibling tool. Those
fail silently or not at all. VERIFICATION_BUILDOUT Phase 2a says it directly - "what actually proves
the migration is complete is a grep that fails when anything still points at a relocated path" - and
notes the human-visible half is the small half.

It generalizes past this one migration. `historical/` was retired, `HostVerdict.lean` reverted,
notes get archived. Add a row to MOVED whenever something relocates, and the check does the rest.

    python tools/verify/check_moved.py            # WARN  (advisory, exit 0)
    python tools/verify/check_moved.py --block    # BLOCK (exit 1 on any live stale reference)

DATED RECORDS ARE EXEMPT, AND THAT IS NOT A LOOPHOLE. `.claude-local/notes/`, `archive/`, and
register.md's Notes column record the tree AS IT STOOD. Rewriting them to name today's paths would
falsify a historical record - a changelog entry saying a checker lived at tools/verify/ in v1.17,
when it did not, is worse than a stale path. The project's standing rule is to verify at the
artifact, never from a note; these surfaces are notes.
"""
import io
import os
import re
import sys

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
SELF = common.self_rel(__file__)

# old path (regex, anchored on the literal old location) -> where it went.
# ⚠ BOTH SEPARATORS, BUILT IN. `SEP` is `[\\/]`, not a literal `/`.
#
# Every pattern used `/` until 2026-08-15, which made Windows-style references INVISIBLE:
# `.claude-local\PDF_Rendering_Standards.md` and `.claude-local\build_zpa.py` sat stale in the
# EDITORIAL GATE BRIEF while this checker reported zero stale references. The reviewer would have
# been sent to two files that no longer exist. Paths here get written by hand on Windows and by
# tools with POSIX separators, so knowing one of them is a detector with a blind half.
#
# ⚠ Do NOT post-process the patterns to add this. The first fix chained two `.replace` calls and
# the second mangled the `[\\/]` the first had just inserted — seven controls failed at once.
SEP = r"[\\/]"
_VERIFY = ("hooks batch report guards vendored gate_round debaseline selfheal ship "
           "check_classes check_hashes check_invariants check_modal check_paths check_poles "
           "check_pov check_prose check_release_ready").split()
MOVED = [(r"\.claude-local" + SEP + r"%s\.py" % n, "tools/verify/%s.py" % n) for n in _VERIFY]
MOVED += [(r"\.claude-local" + SEP + re.escape(n), "tools/verify/%s" % n) for n in
          ("class_baseline.txt", "modal_baseline.txt", "pov_baseline.txt", "prose_baseline.txt",
           "decl_baseline.txt", "vendored_files.txt",
           "proposed_pre_commit_hook.sh", "proposed_pre_push_hook.sh")]
MOVED += [(r"\.claude-local" + SEP + re.escape(n), "scripts/%s" % n) for n in
          ("zp_utils.py", "scan_pdfs.py", "PDF_Rendering_Standards.md")]
# ⚠ ENUMERATED, NOT GLOBBED. `\.claude-local/build_.*\.py` looks right and is wrong: five build
# scripts (build_bottom_matrix, build_claim_map, build_padicbridge, build_zp_reals_companion,
# build_zpj_bridge_companion) were never mirrored and legitimately stayed private, so a glob
# reports their own correct self-references as stale. Caught on this checker's first run. A rule
# that fires on correct code is the cry-wolf shape this project says to narrow, not tolerate.
_MOVED_BUILDS = sorted(
    f for f in os.listdir(os.path.join(REPO, "scripts"))
    if f.startswith("build_") and f.endswith(".py")
) if os.path.isdir(os.path.join(REPO, "scripts")) else []
MOVED += [(r"\.claude-local" + SEP + re.escape(f), "scripts/" + f) for f in _MOVED_BUILDS]
MOVED += [(r"\.claude-local" + SEP + "commands" + SEP, ".claude/commands/")]

RULES = [(re.compile(pat), dest) for pat, dest in MOVED]

# ⚠ GLOBBED REFERENCES — `MIG-2`, and it is the hole this checker was built to have. Every rule above
# matches a CONCRETE filename, so prose that names a family with a wildcard is invisible. Measured
# 2026-08-15: `--block` exited 0 while `.claude-local/proposed_pre_*_hook.sh` sat stale in the defect
# ledger, and again 2026-08-16 on `.claude-local/build_zp*.py` in a PUBLISHED gate brief — which also
# called `scripts/` a mirror it stopped being. Both would have sent a reviewer to files that do not
# exist.
#
# ⚠ THE 14 CONTROLS THIS CHECKER SHIPPED WITH ALL PLANT CONCRETE PATHS, so the blind half was never
# probed. A must-fire control in the wrong shape passes and teaches you nothing.
#
# The rule stays NARROW deliberately: it reports the reference as needing a look rather than
# resolving it to a destination. Resolving is impossible — a glob may cover files that moved AND
# files that legitimately stayed private, which is exactly why the concrete rules above are
# enumerated rather than globbed (see `_MOVED_BUILDS`).
#
# ⚠⚠ ENUMERATED BY FAMILY, NOT "ANY WILDCARD" — and the broad version was written first and was
# wrong twice over. `\.claude-local/<anything-with-a-*>` flagged **markdown bold**: `` `.claude-local/`
# ** `` reads as a wildcard, so `CLAUDE.md` and the ledger lit up. It also flagged
# `.claude-local/*_cleared.txt`, and the review SIGNALS never moved — they are per-push private state
# by design. A rule that fires on correct prose is the cry-wolf shape this file already records
# narrowing rather than tolerating, one paragraph up, about `build_*`.
#
# So: only the families that ACTUALLY RELOCATED, each spelled out. Same principle as `_MOVED_BUILDS`
# above, applied to the globbed half. What stayed private and must not fire: `*_cleared.txt`,
# `gate_round.json`, `batch_state.json`, and every subdirectory (`notes/`, `papers/`, `feedback/`,
# `outreach/`, `deepseek/`).
_MOVED_FAMILIES = (
    r"check_\w*\*\w*\.py",                       # the checkers -> tools/verify/
    r"proposed_pre_\w*\*\w*_hook\.sh",           # the hook sources -> tools/verify/
    r"\w*\*\w*_baseline\.txt",                   # the baselines -> tools/verify/
    r"build_zp\w*\*\w*\.py",                     # the formal builders -> scripts/
)
GLOB_REF = re.compile(r"\.claude-local[/\\](?:" + "|".join(_MOVED_FAMILIES) + ")")

# Surfaces that are DATED RECORDS, plus the tombstones (which name the old path by design).
EXEMPT_DIRS = ("/notes/", "/archive/", "/autobiography/", "/feedback/", "/outreach/",
               "/papers/", "/deepseek/", "/.git/", "/.lake/", "/__pycache__/")
# register.md / RELEASES.md: the changelog of record, quoting past versions verbatim and on purpose.
# check_moved.py: this file IS the relocation table, so every old path appears here by definition.
# phase2_file_list.txt: a frozen worklist from an earlier migration - a dated record, not guidance.
# nb.txt and friends: captured console OUTPUT. A log records what a tool printed at a moment
# in time, so a path inside it is a historical fact, not a live instruction to follow.
# scope_baseline.txt: a GENERATED INVENTORY of what each enumerator covers. `check_moved.surfaces()`
# legitimately walks `.claude-local/`, so its section necessarily names the tombstones there — 19 of
# them, every one a path this table itself defines as relocated. Same category as `check_moved.py`
# above: the file is a record of paths, not an instruction to follow one.
# ⚠ The cost, stated rather than discovered: a genuinely stale reference inside that file would go
# unnoticed here. Acceptable only because it is machine-generated from live state and never hand-
# edited, and because it sits in `batch.CHECKERS`, so a change to it is a hash change routed to
# `/rely`. Do NOT extend this to the other `*_baseline.txt` files — those carry prose keys that can
# and do contain real stale paths.
EXEMPT_FILES = ("register.md", "RELEASES.md", "check_moved.py", "phase2_file_list.txt",
                "nb.txt", "scope_baseline.txt")
SCAN_EXT = (".py", ".md", ".sh", ".ps1", ".yml", ".txt", ".lean")


def is_tombstone(path):
    try:
        return io.open(path, encoding="utf-8").read(40).startswith('"""RELOCATED')
    except (OSError, UnicodeDecodeError):
        return False


def surfaces():
    roots = [os.path.join(REPO, d) for d in
             ("tools", "scripts", ".claude", ".github", "ZeroParadox")]
    roots.append(os.path.join(REPO, ".claude-local"))
    roots.append(REPO)  # top-level files only, handled by the depth guard below
    seen = set()
    for root in roots:
        if not os.path.isdir(root):
            continue
        for dirpath, dirnames, files in os.walk(root):
            rel = "/" + os.path.relpath(dirpath, REPO).replace("\\", "/").strip("./") + "/"
            if any(e in rel for e in EXEMPT_DIRS):
                dirnames[:] = []
                continue
            if root == REPO and dirpath != REPO:
                continue          # repo root: top-level files only, subtrees come from their own root
            for f in files:
                if not f.endswith(SCAN_EXT) or f in EXEMPT_FILES:
                    continue
                p = os.path.join(dirpath, f)
                if p in seen:
                    continue
                seen.add(p)
                yield p


def scan_line(line):
    """Every rule this line trips, as (matched_text, destination). The whole detector, isolated.

    Pulled out of `main` so `--selftest` can exercise the matcher on planted strings IN MEMORY. A
    selftest that wrote probe files into the repo would violate the no-scratch-files rule this
    project enforces on its reviewers, and would be scanned by the other checkers while it sat
    there."""
    hits = [(m.group(0), dest) for pat, dest in RULES for m in [pat.search(line)] if m]
    # A globbed reference names a FAMILY, so there is no single destination to point at — say so
    # rather than guessing one. See GLOB_REF.
    hits += [(m.group(0), "(globbed - resolve by hand; a wildcard may span moved AND still-private "
                          "files)") for m in [GLOB_REF.search(line)] if m]
    return hits


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls.

    ⚠ Written 2026-08-15, after this checker shipped without them. VERIFICATION_BUILDOUT Phase 1
    requires both halves on every checker, and a control with only a must-fire half is recorded in
    CLAUDE.md as having been learned three times. This one did catch a false positive on its first
    real run - a `build_*` glob flagging the five build scripts that legitimately stayed private -
    but *caught by accident* is not the standard, and that exact case is now control 5 below."""
    fire = [
        ("a relocated checker",      ".claude-local/check_prose.py"),
        ("a relocated baseline",     "see .claude-local/pov_baseline.txt for the list"),
        ("a relocated build script", "run python .claude-local/build_zpa.py"),
        ("a relocated hook source",  ".claude-local/proposed_pre_push_hook.sh"),
        ("the old commands dir",     "briefs live in .claude-local/commands/"),
        # ⚠ WINDOWS SEPARATORS. These two shapes sat stale in the EDITORIAL GATE BRIEF while this
        # checker reported zero, because every pattern was written with `/`. The brief would have
        # sent a reviewer to two files that no longer exist.
        ("backslash: a moved doc",    r"read .claude-local\PDF_Rendering_Standards.md first"),
        ("backslash: a moved script", r"the build script in .claude-local\build_zpa.py"),
        # ⚠ GLOB-SHAPED, and MIG-2's ledger row demands these specifically: the 14 original controls
        # all planted CONCRETE paths, so the blind half was never probed and `--block` exited 0 over
        # two real stale references. Both shapes below are verbatim from where they were found.
        ("globbed: the hook sources", ".claude-local/proposed_pre_*_hook.sh per clone"),
        ("globbed: the build scripts",
         "the formal build scripts (`.claude-local/build_zp*.py`, mirrored in `scripts/`)"),
        ("globbed: a backslash form", r"see .claude-local\build_zp*.py"),
    ]
    suppress = [
        # Still private and still correct - these did NOT move.
        ("a private note",           ".claude-local/notes/foo_2026-08-15.md"),
        ("the defect ledger",        "ledger it in .claude-local/DEFECTS.md"),
        ("a signal file",            ".claude-local/pa_cleared.txt is stale"),
        ("the papers library",       "check .claude-local/papers/ first"),
        # ⚠ THE REGRESSION CONTROL. A `build_.*\.py` glob reported these as stale on the first run;
        # they were never mirrored and legitimately remain private. If someone re-globs the rule,
        # this control fails rather than the repo filling with false findings.
        ("an unmirrored build script", "python .claude-local/build_padicbridge.py"),
        ("the new path itself",      "python tools/verify/check_prose.py --block"),
        ("unrelated prose",          "the bottom is the diagonal fixed point"),
        # ⚠ THE GLOB RULE MUST NOT SWALLOW A DIRECTORY THAT LEGITIMATELY STAYED PRIVATE. These name
        # families under `.claude-local/` that never moved; a wildcard over them is correct prose.
        ("globbed but still private", "every .claude-local/notes/*.md from that arc"),
        ("a wildcard outside the private folder", "scripts/build_zp*.py render the formal layers"),
        # ⚠ Both of these were FALSE POSITIVES of the first, broad version of GLOB_REF.
        ("markdown bold, not a wildcard", "the private folder `.claude-local/` **is gitignored**"),
        ("signals never moved",       "the hook validates .claude-local/*_cleared.txt"),
        ("private state never moved", "round state lives in .claude-local/gate_round*.json"),
    ]

    bad = 0
    print("  MUST FIRE")
    for label, line in fire:
        got = scan_line(line)
        ok = bool(got)
        if not ok:
            bad += 1
        print("    %-28s %s" % (label, "ok" if ok else "*** MISSED ***"))
    print("  MUST SUPPRESS")
    for label, line in suppress:
        got = scan_line(line)
        ok = not got
        if not ok:
            bad += 1
        print("    %-28s %s%s" % (label, "ok" if ok else "*** FALSE POSITIVE ***",
                                  "" if ok else "  -> " + got[0][0]))

    # The tombstone skip, exercised on a real file OUTSIDE the repo (no scratch files in-tree).
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        tomb = os.path.join(d, "t.py")
        io.open(tomb, "w", encoding="utf-8").write('"""RELOCATED 2026-08-15 -> tools/verify/x.py\n"""')
        plain = os.path.join(d, "p.py")
        io.open(plain, "w", encoding="utf-8").write("# ordinary file\n")
        for label, path, want in (("tombstone recognised", tomb, True),
                                  ("ordinary file is not", plain, False)):
            ok = is_tombstone(path) is want
            if not ok:
                bad += 1
            print("    %-28s %s" % (label, "ok" if ok else "*** WRONG ***"))

    # ⚠ THE PATTERN PINS (PAT-1). This checker's whole content is its relocation TABLE — 74 rules
    # and 4 globbed families — and ten controls covered them. A rule deleted from the table is a
    # stale path that silently stops being reported, which is the exact failure `MIG-2` was opened
    # for. The destinations are pinned rather than the regexes: a destination is stable and readable,
    # where the patterns carry `SEP` and are rebuilt per platform.
    # ⚠ THE SCOPE PIN (PAT-2). This checker BLOCKS at push and walks privately, and had no
    # scope section at all: its controls run in memory and never touch its enumerator, so
    # nothing exercised what it covers. Verified rather than inferred by /rely round 4.
    print("  SCOPE")
    bad += common.check_scope("check_moved",
                              [os.path.relpath(p, REPO).replace("\\", "/")
                               for p in surfaces()])
    print("  PATTERNS")
    bad += common.check_vocabulary("check_moved", globals())

    print("\n  selftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0


def main(argv):
    if "--selftest" in argv:
        print("=" * 60)
        print("  relocated-path check - CONTROLS")
        print("=" * 60)
        return selftest()
    block = "--block" in argv
    hits = []
    for p in surfaces():
        if is_tombstone(p):
            continue
        try:
            text = io.open(p, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        for i, line in enumerate(text.split("\n"), 1):
            for found, dest in scan_line(line):
                hits.append((os.path.relpath(p, REPO).replace("\\", "/"), i, found, dest))
    print("=" * 60)
    print("  relocated-path check")
    print("  relocations tracked : %d" % len(RULES))
    print("  stale references    : %d" % len(hits))
    print("=" * 60)
    for rel, i, found, dest in hits:
        print("  %s:%d" % (rel, i))
        print("      %s  ->  %s" % (found, dest))
    rc = common.record_if_asked(
        "check_moved",
        [os.path.relpath(p, REPO).replace("\\", "/")
         for p in surfaces() if not is_tombstone(p)],
        {h[0] for h in hits}, "a relocated path is still referenced", argv)
    if rc:
        return rc

    if hits:
        print("\nA relocated path is still referenced. Update the reference, or add the file to")
        print("the dated-record exemptions if it is a historical record rather than live guidance.")
        return 1 if block else 0
    print("OK: nothing points at a relocated path.")
    return 0


if __name__ == "__main__":
    common.utf8_stdout()   # one definition; two of the eight copies had dropped
                           # line_buffering=True, which reorders output against children
    sys.exit(main(sys.argv[1:]))
