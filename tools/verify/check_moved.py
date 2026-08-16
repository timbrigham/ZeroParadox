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

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")

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
_VERIFY = ("hooks batch report guards vendored gate_round gatelock debaseline selfheal ship "
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

# Surfaces that are DATED RECORDS, plus the tombstones (which name the old path by design).
EXEMPT_DIRS = ("/notes/", "/archive/", "/autobiography/", "/feedback/", "/outreach/",
               "/papers/", "/deepseek/", "/.git/", "/.lake/", "/__pycache__/")
# register.md / RELEASES.md: the changelog of record, quoting past versions verbatim and on purpose.
# check_moved.py: this file IS the relocation table, so every old path appears here by definition.
# phase2_file_list.txt: a frozen worklist from an earlier migration - a dated record, not guidance.
# nb.txt and friends: captured console OUTPUT. A log records what a tool printed at a moment
# in time, so a path inside it is a historical fact, not a live instruction to follow.
EXEMPT_FILES = ("register.md", "RELEASES.md", "check_moved.py", "phase2_file_list.txt",
                "nb.txt")
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
    return [(m.group(0), dest) for pat, dest in RULES for m in [pat.search(line)] if m]


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
    if hits:
        print("\nA relocated path is still referenced. Update the reference, or add the file to")
        print("the dated-record exemptions if it is a historical record rather than live guidance.")
        return 1 if block else 0
    print("OK: nothing points at a relocated path.")
    return 0


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
    except Exception:
        pass
    sys.exit(main(sys.argv[1:]))
