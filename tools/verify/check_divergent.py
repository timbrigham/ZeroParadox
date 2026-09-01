#!/usr/bin/env python3
"""DC-24 / DC-28 - a claim corrected in one place and left standing in another.

THE CLASS. A sentence lives in several files. Someone fixes it where they found it, and the twin
survives. Every correction is real and recent; every sweep hits the authoritative file and misses a
reader-facing sibling. Four consecutive review rounds on one document produced this shape, and the
counts did not fall: 6 findings, then 7, then 12. `CLAUDE.md` R-RECUR's ladder says the fourth
occurrence is where a remembered rule becomes a checker.

⚠⚠ THE DETECTOR IS THE WHOLE DESIGN, AND IT IS BACKWARDS FROM THE OBVIOUS ONE.

Do NOT grep for the NEW phrasing. A fix that landed is not evidence of anything, and searching for it
finds exactly the sites already correct. **Grep for the phrase the diff REMOVED.** What a fix deleted
is a fingerprint of the defect, and any file still carrying it is a twin the fix did not reach.

Two independent review agents converged on this formulation on 2026-08-28 after finding it by hand.

⚠ AND IT RUNS ON THE RENDERED ARTIFACT, NEVER THE SOURCE. Measured the same day: of the residual
copies one round left behind, three rendered from a data module that is not in this repository at
all, so no grep of any tracked generator could see them. A source-only sweep reports clean while the
published page still carries the sentence. `R-DEFECTCLASS` records the same lesson one layer over:
a claim-sweep's unit is the extracted PDF, because a claim can span two adjacent string literals.

⚠ HTML ENTITIES ARE DECODED BEFORE MATCHING. The published interactive maps encode every
mathematical glyph numerically - infinity is `&#8734;`, bottom is `&#8869;` - so a pattern written in
glyphs scores ZERO against the raw bytes and eleven against the decoded text. Measured 2026-08-29.

WHAT IT IS NOT. It does not judge whether a sentence is true; it reports that two files disagree
about one, which is a question for a reader. It is a READING LIST, and it prints its count on every
run whether or not anything is found.

  python check_divergent.py                 # report, exit 0
  python check_divergent.py --block         # exit 1 on any unbaselined divergence
  python check_divergent.py --selftest      # the controls, both directions
"""
import io, os, re, sys, html, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

common.utf8_stdout()

HERE = str(common.HERE)
REPO = str(common.REPO)
SELF = common.self_rel(__file__)

# The RENDERED surfaces a reader meets, PLUS the sources that supply them.
# ⚠ `.py` WAS MISSING AND THAT WAS THE SAME DEFECT THIS FILE EXISTS TO CATCH. The first version
# excluded generators, reasoning that "a generator is checked through its artifact" — which is false
# for anything that does NOT render. Measured 2026-08-29, hours after this checker was written: a
# retired phrase survived in `build_bottom_matrix.py`'s readout, which renders only to a private
# note, and three `∅` cell reasons cited a criterion nothing defined any more. This checker could
# not see one of them, having been given the wrong extension list by its own author on the same day
# he diagnosed exactly that blindness in `check_poles`.
SCAN_EXT = (".md", ".html", ".lean", ".py")
SKIP_DIRS = {".lake", ".git", "__pycache__", ".claude-local", "node_modules", "historical"}
SKIP_RELDIRS = {"tools/verify", "tools/process"}

# ---------------------------------------------------------------------------
# THE RETIRED-PHRASE REGISTER. One row per phrase a correction has REMOVED, with the date and the
# reason. This is the checker's whole input, and it is deliberately a written record rather than a
# heuristic: a phrase earns a row when a fix deletes it, so the register grows by the same act that
# creates the risk. An empty register means nobody has recorded a correction yet, NOT that the
# corpus is clean -- and the run says so rather than printing a bare zero.
RETIRED = [
    {"phrase": "successive nulls",
     "since": "2026-08-28",
     "why": "asserts the snap-arc lands on a NEW bottom. `snap_arc_z2_loop` proves it returns to the "
            "SAME zero, and `dp2_execution_distinguishability` proves the two nulls have EQUAL value "
            "and differ only in machine state. The novelty is a commitment, never a theorem.",
     "instead": "state the return as 'to A bottom', and mark the novelty a commitment"},
    {"phrase": "a NEW null each return",
     "since": "2026-08-29",
     "why": "same claim as 'successive nulls', stated harder, in a published figure.",
     "instead": "'novelty is a commitment'"},
    {"phrase": "coincide at the seam",
     "since": "2026-08-29",
     "why": "appeared beside a `rInv_swaps` citation. R-BEDROCK prohibits citing that theorem for a "
            "COINCIDENCE: it proves two points EXCHANGED, and there they are provably distinct.",
     "instead": "'exchanged by inversion ... which leaves them distinct'"},
    {"phrase": "generates the ceiling",
     "since": "2026-08-28",
     "why": "'ceiling' as epsilon-zero's identity collapses it to the max face, against "
            "`epsilon0_min_eq_max`. It also collides with GUIDE/SNAP, where 'ceiling' names the "
            "UPPER BOTTOM: same word, two referents, three linked documents.",
     "instead": "'generates the tower above it', naming both faces"},
    {"phrase": "one and the same object",
     "since": "2026-07-15",
     "why": "the cross-category identity is retired as ill-typed. `x = y` across distinct categories "
            "is not a well-formed proposition, so it was never a claim to hold.",
     "instead": "the FAMILY reading, or the naming reading"},
]


def enumerate_files():
    """Every file this checker scans, repo-relative. EXTRACTED so the scope pin can query it."""
    for root, dirs, files in os.walk(REPO):
        relroot = os.path.relpath(root, REPO).replace("\\", "/")
        dirs[:] = [
            d for d in dirs
            if d not in SKIP_DIRS
            and (relroot + "/" + d).lstrip("./") not in SKIP_RELDIRS
        ]
        for fn in files:
            if fn.endswith(SCAN_EXT):
                yield os.path.relpath(os.path.join(root, fn), REPO).replace("\\", "/")


def render(text):
    """The text as a READER meets it: entities decoded, soft-wrap joined.

    ⚠ WRAP-TOLERANCE IS NOT COSMETIC. A phrase that straddles a line break is exactly the residual a
    line-scoped grep misses -- measured 2026-08-28, when a sweep found three of four copies and the
    one it missed wrapped across two lines."""
    t = html.unescape(text)
    return re.sub(r"\s+", " ", t)


def scan_text(text, path="<str>"):
    """Every retired phrase still present, as (path, phrase, since, context)."""
    flat = render(text)
    out = []
    for row in RETIRED:
        p = row["phrase"]
        i = flat.lower().find(p.lower())
        if i < 0:
            continue
        out.append((path, p, row["since"], flat[max(0, i - 60): i + len(p) + 60].strip()))
    return out


def scan_repo():
    hits = []
    for rel in enumerate_files():
        try:
            t = io.open(os.path.join(REPO, rel), encoding="utf-8").read()
        except Exception:
            continue
        hits += scan_text(t, rel)
    return hits


# --------------------------------------------------------------------------- controls
MUST_FIRE = [
    ("plain",            "Floor and ceiling are both bottom (successive nulls); epsilon-zero is the first step"),
    ("entity-encoded",   "the pole &#183; floor and ceiling both &#8869; &#183; a NEW null each return"),
    ("wrapped",          "the two poles of the self-dual 0=infinity, swapped by inversion\n    "
                         "and coincide at the seam"),
    ("case-shifted",     "The floor Generates The Ceiling: epsilon-zero = closure of 0"),
]
MUST_SUPPRESS = [
    ("the corrected form",   "the return is to A bottom; that it is a NEW one is a commitment"),
    ("the exchange form",    "exchanged by inversion, which proves the exchange and leaves them distinct"),
    ("the tower form",       "the floor generates the tower above it, and it is both supremum and least fixed point"),
    ("family, not identity", "the members are distinct as structures, proved pairwise wherever a wall has been built"),
]


def selftest():
    bad = 0
    print("MUST FIRE")
    for name, line in MUST_FIRE:
        got = bool(scan_text(line))
        print("  %-24s %s" % (name, "ok" if got else "*** DID NOT FIRE ***"))
        bad += 0 if got else 1
    print("MUST SUPPRESS")
    for name, line in MUST_SUPPRESS:
        got = bool(scan_text(line))
        print("  %-24s %s" % (name, "ok" if not got else "*** FALSE POSITIVE ***"))
        bad += 1 if got else 0
    print("SCOPE")
    bad += common.check_scope("check_divergent", list(enumerate_files()))
    print("REGISTER")
    if not RETIRED:
        print("  register is EMPTY -- the checker can never fire      *** UNARMED ***")
        bad += 1
    else:
        print("  %d retired phrase(s) registered                      ok" % len(RETIRED))
    return bad


def main():
    argv = sys.argv[1:]
    if "--selftest" in argv:
        bad = selftest()
        print("\nselftest: %s" % ("PASS" if bad == 0 else "%d CONTROL(S) MISBEHAVED" % bad))
        return 0 if bad == 0 else 1

    hits = scan_repo()
    files = len(set(h[0] for h in hits))
    for path, phrase, since, ctx in sorted(hits):
        print("%s  retired %r (since %s)" % (path, phrase, since))
        print("    ...%s..." % ctx)
    print()
    print("%d surviving retired phrase(s) in %d file(s); register holds %d phrase(s)"
          % (len(hits), files, len(RETIRED)))
    if not hits:
        print("⚠ A ZERO HERE IS ONLY AS WIDE AS THE REGISTER. It means no REGISTERED phrase survives,")
        print("  never that no claim diverges. Add a row whenever a fix deletes a sentence.")
    if "--block" in argv and hits:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
