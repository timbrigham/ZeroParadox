#!/usr/bin/env python3
"""Triage the grandfathered baselines toward ZERO. (Tim, 2026-08-09: no grandfathered content.)

WHY A BASELINE IS DEBT AND NOT A DECISION. Its stated premise is that each entry was verified by
reading it. The prose baseline was once REGENERATED rather than pruned, which falsifies that premise
for those entries. So a baseline is a record of what nobody has read, sitting behind a green check.

THE TWO TERMINAL STATES, and neither is "grandfathered":
  * FIX it, or
  * LABEL it in-source with the reason it is fine (`Idiom:`, `Statement:`, `Reading:`, a NO-GO note).
A label sits where the next reader is and carries the verification a baseline never had.
⚠ ORDER IS FIXED: fix before label, in every batch. Labelling first grandfathers defects under a new
name, which is the failure this whole exercise exists to end.

THE SPLIT THIS TOOL COMPUTES - it is the real reduction, and it is bigger than any AI filtering:

  MECHANICAL - the property is decidable by the checker itself. A block is 12 lines against a cap of
    10; there is no judgement to make, so the checker IS the evaluation. No AI stage, no gate round.
    Delete-first: across one arc, deletions ran a ZERO error rate while authored prose ran ~1 in 7.

  SEMANTIC - the property needs judgement (is this gloss accurate? which POV KIND? is this class
    degenerate?). No amount of cheap filtering removes the need for someone to look, because the
    label asserts that someone did.

  PROBE - a SEMANTIC site whose question is settled by RUNNING something: build the trivial witness,
    write the `example` that fails when the gloss is wrong, measure the axioms. This is the stage
    that was missing from the original plan, and it is where the yield is - every BEDROCK finding
    across ~20 agent runs came from executing rather than reading.

⚠ THE CHEAP STAGES RUN WIDE, NOT NESTED. Measured 2026-08-09: `check_poles.py` caught both real
defects the bulk LLM missed in 4/4 runs, and the LLM caught two the regex structurally cannot see.
Feeding the LLM only what the regex flagged would inherit every false negative permanently. Union
their output; narrow at the judgement stage, never before it.

  python debaseline.py            # summary
  python debaseline.py --files    # per-file worklist, for file-sized batches
  python debaseline.py --bucket unlabelled   # one bucket's sites
"""
import io, os, sys, collections

BASE = os.path.dirname(os.path.abspath(__file__))

# baseline file -> (bucket name, disposition, needs a probe?)
SOURCES = {
    "class_baseline.txt": ("class",      "SEMANTIC", True),
    "modal_baseline.txt": ("modal",      "SEMANTIC", True),
    "pov_baseline.txt":   ("pov",        "SEMANTIC", False),
}
# prose encodes its kind in the key: path::kind::hash::text
PROSE_KIND = {
    "block":      ("prose-block",      "MECHANICAL", False),  # over-cap header; length is decidable
    "doc":        ("prose-doc",        "MECHANICAL", False),  # docstring longer than its decl
    "bare":       ("prose-bare",       "SEMANTIC",   False),  # a gloss must be AUTHORED, and
                                                              # authoring is where errors come from
    # ⚠ The SERIALIZED kind is `label`, while check_prose.py's internal name for the same rule is
    # `unlabelled` (it writes "%s::label::%s" at :169). Assuming the two matched produced 83
    # unclassified sites on the first run. Read the file, not the variable name.
    "label":      ("prose-unlabelled", "SEMANTIC",   True),   # DC-1 surface; settle with an `example`
}

def entries(fn):
    p = os.path.join(BASE, fn)
    if not os.path.exists(p):
        return []
    out = []
    for ln in io.open(p, encoding="utf-8-sig").read().splitlines():
        s = ln.strip()
        if s and not s.startswith("#"):
            out.append(s)
    return out

def path_of(entry):
    """First path-looking field, however the baseline delimits it."""
    for sep in ("::", "\t"):
        if sep in entry:
            return entry.split(sep)[0]
    return entry.split()[0] if entry else "?"

def collect():
    rows = []
    for fn, (bucket, disp, probe) in SOURCES.items():
        for e in entries(fn):
            rows.append((bucket, disp, probe, path_of(e), e))
    for e in entries("prose_baseline.txt"):
        parts = e.split("::")
        kind = parts[1] if len(parts) > 1 else "?"
        bucket, disp, probe = PROSE_KIND.get(kind, ("prose-?", "SEMANTIC", False))
        rows.append((bucket, disp, probe, parts[0], e))
    return rows

# Risk order: yield per site, measured where known. Classes have a ~30% known degeneracy rate
# (5 of 17 audited by hand were degenerate or bundled a commitment as data); unlabelled glosses are
# the corpus's characteristic defect class; modal claims put a false universal negative into a
# published PDF. Volume prose is last because it is formatting, not claims.
RISK = ["class", "modal", "prose-unlabelled", "pov", "prose-bare", "prose-doc", "prose-block"]

def main():
    rows = collect()
    by = collections.Counter(r[0] for r in rows)
    disp = collections.Counter(r[1] for r in rows)

    if "--bucket" in sys.argv:
        want = sys.argv[sys.argv.index("--bucket") + 1]
        for b, d, pr, path, e in rows:
            if b == want:
                print("%-46s %s" % (path, e[:110]))
        print("\n%d site(s) in %s" % (by[want], want))
        return 0

    if "--files" in sys.argv:
        per = collections.defaultdict(collections.Counter)
        for b, d, pr, path, e in rows:
            per[path][b] += 1
        order = sorted(per.items(), key=lambda kv: -sum(kv[1].values()))
        print("%-58s %5s  buckets" % ("file", "total"))
        for path, c in order[:40]:
            print("%-58s %5d  %s" % (path[:58], sum(c.values()),
                                     ", ".join("%s:%d" % (k, v) for k, v in c.most_common())))
        print("\n%d files carry grandfathered sites (top 40 shown)" % len(per))
        return 0

    print("GRANDFATHERED SITES — %d total\n" % len(rows))
    print("%-20s %6s  %-11s %s" % ("bucket", "sites", "disposition", "needs a probe"))
    seen = set()
    for b in RISK + sorted(set(by) - set(RISK)):
        if b not in by or b in seen:
            continue
        seen.add(b)
        r = next(x for x in rows if x[0] == b)
        print("%-20s %6d  %-11s %s" % (b, by[b], r[1], "yes" if r[2] else "-"))
    print("\n%-20s %6d   <- the checker IS the evaluation; no AI, no gate round"
          % ("MECHANICAL", disp["MECHANICAL"]))
    print("%-20s %6d   <- someone must look; a label asserts that they did"
          % ("SEMANTIC", disp["SEMANTIC"]))
    probes = sum(1 for r in rows if r[2])
    print("%-20s %6d   <- settled by RUNNING something, not by classifying text" % ("of those, PROBE", probes))
    pct = 100.0 * disp["MECHANICAL"] / len(rows) if rows else 0
    print("\n%.0f%% needs no judgement at all. Work the SEMANTIC buckets in RISK order above." % pct)
    return 0

# --------------------------------------------------------------------------- controls
# ⚠ The `label` case is the bug this file shipped: the prose baseline SERIALIZES the kind as
# `label` while `check_prose.py`'s internal name for the same rule is `unlabelled`. Mapping the
# internal name left 83 sites unclassified as `prose-?` — read the file, not the variable name.
CASES = [
    ("prose block", "ZeroParadox/A.lean::block::abc123::header", "prose-block", "MECHANICAL"),
    ("prose doc", "ZeroParadox/A.lean::doc::abc123::WVSNondeg", "prose-doc", "MECHANICAL"),
    ("prose bare #check", "ZeroParadox/A.lean::bare::foo", "prose-bare", "SEMANTIC"),
    ("prose unlabelled gloss (serialized as `label`)",
     "ZeroParadox/A.lean::label::foo", "prose-unlabelled", "SEMANTIC"),
    ("unknown kind falls back, never silently drops",
     "ZeroParadox/A.lean::wat::foo", "prose-?", "SEMANTIC"),
]
PATH_CASES = [
    ("double-colon delimiter", "ZeroParadox/A.lean::structure Foo", "ZeroParadox/A.lean"),
    ("tab delimiter", "BOTTOMELEMENT.md::hash\tBOTTOMELEMENT.md:116\tprose", "BOTTOMELEMENT.md"),
]


def selftest():
    bad = 0
    print("prose kind -> bucket mapping")
    for label, entry, want_bucket, want_disp in CASES:
        parts = entry.split("::")
        bucket, disp, _probe = PROSE_KIND.get(parts[1], ("prose-?", "SEMANTIC", False))
        ok = (bucket, disp) == (want_bucket, want_disp)
        print("  %-46s %s" % (label, "ok" if ok else "*** got %s/%s ***" % (bucket, disp)))
        bad += 0 if ok else 1
    print("path extraction")
    for label, entry, want in PATH_CASES:
        ok = path_of(entry) == want
        print("  %-46s %s" % (label, "ok" if ok else "*** got %s ***" % path_of(entry)))
        bad += 0 if ok else 1
    print("every bucket has a disposition and a risk rank")
    known = {b for b, _d, _p in list(SOURCES.values()) + list(PROSE_KIND.values())}
    missing = sorted(known - set(RISK))
    ok = not missing
    print("  %-46s %s" % ("no bucket missing from RISK order",
                          "ok" if ok else "*** unranked: %s ***" % missing))
    bad += 0 if ok else 1

    # ⚠ MUST FIRE — the half this selftest shipped without, and it went unnoticed because NOTHING
    # RAN THESE CONTROLS (DEB-1, /rely round 2): not `check_checkers`, not `ci_report.SELFTESTS`,
    # not any workflow, while `batch.py` depends on this module for every debaselining worklist.
    # The assertions above are all must-SUPPRESS — they check that correct input is classified
    # correctly. None of them could fail if the classifier answered "prose-?" to everything.
    print("MUST FIRE (a misclassification is caught)")
    for label, entry, wrong_bucket in (
            ("a kind is NOT silently bucketed as its neighbour",
             "ZeroParadox/Foo.lean::unlabelled::1", "prose-bare"),
            ("an unknown kind falls to the sentinel, not a real bucket",
             "ZeroParadox/Foo.lean::not-a-real-kind::1", "prose-doc"),
    ):
        parts = entry.split("::")
        got, _disp, _probe = PROSE_KIND.get(parts[1], ("prose-?", "SEMANTIC", False))
        ok = got != wrong_bucket
        print("  %-46s %s" % (label, "ok" if ok else "*** COLLAPSED to %s ***" % got))
        bad += 0 if ok else 1

    # And the mapping must not be degenerate: if every kind mapped to one bucket the cases above
    # would still pass individually. A classifier with one output class classifies nothing.
    distinct = {b for b, _d, _p in PROSE_KIND.values()}
    ok = len(distinct) > 1
    print("  %-46s %s" % ("the mapping is not degenerate",
                          "ok" if ok else "*** ONE BUCKET — classifies nothing ***"))
    bad += 0 if ok else 1

    print("\nselftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
