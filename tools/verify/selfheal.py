"""Standing recurrence check on the GATES and SUBAGENT BEHAVIOUR. Suggests; never corrects.

    python selfheal.py           # the report
    python selfheal.py --all     # include shapes under the threshold

WHY (Tim, 2026-08-10): *"there should also be a standing self improvement on the gates and the
sub-agent behavior. not automatic correction, but if we hit the same bug repeatedly you should
suggest process improvements."*

`DEFECT_CLASSES.md` already states the rule — *"a one-off is an instance; the SECOND occurrence is a
class"* — and this session proved the rule leaks exactly the way every discipline in this project
leaks: the same shape recurred three times before anyone noticed, because noticing required someone
to remember 67 ledger rows at once. Counting is decidable, so a script should do it.

**WHAT THIS IS NOT.** It does not edit, fix, or file anything. It reports *"this shape has now
happened N times and has no class row"* and leaves the judgement — is this one phenomenon or three
coincidences, and what process change would actually prevent it — to a human or an agent. Auto-
filing would produce a class register full of rows nobody verified, which is the failure mode
`DEFECT_CLASSES.md` exists to avoid.

**WHY THESE SHAPES.** They are the PROCESS and AGENT-BEHAVIOUR failures measured in this corpus, as
opposed to the mathematical-content failures `DC-1…DC-18` already cover. The split matters: a
content defect ships a wrong claim, a process defect ships a gate that cannot see it.

⚠ **The counts are a READING LIST, not a finding list** — the same rule this project applies to every
other detector. A row matching twice may be one incident described twice. **Read the hits before
acting on a number.**
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
PRIV = str(common.PRIV)
SELF = common.self_rel(__file__)
BASE = HERE
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import report                                    # noqa: E402

# BOTH still private, and DEFECT_CLASSES.md is a deliberate deferral rather than an oversight.
# VERIFICATION_BUILDOUT.md Phase 7 already schedules it for publication and attaches two conditions
# this migration does not satisfy: a preamble that stops "17 defect classes" reading as *unstable*
# rather than *rigorous*, and a pass through both adversary gates. Publishing the CODE needs
# neither — a checker makes no claim about the mathematics. Publishing the PROSE needs both.
DEFECTS = os.path.join(PRIV, "DEFECTS.md")
CLASSES = os.path.join(PRIV, "DEFECT_CLASSES.md")
THRESHOLD = 3

# The summary line's stable half. `/ship` selects that line out of this script's stdout, so the
# two of them agreed on a wording by COPY until 2026-09-16, when `/rely` O2 measured the copy
# broken: `ship.py` looked for a line that both began `⚠` and contained "shape(s)", and no line
# here has ever satisfied both. **The self-heal line had never once printed.** One definition,
# imported — which is the remedy SH-7 itself prescribes, applied to SH-7's own reporting path.
SUMMARY_TAG = "shape(s) over threshold"

# The ranked list's two UNCLASSED markers, exported for the same reason as `SUMMARY_TAG` and
# after the same defect one ring further out (`/rely` R2-B1, 2026-09-16): `batch.py` selects the
# push-time advisory by matching `← NO CLASS ROW` as a retyped literal, so when the second marker
# was added, a shape naming a row that does not exist stopped reaching the push-time channel
# entirely — under a heading that promises "recurring process shapes with NO class row", which
# this script defines as *no id at all, or an id naming no row*. Half the set, under the heading
# for the whole set. **Consumers select on these names; they do not retype the strings.**
ACTIONS_HEADING = "WHAT TO DO BEFORE THE NEXT RUN"
MARK_NO_ROW = "← NO CLASS ROW"
MARK_NAMES_NO_ROW = "NAMES NO ROW"
UNCLASSED_MARKS = (MARK_NO_ROW, MARK_NAMES_NO_ROW)

# A class id is DEFINED at exactly two kinds of site in `DEFECT_CLASSES.md`: a row in the
# summary table (`| **DC-N** |`) and a section heading whose subject it IS. Anywhere else it is
# a REFERENCE, and a reference is not evidence the row exists.
#
# ⚠ LEADING POSITION IS THE TEST, tightened 2026-09-16 (`/rely` R2-O4). "anywhere in a heading"
# accepted `### Why this is not DC-99` and `#### See also: DC-99` — headings that CITE a class
# while defining nothing. Every real heading in the register leads with the id, after at most a
# marker glyph: `## DC-44 — a TRUE value read against the WRONG OBJECT`, `### ⛔ DC-2 has NO
# CHECKER`, `### ⚠ DC-24's DIAGNOSIS WAS WRONG`.
#
# ⛔ WHAT IT STILL ACCEPTS, DELIBERATELY: `### DC-99 was withdrawn`. A heading LEADING with the
# id is that class's section, and the question this answers is "has the reader somewhere to go?"
# — a section recording a retirement answers YES. Naming the limit beats implying it is closed;
# a third narrowing of the same proxy is where `R-REVALIDATE` says to stop and measure instead.
CLASS_DEFN = re.compile(
    r"^(?:\|\s*\*\*(DC-\d+)\*\*"                 # a row in the summary table
    r"|#{1,6}\s+[^\w\n]*(DC-\d+))",              # or a heading LEADING with the id
    re.M)

# id, name, pattern, existing class (or None), the process change worth considering
SHAPES = [
    ("SH-1", "exit status not propagated",
     r"exit code|exit status|propagate|\$\?",
     "DC-10 (partial)",
     "Require every new shell/subprocess wiring to ship with a control that makes the child FAIL "
     "and asserts the caller sees non-zero. Three instances so far were found by reading, not by a test."),
    ("SH-2", "encoding / BOM / codepage",
     r"\bascii\b|BOM|cp1252|UnicodeEncode|line_buffering|em-dash",
     "DC-33",
     "One import that sets utf-8 + line buffering for every entry point (report.py does this now). "
     "Any NEW standalone script must import it or set both explicitly."),
    ("SH-3", "fixed ONE OF TWO routes to the same property",
     r"second route|one of two|survived the first fix|different door|same defect .{0,30}through",
     None,
     "SOLVED MECHANICALLY 2026-08-10 — do not re-answer this with a rule. Add the property and "
     "EVERY route to `guards.py`, which walks them all and BLOCKS at pre-push. The "
     "prose version of this remedy stood for the first four instances and prevented none of them; "
     "the registry found two more live routes on its first run. `guards.py --list` shows the "
     "surface. A permitted route is listed too, with a `visible` predicate."),
    ("SH-4", "agent mutated or destroyed shared state",
     r"reset --hard|destroyed the caller|git clean|left .{0,20}in the source tree|swept it up",
     None,
     "Agents that need git state use `git worktree add --detach`; the shared tree is off limits. "
     "Caller commits or stashes before spawning. Already in CLAUDE.md — keep it in every brief."),
    ("SH-5", "tooling trap yielding a FALSE ZERO",
     r"POSIX ERE|wrapped across|SimpleMatch|Select-Object -First|false zero|truncated .{0,15}search",
     "DC-8 (partial)",
     "Before believing any zero, run the probe in the SHAPE you expect to find (wrapped, "
     "comment-prefixed, piped). Keep must-fire and must-suppress controls beside each detector."),
    ("SH-6", "gate reports success it has not earned",
     r"fail-open|fails open|vacuous|reported success|passed vacuously",
     "DC-10",
     "Every gate states its enforcement mode in its own output (report.py manifest), and every "
     "check is exercised once in a state where it MUST fail."),
    ("SH-7", "duplicated definition that drifted",
     r"second (copy|implementation)|re-implement|two (partial )?implementations|drifted|paraphrase",
     # ⚠ NOT DC-31. Mapped there 2026-08-27 and reverted the same day: DC-31 is a SHADOWED
     # top-level name inside ONE module, and none of the rows this pattern matches is that.
     # They are cross-file duplication and paraphrase drift. A row that does not cover the
     # shape is worse than no row, because the banner then reports the shape as covered.
     # ⭐ MAPPED 2026-09-15 to DC-53, written FOR this shape at its 18th occurrence. The banner
     # had printed "← NO CLASS ROW" on every prepush run in the meantime; the row it was asking
     # for now exists, and DC-53 carries the detector (the claim sweep over DELETED wording).
     "DC-53",
     "One definition, imported. If two languages need it, one of them delegates. Measured cost so "
     "far: two hook implementations, two vendored rules, two ways to spawn agents. ⚠ AND THE "
     "REGISTRY FORM IS THE EXPENSIVE ONE: when the drifted copy is a CLASS ROW describing a "
     "detector, the tool is believed absent and the defect it would catch ships. Measured "
     "2026-09-15: DC-24's row denied having a mechanical half for 28 days after it shipped, and "
     "the defect that half would have caught reached two DOI-bearing PDFs."),
    ("SH-8", "report/manifest claims more than it does",
     r"manifest .{0,20}lie|claims? .{0,25}BLOCK|advisory .{0,20}blocked|reads as (a )?confirmation",
     None,
     "The manifest is generated FROM the same table the runner iterates, so it cannot describe a "
     "plan the code does not execute."),
]


def read(p):
    """The file's text, or `None` when there is no file.

    ⚠ IT RETURNED `""` UNTIL 2026-09-16, AND THAT IS NOT A WEAKER MESSAGE — IT IS THE SAME
    BYTES. `/rely` R2-B3 measured it: a MISSING `DEFECTS.md` and a ledger with no rows produce
    byte-identical output, a clean bill of health, exit 0. And missing is the DEFAULT state on
    any checkout without the private repo, since `.claude-local` is its own repository that the
    parent ignores — so the reading nobody can distinguish is also the common one. R-ZERONULL:
    the empty branch must return a VALUE that differs, never only a different message.
    """
    if not os.path.exists(p):
        return None
    return io.open(p, encoding="utf-8", errors="replace").read()


def rows_of(ledger):
    """The ledger as ROWS, not as one string.

    ⚠ It used to count regex MATCHES across the whole file, which counts one incident described
    three times as three incidents — measured by `/rely` pass 4: two of four unclassed flags were
    artefacts of that. A recurrence claim must count DISTINCT ROWS or it manufactures the very
    pattern it claims to detect."""
    return [r for r in re.split(r"\n(?=\| \*\*)", ledger) if r.startswith("| **")]


def main():
    show_all = "--all" in sys.argv
    ledger, classes = read(DEFECTS), read(CLASSES)

    # ⛔ FAIL LOUD AND EARLY. An UNREADABLE input cannot produce a report about recurrence, and
    # the one thing it must never produce is the report it would print if there were nothing to
    # find. Both inputs live in `.claude-local`, a separate repository the parent ignores, so
    # their absence is ordinary rather than exotic.
    absent = [p for p, t in ((DEFECTS, ledger), (CLASSES, classes)) if t is None]
    if absent:
        for p in absent:
            sys.stderr.write("  ** NOT FOUND: %s **\n" % p)
        sys.stderr.write(
            "  This script counts recurrence across those two files. With either missing it has\n"
            "  NOTHING to count, and a count of zero would be indistinguishable from a clean\n"
            "  register. Refusing rather than reporting health it has not measured.\n")
        return 2
    rows = len(re.findall(r"^\| \*\*", ledger, re.M))
    # ⚠ DEFINITION SITES ONLY — a table row `| **DC-N**` or a heading naming DC-N. `/rely`
    # O1, 2026-09-16: the old `DC-\d+` scan accepted ANY mention, so a class id merely
    # discussed in prose read as proof its row existed. The property under test is
    # EXISTENCE, and a mention is not an existence proof — the same substitution DC-27
    # names (a PROXY tested for the PROPERTY). Measured at the change: both forms return
    # the same 53 ids today, so this tightens the test without moving the output.
    known = sorted({a or b for a, b in CLASS_DEFN.findall(classes)},
                   key=lambda s: int(s.split("-")[1]))

    report.banner("self-heal — recurrence on gates and agent behaviour", [
        ("ledger", "%d instance row(s) in DEFECTS.md" % rows),
        ("classes", "%d class row(s): %s" % (len(known), " ".join(known))),
        ("rule", "a one-off is an instance; the SECOND occurrence is a class"),
        ("action", "SUGGESTS ONLY — never edits, never files"),
    ])

    rows = rows_of(ledger)
    flagged = []
    print("  %-6s %-42s %6s  %s" % ("id", "shape", "rows", "class"))
    print("  " + "-" * 74)
    for sid, name, pat, cls, fix in SHAPES:
        n = sum(1 for r in rows if re.search(pat, r, re.I))       # DISTINCT ROWS, not matches
        if n < THRESHOLD and not show_all:
            continue
        # ⚠ EXISTENCE is checked; COVERAGE is not and cannot be cheaply. RLY37-1 measured
        # the old behaviour: `cls="banana"` suppressed the mark and still printed
        # "0 still have no class row", a sentence naming a file the code never read.
        bogus = bool(cls) and cls.split()[0] not in known
        mark = "!" if n >= THRESHOLD and (not cls or bogus) else " "
        shown = (cls + "  ⚠ NO SUCH ROW") if bogus else (cls or "— none —")
        print("  %-6s %-42s %6d%s %s" % (sid, name, n, mark, shown))
        if n >= THRESHOLD:
            # ⚠ `bogus` TRAVELS. `/rely` B2, 2026-09-16: it was computed here and consumed
            # only by this table, while both downstream consumers re-derived "is it classed?"
            # from `cls` being non-empty. A shape carrying a class id that names NO ROW then
            # counted as COVERED in the summary and lost its marker in the ranked list —
            # the same defect RLY37-1 fixed at the mark-and-string route, one ring out.
            flagged.append((sid, name, n, cls, fix, bogus))

    print("")
    if not flagged:
        print("  Nothing at or over %d distinct rows. Nothing to propose." % THRESHOLD)
        return 0

    # ── THE STANDING QUESTION ────────────────────────────────────────────────────────────────
    # Tim, 2026-08-10: *"what should we be doing here and now to make the next run better? that's
    # the question that I'm going to keep wanting to ask."* So it is answered on every run, in the
    # imperative, ranked — rather than left as a table the reader has to turn into actions.
    # UNCLASSED means "has no row you can go and read" — no id at all, OR an id naming no row.
    # Collapsing the second into the first is what made the summary sentence false.
    uncl = [f for f in flagged if not f[3] or f[5]]
    print("  " + "=" * 74)
    print("  %s — ranked, most leverage first" % ACTIONS_HEADING)
    print("  " + "=" * 74)
    for i, (sid, name, n, cls, fix, bogus) in enumerate(
            sorted(flagged, key=lambda f: (bool(f[3]) and not f[5], -f[2])), 1):
        flag = ("  " + MARK_NO_ROW if not cls else
                ("  ← %s %s" % (cls.split()[0], MARK_NAMES_NO_ROW)) if bogus else "")
        print("  %d. [%s] %s — %d row(s)%s" % (i, sid, name, n, flag))
        print("     %s" % fix)
    print("")
    print("  %d %s; %d have no class row to read in DEFECT_CLASSES.md"
          % (len(flagged), SUMMARY_TAG, len(uncl)))
    print("  (no id at all, or an id naming no row — both leave the reader with nowhere to go).")
    print("  A class row is worth adding only where the DETECTOR transfers to a question nobody")
    print("  has asked yet — otherwise it is a label, and this register has been through six.")
    print("")
    print("  ⚠ Counts are DISTINCT LEDGER ROWS, but they are still a READING LIST, not a finding")
    print("    list: two rows may describe one incident. Read them before acting on a number.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
