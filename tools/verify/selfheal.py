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

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
PRIV = os.path.join(REPO, ".claude-local")
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")
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

# id, name, pattern, existing class (or None), the process change worth considering
SHAPES = [
    ("SH-1", "exit status not propagated",
     r"exit code|exit status|propagate|\$\?",
     "DC-10 (partial)",
     "Require every new shell/subprocess wiring to ship with a control that makes the child FAIL "
     "and asserts the caller sees non-zero. Three instances so far were found by reading, not by a test."),
    ("SH-2", "encoding / BOM / codepage",
     r"\bascii\b|BOM|cp1252|UnicodeEncode|line_buffering|em-dash",
     None,
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
     None,
     "One definition, imported. If two languages need it, one of them delegates. Measured cost so "
     "far: two hook implementations, two vendored rules, two ways to spawn agents."),
    ("SH-8", "report/manifest claims more than it does",
     r"manifest .{0,20}lie|claims? .{0,25}BLOCK|advisory .{0,20}blocked|reads as (a )?confirmation",
     None,
     "The manifest is generated FROM the same table the runner iterates, so it cannot describe a "
     "plan the code does not execute."),
]


def read(p):
    return io.open(p, encoding="utf-8", errors="replace").read() if os.path.exists(p) else ""


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
    rows = len(re.findall(r"^\| \*\*", ledger, re.M))
    known = sorted(set(re.findall(r"DC-\d+", classes)),
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
        mark = "!" if n >= THRESHOLD and not cls else " "
        print("  %-6s %-42s %6d%s %s" % (sid, name, n, mark, cls or "— none —"))
        if n >= THRESHOLD:
            flagged.append((sid, name, n, cls, fix))

    print("")
    if not flagged:
        print("  Nothing at or over %d distinct rows. Nothing to propose." % THRESHOLD)
        return 0

    # ── THE STANDING QUESTION ────────────────────────────────────────────────────────────────
    # Tim, 2026-08-10: *"what should we be doing here and now to make the next run better? that's
    # the question that I'm going to keep wanting to ask."* So it is answered on every run, in the
    # imperative, ranked — rather than left as a table the reader has to turn into actions.
    uncl = [f for f in flagged if not f[3]]
    print("  " + "=" * 74)
    print("  WHAT TO DO BEFORE THE NEXT RUN — ranked, most leverage first")
    print("  " + "=" * 74)
    for i, (sid, name, n, cls, fix) in enumerate(
            sorted(flagged, key=lambda f: (bool(f[3]), -f[2])), 1):
        print("  %d. [%s] %s — %d row(s)%s" % (i, sid, name, n,
                                               "" if cls else "  ← NO CLASS ROW"))
        print("     %s" % fix)
    print("")
    print("  %d shape(s) over threshold; %d still have no class row in DEFECT_CLASSES.md."
          % (len(flagged), len(uncl)))
    print("  A class row is worth adding only where the DETECTOR transfers to a question nobody")
    print("  has asked yet — otherwise it is a label, and this register has been through six.")
    print("")
    print("  ⚠ Counts are DISTINCT LEDGER ROWS, but they are still a READING LIST, not a finding")
    print("    list: two rows may describe one incident. Read them before acting on a number.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
