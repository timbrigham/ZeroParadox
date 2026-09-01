# -*- coding: utf-8 -*-
"""Enumerate everything that touches the /rely routing decision — A SCREEN, NEVER A GATE.

⚠⚠ THIS FILE DOES NOT VOTE, AND THAT IS THE ENTIRE DESIGN. It is not in the blocking roster, no hook
runs it, and nothing adds its exit code to `bad`. It is registered in `agent_gate.py`, which wraps it
in an agent that writes a defect file and returns no verdict on the push (`CLAUDE.md` rung 5: the
screen may replace the ENUMERATION, it may never replace the VERDICT).

⭐ WHY IT EXISTS, AND THE MEASUREMENT IS THE WHOLE ARGUMENT. `guards.py` used to answer *"does every
consumer of `check_routing` honour the blocking flag?"* by reading source. Three versions, six
defeats: a whole-file substring matched comments; a 12-line window contained the token by
construction; an AST walk lost consumers to one space before an argument list, to a list
comprehension, to a `list(...)` wrapper, and passed a `print(blocking)` that reads the flag and obeys
nothing. Each repair closed the holes its author thought of and the next reader found different ones
— rung 5's tell exactly.

**The question splits, and the two halves have different natures:**

  * *"Do the KNOWN enforcement surfaces obey the flag?"* — FINITE. Two surfaces, both callable. That
    stays in `guards.py`, it is behavioural (drive them, read the answer back), and it BLOCKS. A
    fail-open leg is never downgraded, however many rounds it costs.
  * *"Is there a THIRD consumer nobody registered?"* — UNBOUNDED. It can never prove itself done and
    its own repairs re-arm it. That is an enumeration leg, and it is what this file carries.

**Why an unregistered consumer cannot silently weaken the push:** enforcement is not a vote among
consumers. The push path is fixed — `.git/hooks/pre-push` → `hooks.py` → `batch.py prepush` →
`cmd_prepush` (and the hook plan itself is guarded separately), and the release path is
`ship.required_gates`. A new consumer is ADDITIVE: it can fail to enforce, but it cannot dis-enforce
the two that do, and both of those are behaviourally pinned. So incompleteness here is a coverage
gap worth reading about, not a hole work escapes through — which is precisely the split that makes
downgrading this half legitimate and downgrading the other half forbidden.

⚠ IT IS DELIBERATELY OVER-INCLUSIVE. It matches raw text, not the parse tree, because a screen that
misses is useless and a screen that over-flags is merely read. Precision is the reader's job.
"""
import io
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
REPO = str(common.REPO)

SKIP = {".git", ".lake", ".claude-local", "node_modules", "__pycache__", ".venv"}
NEEDLES = ("check_routing", "routing_verdict", "routing_bad", "_LEG_BLOCKING")

# ⚠ AN ALLOWLIST, SO A NEW CONSUMER FAILS OPEN INTO THE REPORT RATHER THAN OUT OF IT. Adding a file
# here is a deliberate act that shows up in a diff; the previous design discovered consumers and so
# could silently stop finding one. Each entry states WHY it is allowed to touch the decision.
PINNED = {
    "tools/verify/batch.py":
        "DEFINES the decision (check_routing, routing_bad, routing_verdict) and consumes it in "
        "cmd_prepush — the push gate. Behaviourally pinned by guards.py ROUTE 5.",
    "tools/verify/ship.py":
        "The RELEASE gate: required_gates turns a blocking row into a demanded /rely signal. "
        "Behaviourally pinned by guards.py ROUTE 3.",
    "tools/verify/guards.py":
        "The control itself — it drives both surfaces with synthetic rows.",
    "tools/verify/scan_routing_consumers.py":
        "This screen.",
    "tools/verify/probe_routing_behavioural.py":
        "The mutation control: it NEUTERS both surfaces on purpose, in a throwaway worktree, and "
        "requires guards.py to go red on each.",
    "tools/verify/agent_gate.py":
        "Registers this screen; names it in the registry only.",
    # ⚠ `report.py` WAS PINNED HERE AND IS NOT ANY MORE — it formats the manifest line that
    # announces the routing legs, but it does not reference the decision by name, so the pin was
    # describing a relationship that does not exist. The ZERO-sites warning below is what surfaced
    # it, on this file's first run. A stale pin is not harmless: it is a standing licence for a file
    # to touch the decision without ever appearing as UNREGISTERED. If `report.py` ever does
    # reference it, it should show up here as unregistered and be READ, not waved through by a line
    # written months earlier for a different reason.
}


def scan():
    hits = []
    scanned = 0
    for dirpath, dirs, names in os.walk(REPO):
        dirs[:] = [d for d in dirs if d not in SKIP]
        for n in names:
            if not n.endswith(".py"):
                continue
            p = os.path.join(dirpath, n)
            rel = os.path.relpath(p, REPO).replace("\\", "/")
            scanned += 1
            try:
                lines = io.open(p, encoding="utf-8", errors="replace").read().splitlines()
            except OSError as e:
                hits.append((rel, 0, "UNREADABLE", repr(e)))
                continue
            for i, line in enumerate(lines, 1):
                if any(t in line for t in NEEDLES):
                    hits.append((rel, i, "PINNED" if rel in PINNED else "UNREGISTERED",
                                 line.strip()[:150]))
    return scanned, hits


def main():
    scanned, hits = scan()
    unreg = [h for h in hits if h[2] == "UNREGISTERED"]
    unread = [h for h in hits if h[2] == "UNREADABLE"]

    print("%s — routing-decision consumers (SCREEN, advisory; this file never blocks)" % SELF)
    print("  scanned            : %d .py file(s) under %s" % (scanned, REPO))
    print("  needles            : %s" % ", ".join(NEEDLES))
    print("  reference sites    : %d" % len(hits))
    print()
    print("  PINNED surfaces, and why each is permitted to touch the decision:")
    for rel in sorted(PINNED):
        n = len([h for h in hits if h[0] == rel])
        print("    %-42s %3d site(s)  %s" % (rel, n, PINNED[rel]))
        if n == 0:
            print("      ** ZERO sites — this surface is pinned but no longer references the "
                  "routing decision at all. Either it was neutered or the allowlist is stale. **")
    print()
    print("  UNREGISTERED: %d" % len(unreg))
    for rel, lineno, _k, text in unreg:
        print("    %s:%d  %s" % (rel, lineno, text))
    if unread:
        print("  UNREADABLE: %d" % len(unread))
        for rel, _l, _k, text in unread:
            print("    %s  %s" % (rel, text))

    # ⚠ A NON-ZERO EXIT HERE IS A READING LIST, NOT A BLOCK. `agent_gate` turns it into a written
    # diagnosis; `bad` and the push exit code are untouched by construction.
    return 1 if (unreg or unread) else 0


if __name__ == "__main__":
    sys.exit(main())
