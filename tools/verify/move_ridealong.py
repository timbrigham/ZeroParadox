# -*- coding: utf-8 -*-
"""Move oversized module-doc sections into a `Foo.md` ride-along — BYTE-IDENTICALLY.

⭐ WHY BYTE-IDENTICAL IS THE WHOLE POINT (Tim, 2026-08-22: *"I like the idea of a byte identical
migration into the MD files… some future iteration might involve refactoring those files, but making
that into a separate action I think is the defensible course"*).

**A move that changes no bytes needs no prose review.** Editorial and adversary exist to assess
claims; if the claim is character-for-character what it already was, there is nothing to assess and
the diff proves it. Fusing a move with a rewrite destroys that property — a reviewer can no longer
tell what MOVED from what CHANGED, so the whole migration inherits the review cost of a rewrite.
Measured on the first one done by hand (`Kruskal.md`, `642d334`): the two were fused, and the result
needs a full prose pass it would otherwise not have needed.

So this tool performs the MOVE and refuses to perform the REWRITE. Refactoring a ride-along after it
lands is a separate, separately-reviewable action.

⚠⚠ THE TOOL DECIDES NOTHING. Which sections move is judgement — `CLAUDE.md` requires ONE LINE of
consequence at the site plus a pointer, never a bare pointer and never a paraphrase, and no script
can tell which sentence a reader standing there actually needs. Pass the sections explicitly. This
executes and VERIFIES; the selection comes from a human or an agent.

⚠⚠ IT REFUSES WHEN A MOVE WOULD RE-KEY A FROZEN BASELINE, AND THAT CASE IS REAL, NOT THEORETICAL.
`check_modal` and `check_pov` key their baselines by PATH (`<rel>|<phrase>`). Moving a grandfathered
modal claim from `Foo.lean` to `Foo.md` therefore turns one baseline entry into a DIFFERENT one —
an ADDITION to a frozen baseline, which `common.refuse_baseline_write` exists to forbid. The claim
must be FIXED (state its evidence at the site) or STAY in the `.lean`. Measured on `Kruskal.lean`,
which was exactly this case.

⚠ `check_prose` has the opposite behaviour and it is why this tool helps at all: ride-alongs are
counted in the ratio but NOT capped per block, so a moved prose block's violation dissolves rather
than moving. No key is re-added.

⚠ PRS-10, the laundering fence: moving an essay into a file no checker scans would take the block
under cap, improve every counter, and reduce unverified liability by exactly zero. So this tool
ASSERTS the destination is in `common.targets()` before it writes anything — the ride-along
convention is `Foo.md` beside `Foo.lean` and it must be TRACKED to be scanned.

Usage (this tool prints its own invocation path; never hardcode one):
  move_ridealong.py <file.lean> --list
  move_ridealong.py <file.lean> --move "## Section A" "## Section B"
  move_ridealong.py <file.lean> --move ... --apply     # without --apply it is a dry run
"""
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402
import vendored                                                  # noqa: E402
import check_prose                                               # noqa: E402
import check_modal                                               # noqa: E402
import check_pov                                                 # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
REPO = str(common.REPO)

TAKE_RE = re.compile(r"^#{1,3}\s+Engineer's Take", re.I)
HEADING = re.compile(r"^#{1,3}\s+\S")


def block_span(lines):
    """(start, end) of the module-doc block, or None. `start` is the `/-!` line."""
    for i, l in enumerate(lines):
        if l.strip().startswith("/-!"):
            j = i + 1
            while j < len(lines) and "-/" not in lines[j]:
                j += 1
            return (i, j) if j < len(lines) else None
    return None


def sections(lines, start, end):
    """[(heading, first_line, last_line)] inside the block. The pre-heading preamble is index 0."""
    out, cur = [], ("(preamble)", start + 1)
    for k in range(start + 1, end):
        if HEADING.match(lines[k].strip()):
            out.append((cur[0], cur[1], k - 1))
            cur = (lines[k].strip(), k)
    out.append((cur[0], cur[1], end - 1))
    return out


def is_take(heading):
    return bool(TAKE_RE.match(heading))


def _line_of(loc):
    """`rel:123` -> 123, or None."""
    m = re.search(r":(\d+)\s*$", str(loc))
    return int(m.group(1)) if m else None


def baselined_claims_in(src_rel, ranges):
    """Grandfathered modal/POV sites inside the moved LINE RANGES — what a move would RE-KEY.

    ⚠ THIS IS THE REFUSAL CONDITION. Both checkers key by PATH (`<rel>|<phrase>` for modal,
    `<rel>::<digest>` for POV), so relocating a grandfathered site turns its entry into a DIFFERENT
    entry — an ADDITION to a frozen baseline, which `common.refuse_baseline_write` forbids.

    ⚠⚠ IT ASKS THE CHECKERS, AND IT USES THEIR LINE NUMBERS. The first version of this function
    matched `check_modal` by re-deriving a key from free text and did nothing at all for
    `check_pov` — it looped over the baseline, executed `pass`, and reported a failure branch that
    could never fire. A check that cannot fail is not a check; that is the defect class this whole
    bundle exists to catch, committed inside the tool written to help drain it. Both halves now run
    the real scanners and filter by line, so a site is either provably inside a moved range or it is
    not.

    ⚠ FAIL-CLOSED: anything that cannot be resolved to a line is reported as blocking."""
    found = []
    lo_hi = list(ranges)

    def inside(n):
        return n is not None and any(a <= (n - 1) <= b for a, b in lo_hi)

    mbase = check_modal.load_baseline()
    for hit in check_modal.scan():
        rel, line, phrase = hit[0], hit[1], hit[2]
        if rel != src_rel:
            continue
        if check_modal.key((rel, line, phrase)) in mbase and inside(line):
            found.append(("check_modal", "%s:%s  %r" % (rel, line, phrase)))

    pbase = check_pov.load_baseline()
    untagged, _tagged, _denials = check_pov.scan()
    for k, loc, sn in untagged:
        if not str(loc).startswith(src_rel + ":"):
            continue
        n = _line_of(loc)
        if k in pbase and (n is None or inside(n)):
            found.append(("check_pov", "%s  %s" % (loc, str(sn)[:60])))
    return found


def main():
    argv = sys.argv[1:]
    if not argv:
        print(__doc__.strip().splitlines()[0])
        print("usage: python %s <file.lean> --list | --move \"## A\" [...] [--apply]" % SELF)
        return 2
    src = argv[0]
    rel = os.path.relpath(os.path.abspath(src), REPO).replace("\\", "/")
    if not os.path.exists(src):
        print("no such file: %s" % src)
        return 2
    lines = io.open(src, encoding="utf-8").read().split("\n")
    span = block_span(lines)
    if not span:
        print("%s has no module-doc block" % rel)
        return 2
    start, end = span
    secs = sections(lines, start, end)
    length, unclosed = check_prose.countable_block_lines(lines, start, end)

    print("=" * 64)
    print("  ride-along migration — %s" % rel)
    print("=" * 64)
    print("  block            : lines %d-%d" % (start + 1, end + 1))
    print("  counted          : %d (cap %d)%s"
          % (length, check_prose.BLOCK_CAP,
             "  OVER" if length > check_prose.BLOCK_CAP else "  under cap already"))
    print("  Take unclosed    : %s" % unclosed)
    print("  sections:")
    for h, a, b in secs:
        print("      %-52s lines %4d-%-4d  %s"
              % (h[:52], a + 1, b + 1, "** THE TAKE — NEVER MOVES **" if is_take(h) else ""))

    if "--move" not in argv:
        print("\n  (--list only; pass --move \"## Section\" ... to migrate)")
        return 0

    wanted = [a for a in argv[argv.index("--move") + 1:] if not a.startswith("--")]
    chosen = [(h, a, b) for h, a, b in secs if h in wanted]
    missing = [w for w in wanted if w not in [h for h, _a, _b in secs]]
    if missing:
        print("\n  REFUSED — no such section(s): %s" % ", ".join(missing))
        return 2
    if any(is_take(h) for h, _a, _b in chosen):
        print("\n  REFUSED — the Engineer's Take is Tim's voice and never moves.")
        return 2

    moved_text = "\n".join("\n".join(lines[a:b + 1]) for _h, a, b in chosen)

    # ⚠ THE REFUSAL CHECK, BEFORE ANYTHING IS WRITTEN.
    dest_rel = rel[:-5] + ".md"
    blocked = baselined_claims_in(rel, [(a, b) for _h, a, b in chosen])
    if blocked:
        print("\n  REFUSED — the moved text carries a GRANDFATHERED claim, and moving it would")
        print("  re-key a FROZEN baseline (an addition, which the freeze forbids):")
        for who, k in blocked:
            print("      %-12s %s" % (who, k))
        print("  Fix the claim at its site (state the evidence) or leave the section in the .lean.")
        return 1

    # PRS-10: the destination must actually be scanned, or this is laundering.
    dest_abs = os.path.join(REPO, dest_rel.replace("/", os.sep))
    scanned = any(r == dest_rel for _p, r in
                  common.targets(is_vendored=vendored.is_vendored))
    print("\n  destination      : %s" % dest_rel)
    print("  currently scanned: %s%s"
          % (scanned, "" if scanned else "  (new file — MUST be `git add`ed to be scanned)"))
    print("  moving %d section(s), %d bytes" % (len(chosen), len(moved_text)))

    if "--apply" not in argv:
        print("\n  DRY RUN — pass --apply to write.")
        return 0

    # ⚠⚠ THE HEADER USED TO SAY "carries the review status it already had", AND THAT SENTENCE WAS
    # THE WHOLE ERROR (Tim, 2026-08-22: *"just moving the content from the lean file to a MD file
    # does not mean that we don't analyze it and make sure that the claims that it's making are
    # accurate"*). Grandfathered content is not reviewed-and-fine; a baseline entry IS the record
    # that a site was let through UNEXAMINED. So a byte-identical move preserves *unexamined*, and
    # saying it "carries its review status" launders an absence into an approval.
    header = ("# %s — ride-along documentation\n\nMoved from `%s`. ⚠ **This content was "
              "GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was "
              "let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are "
              "unverified until a claim review says otherwise.\n\n"
              % (os.path.basename(rel)[:-5], rel))
    existing = io.open(dest_abs, encoding="utf-8").read() if os.path.exists(dest_abs) else header
    io.open(dest_abs, "w", encoding="utf-8", newline="\n").write(existing + moved_text + "\n")

    keep = [l for i, l in enumerate(lines)
            if not any(a <= i <= b for _h, a, b in chosen)]
    io.open(src, "w", encoding="utf-8", newline="\n").write("\n".join(keep))

    # ⚠⚠ THE INVARIANT, ASSERTED AFTER THE WRITE. This is the deliverable, not the move.
    written = io.open(dest_abs, encoding="utf-8").read()
    ok = moved_text in written
    print("\n  BYTE-IDENTICAL: %s" % ("yes — the moved text appears verbatim in the destination"
                                      if ok else "*** NO — the destination does not contain the "
                                                 "moved bytes; REVERT THIS ***"))
    # ⚠⚠ STEP 1 OF 2, AND THE TOOL MUST NOT LET THIS READ AS DONE. `check_prose` measures prose
    # VOLUME, not truth: getting a block under cap says nothing about whether its claims hold. The
    # baseline entry records "unexamined", so deleting it because a VOLUME check went green retires
    # the evidence of a liability without discharging it — `PRS-10`, which is precisely "satisfying
    # the metric without touching the property". Measured on the first migration done by hand
    # (`Kruskal.md`): the entry was removed on a green volume check and the claims had still never
    # been read by anything.
    print("""
  ================= STEP 1 OF 2 — THE MOVE IS DONE, THE LIABILITY IS NOT =================
  This content was GRANDFATHERED, i.e. never examined. Moving it changed nothing about that.

  DO NOT remove the baseline entry yet. `check_prose` going green measures VOLUME, not TRUTH;
  removing the entry on that basis deletes the record of an unexamined claim without examining
  it.

  REQUIRED NEXT:  /claim-review <the destination .md>
                  - verify every external attribution against the source, not against the
                    file's own confidence
                  - the baseline entry becomes removable only after that verdict
  ========================================================================================""")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
