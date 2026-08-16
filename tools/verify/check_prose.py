#!/usr/bin/env python
"""check_prose.py - the prose-volume gate for Lean sources.

Tim, 2026-08-08: "apart from the engineer's take, I don't think there should be more
prose than code as a general rule counted by line numbers."

WHY THIS IS MECHANICAL AND NOT A DISCIPLINE. Code is kernel-checked; prose is unchecked
by construction, so the prose:code ratio is the ratio of verified asset to unverified
liability. Measured across three gate rounds on 2026-08-08: roughly twelve findings, ALL
of them in prose, NONE in a theorem statement - and an 82-line cut then passed all three
gates with nothing load-bearing lost. This is the sixth convention of this shape in the
project and the previous five all leaked until they were enforced.

TWO PRONGS, because a per-file line count is gameable by adding code and does not point
at where the essays actually live:

  1. DOCSTRING  - a `/-- ... -/` must not be longer than the declaration it documents.
  2. BLOCK      - a `/-! ... -/` module-doc block must not exceed BLOCK_CAP lines.
  3. FILE RATIO - reported, never enforced. It is the signal, not the target.

The Engineer's Take is EXEMPT (Tim's voice, and the only corpus written in the register
a question arrives in - `where.py` reports Takes for exactly that reason).

Baselined like check_pov.py / check_classes.py: fires on NEW and EDITED sites only.
Shrink the baseline as files are touched; never grow it deliberately.

The exact invocation path is printed in this tool's own output; it is never written down here.

  check_prose.py              # WARN  (pre-commit)
  check_prose.py --block      # BLOCK (pre-push)
  check_prose.py --baseline   # regenerate, only after a real audit
  check_prose.py --selftest   # must-fire AND must-suppress controls
"""

import hashlib
import io
import os
import re
import sys

# The report lines quote corpus prose, which contains the framework's glyphs. On a Windows console
# stdout defaults to cp1252 and `print` of a bottom sign raises UnicodeEncodeError - so the checker
# exits 1 having gated NOTHING, and `batch.py precommit` reports that crash as a checker FAILURE.
# The failure is indistinguishable from a real violation and blocks a clean commit; a crash landing
# earlier would instead truncate the findings list and look like a completed run. Same fix, same
# reason, as report.py:34.
sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)

# Roots. HERE is this bundle (public, tracked); the baseline travels WITH the checker. SELF is
# derived, never written down — a hardcoded invocation path is a copy of the path, and copies drift.
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
SRC = str(common.SRC)
SELF = common.self_rel(__file__)
BASELINE = os.path.join(HERE, "prose_baseline.txt")

"""Tim's design, 2026-08-08, which is the rule this file enforces:

    "I'm not a big fan of having just a giant header block full of prose. Usually it's a
     short summary of what the file is supposed to be doing as a whole, no more than a
     few sentences, and only once you actually get into the individual lines, do you have
     a statement of what that exact line is supposed to be doing."

Measured the same day, and the corpus ALREADY does this nearly everywhere - file-header
blocks run p50 1 line, p75 3, p90 7; section blocks p50 1, p75 6, p90 14; and 85% of
declarations already carry a docstring. This is outlier control, not a migration. The cap
is set just above the p90 for file headers so the normal case is untouched and the
essays - 121, 115, 100, 83 lines - are what it bites.
"""

BLOCK_CAP = 10   # "a few sentences": above p90 for file headers (7), under p90 for sections (14)

TAKE_RE = re.compile(r"#+\s*Engineer'?s\s+Take", re.I)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b"
    r"(?:\s+([A-Za-z_À-￿][^\s:({\[]*))?"
)
CHECK_RE = re.compile(r"^\s*#check\s+(.+?)\s*(?:--\s*(.*))?$")
# CLAUDE.md's standing convention: every gloss is Statement: (what the decl proves) or
# Reading: (the framework's interpretation, explicitly not a claim about the theorem).
LABEL_RE = re.compile(r"^\**\s*(Statement|Reading)\b\s*\**\s*:", re.I)
# a line that ends the previous declaration's body by starting a new top-level construct
BOUNDARY_RE = re.compile(
    r"^(?:@\[|/--|/-!|end\b|section\b|namespace\b|open\b|variable\b|attribute\b|import\b|#|"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b)"
)


def _read(path):
    return io.open(path, encoding="utf-8", errors="replace").read().split("\n")


# Third-party code is EXEMPT STRUCTURALLY, not baselined. The rule now lives in ONE place —
# `vendored.py` — because it was re-implemented from memory in batch.py and the copy was
# already wrong three ways after a day. Import it; never restate it.
from vendored import is_vendored  # noqa: E402  (VENDOR_RE and the head window live there)


def scan_file(path, rel):
    """Yield (kind, key, actual, limit, line, detail) violations for one file."""
    lines = _read(path)
    n = len(lines)
    out = []
    i = 0
    while i < n:
        raw = lines[i]
        t = raw.strip()

        if t.startswith("/-!"):
            start = i
            if "-/" in t[3:]:
                i += 1
                continue
            j = i + 1
            while j < n and "-/" not in lines[j]:
                j += 1
            # Measure the block EXCLUDING its Engineer's Take section, rather than exempting
            # the whole block when a Take is present. Exempting wholesale is a loophole: any
            # amount of essay hides by sitting in the same block as the Take, which is exactly
            # how the corpus is laid out. Found 2026-08-08 while writing compliant content.
            length, take_unclosed = countable_block_lines(lines, start, j)
            key = block_key(rel, lines, start, j)
            if length > BLOCK_CAP:
                out.append(("block", key, length, BLOCK_CAP, start + 1,
                            "module-doc block (excluding the Take)"))
            # ⚠ INDEPENDENT `if`, never `elif` (RLY11-1, 2026-08-12). Written first as `elif`,
            # which made the two conditions alternatives: a block that was BOTH over cap AND
            # latching reported only as `block`, and since 55 such blocks are baselined, `new`
            # excluded them and they printed NOWHERE. The checker announced `UNMEASURED: 10`
            # when the true figure was 65 — 397 prose lines unmeasured AND unnamed. That is
            # precisely the failure `takeopen` exists to prevent, reintroduced by the fix for
            # it. A block can be over cap on what IS measured and still hide a remainder;
            # they are orthogonal facts and each gets its own row.
            if take_unclosed:
                # Not a violation - a MEASUREMENT GAP, reported so it cannot go quiet (PRS-1).
                # The Take swallows the rest of the block, so `length` is a floor, not a count.
                out.append(("takeopen", key, length, BLOCK_CAP, start + 1,
                            "Engineer's Take runs to end of block - remainder NOT measured"))
            i = j + 1
            continue

        if t.startswith("/--"):
            start = i
            if "-/" in t[3:]:
                j = i
            else:
                j = i + 1
                while j < n and "-/" not in lines[j]:
                    j += 1
            doclen = j - start + 1
            name, body = decl_after(lines, j + 1, n)
            if name is not None and doclen > body:
                key = "%s::doc::%s" % (rel, name)
                out.append(("doc", key, doclen, body, start + 1,
                            "docstring on `%s`" % name))
            i = j + 1
            continue

        # an index line must justify ITSELF. A `#check` is a line item in a CannotBe-style
        # index; the reason it belongs there has to sit on the line, not in the header, or
        # nothing can be checked against it and no two items are distinguishable.
        cm = CHECK_RE.match(raw)
        if cm:
            target = cm.group(1).strip()
            gloss = (cm.group(2) or "").strip()
            labelled = bool(gloss) and bool(LABEL_RE.match(gloss))
            # Walk the WHOLE contiguous comment block above, not just one line: a gloss may
            # run several lines with its label on the first. Checking only the adjacent line
            # reports a correctly-labelled multi-line gloss as unlabelled (measured 2026-08-08
            # on the first file written to comply with this rule).
            k = i - 1
            while k >= 0 and not lines[k].strip():
                k -= 1
            while k >= 0 and lines[k].strip().startswith("--"):
                text = lines[k].strip().lstrip("-").strip()
                if text:
                    gloss = gloss or text
                    if LABEL_RE.match(text):
                        labelled = True
                k -= 1
            short = target.split()[-1].split(".")[-1][:48]
            if not gloss:
                out.append(("bare", "%s::bare::%s" % (rel, short), 0, 1, i + 1,
                            "`#check %s` has no gloss" % short))
            elif not labelled:
                out.append(("unlabelled", "%s::label::%s" % (rel, short), 0, 1, i + 1,
                            "gloss on `%s` carries no Statement:/Reading: label" % short))
            i += 1
            continue

        # RETIRED 2026-08-08: "a declaration must SAY what it does" is no longer debt.
        #
        # The rule demanded prose - it was the one check here that CREATED authoring work
        # rather than capping it, and authoring is where this corpus's defects come from
        # (measured across one arc: roughly one hand-written gloss in seven was false,
        # while deletions produced none). What it demanded is also now redundant: the
        # public CI run summary publishes every declaration's axiom footprint and the
        # build emits its elaborated signature, both regenerated per run and neither
        # hand-maintained. A docstring restating a signature is a second copy that can
        # drift; the artifact cannot.
        #
        # What this does NOT retire: the `bare` rule below still requires a gloss on a
        # `#check`, because the `CannotBe` index files are reader maps for people who do
        # not read Lean signatures, and a bare index line tells them nothing. 17 of the
        # 27 open bare sites are in those indexes and remain real debt.
        #
        # An interpretive docstring is still WELCOME everywhere - it is simply no longer
        # mandatory, and the caps on over-long ones are untouched.
        i += 1
    return out


def undocumented_exempt(lines, i):
    """A declaration is exempt when the line above it closes a docstring, or when it is
    a local helper (`private`) or an `example` - neither is part of the file's surface."""
    t = lines[i].strip()
    if t.startswith("example") or "private " in t[:40]:
        return True
    k = i - 1
    while k >= 0 and not lines[k].strip():
        k -= 1
    if k < 0:
        return False
    prev = lines[k].strip()
    if prev.endswith("-/"):
        return True
    if prev.startswith("@["):          # attribute line sits between doc and decl
        k -= 1
        while k >= 0 and not lines[k].strip():
            k -= 1
        return k >= 0 and lines[k].strip().endswith("-/")
    return False


def countable_block_lines(lines, start, end):
    """Length of a module-doc block with its Engineer's Take section removed.

    The Take runs from its heading to the next EXPLICIT DELIMITER - a markdown heading, or a
    `---` horizontal rule - or to the end of the block. Everything else counts against the cap.

    Returns (count, take_unclosed).

    PRS-1, 2026-08-12: the `---` delimiter and the `take_unclosed` flag are BOTH new. Before
    them the exemption LATCHED: once a Take opened, only a heading closed it, so a block whose
    Take was followed by no heading was never measured at all. Measured blast radius when
    found: 13 files, 244 prose lines. `BoundaryBridge.lean` reported 3 lines against a cap of
    10 for a 27-line block - a clean zero that meant nothing.

    Why the pre-existing selftest missed it: its must-fire control put the essay BEFORE the
    Take. The uncovered shape was essay AFTER it. `CLAUDE.md`'s own rule - plant the probe in
    the shape you actually expect - applied to this file and had not been.

    Why a blank line does NOT close the Take: Takes contain paragraphs. And the Take is Tim's
    voice, so where his prose ends is not this checker's call to make. A bare continuation is
    genuinely indistinguishable from a long Take, so that case is REPORTED (`take_unclosed`)
    rather than silently exempted - the same design as the `Idiom:` label, which is a
    suppression mechanism made countable so rubber-stamping shows up as a rising number
    instead of going quiet.
    """
    count = 0
    in_take = False
    saw_take = False
    closed = False
    for k in range(start, min(end + 1, len(lines))):
        t = lines[k].strip()
        if TAKE_RE.search(t):
            in_take = True
            saw_take = True
            continue
        if in_take and (re.match(r"^#{1,3}\s+\S", t) or re.match(r"^-{3,}\s*$", t)):
            in_take = False
            closed = True
        if in_take:
            continue
        count += 1
    return count, (saw_take and not closed)


def block_key(rel, lines, start, end):
    """Key a block by a hash of its CONTENT, not its line number.

    Two properties, both wanted. It survives the block moving within the file, so an
    unrelated edit above does not re-fire it. And it CHANGES when the block is edited,
    so a grandfathered block that gets touched must come under the cap - which is the
    baseline-shrinking rule enforced rather than remembered.
    """
    body = "\n".join(lines[start:min(end + 1, len(lines))])
    digest = hashlib.sha256(body.encode("utf-8", "replace")).hexdigest()[:12]
    head = ""
    for k in range(start, min(end + 1, len(lines))):
        s = lines[k].strip().lstrip("/-!").strip().lstrip("#").strip().strip("* ").strip()
        if s and not s.startswith("-/"):
            # strip AFTER truncation: a key ending in whitespace is destroyed by the
            # .strip() on baseline read-back, so it would never match itself
            head = s[:48].strip()
            break
    return "%s::block::%s::%s" % (rel, digest, head)


def decl_after(lines, k, n):
    """Name and body-line-count of the declaration following a docstring."""
    while k < n and not lines[k].strip():
        k += 1
    if k >= n:
        return None, 0
    m = DECL_RE.match(lines[k])
    if not m:
        return None, 0
    name = m.group(2) or "<anonymous>"
    body = 0
    k2 = k
    while k2 < n:
        s = lines[k2]
        st = s.strip()
        if not st:
            k2 += 1
            continue
        if body > 0 and not s.startswith((" ", "\t")) and BOUNDARY_RE.match(st):
            break
        body += 1
        k2 += 1
    return name, max(body, 1)


def file_ratio(path):
    """(prose, code) excluding blank lines and the Engineer's Take."""
    lines = _read(path)
    prose = code = 0
    in_block = False
    in_take = False
    for ln in lines:
        t = ln.strip()
        if not t:
            continue
        if TAKE_RE.search(t):
            in_take = True
        elif in_take and re.match(r"^#{1,3}\s+\S", t) and not TAKE_RE.search(t):
            in_take = False
        if in_block:
            if not in_take:
                prose += 1
            if "-/" in t:
                in_block = False
            continue
        if t.startswith("/-"):
            if not in_take:
                prose += 1
            if "-/" not in t[2:]:
                in_block = True
            continue
        if t.startswith("--"):
            if not in_take:
                prose += 1
            continue
        code += 1
    return prose, code


def all_files(include_vendored=False):
    for dirpath, _, filenames in os.walk(SRC):
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, REPO).replace("\\", "/")
                if not include_vendored and is_vendored(p, rel):
                    continue
                yield p, rel


def vendored_files():
    out = []
    for dirpath, _, filenames in os.walk(SRC):
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, REPO).replace("\\", "/")
                if is_vendored(p, rel):
                    out.append(rel)
    return out


def load_baseline():
    return common.load_baseline(BASELINE)


def run(block_mode=False, write_baseline=False):
    viols = []
    tot_p = tot_c = 0
    worst = []
    takeopen = []
    for path, rel in all_files():
        # `takeopen` is a MEASUREMENT GAP, never a violation (PRS-1). It must not enter
        # `viols`: it would block on 13 files at once for prose nobody has read, and it is
        # not a claim that anything is over cap - it is a statement that the remainder of the
        # block was not measured at all. Reported unconditionally and never baselined, on the
        # same principle as `check_pov.py`'s DENIAL pattern: a convention with a forbidden
        # form must detect the form itself, not merely the absence of the required one.
        for v in scan_file(path, rel):
            (takeopen if v[0] == "takeopen" else viols).append(v)
        p, c = file_ratio(path)
        tot_p += p
        tot_c += c
        if c and p > c:
            worst.append((rel, p, c))

    if write_baseline:
        with io.open(BASELINE, "w", encoding="utf-8", newline="\n") as f:
            f.write("# check_prose.py baseline - prose sites grandfathered at creation.\n")
            f.write("# SHRINK as files are touched; never grow deliberately.\n")
            f.write("# Regenerate with --baseline ONLY after a real audit.\n")
            for k in sorted(set(v[1] for v in viols)):
                f.write(k + "\n")
        print("baseline written: %d keys" % len(set(v[1] for v in viols)))
        return 0

    base = load_baseline()
    new = [v for v in viols if v[1] not in base]

    vend = vendored_files()
    print("=" * 40)
    print("  prose-volume check")
    if vend:
        print("  EXEMPT (third-party backport, not ours to edit): %d file(s)" % len(vend))
        for v in vend:
            print("      %s" % v)
    print("  corpus prose/code (Takes excluded): %.2f  (%d / %d)"
          % (tot_p / max(tot_c, 1), tot_p, tot_c))
    print("  files where prose exceeds code:     %d" % len(worst))
    print("  block cap: %d lines   sites over: %d" % (BLOCK_CAP, len(viols)))
    KINDS = [("block", "module-doc blocks over cap"),
             ("doc", "docstrings longer than their decl"),
             ("bare", "#check with no gloss"),
             ("unlabelled", "gloss with no Statement:/Reading:")]
    for k, desc in KINDS:
        tot = sum(1 for v in viols if v[0] == k)
        if tot:
            print("      %-34s %4d" % (desc, tot))
    print("  grandfathered (baseline):           %d" % len(base))
    print("  NEW oversized prose sites:          %d" % len(new))
    if takeopen:
        # NEVER baselined, NEVER blocking - but never silent either. A rising number here
        # means more of the corpus has stopped being measured (PRS-1).
        over = set(v[1] for v in viols if v[0] == "block")
        gap_only = [v for v in takeopen if v[1] not in over]
        print("  ---- MEASUREMENT GAPS (not violations, not baselined) ----")
        print("  Take runs to end of block, remainder UNMEASURED: %d" % len(takeopen))
        # The split matters: a block already listed as over-cap is at least NAMED somewhere,
        # while a gap-only block is invisible in every other line of this report.
        print("      of which also over cap (counted above):      %d" % (len(takeopen)
                                                                        - len(gap_only)))
        print("      gap ONLY - named nowhere else:               %d" % len(gap_only))
        # ⚠ Name EVERY gapped block, not just the gap-only ones (RLY12-1). Listing only
        # `gap_only` left the 55 over-cap-and-latching blocks counted but UNNAMED - and
        # "unmeasured AND unnamed" is the defect this report exists to end, so a summary count
        # reproduced it one level down. It also made the guard detector unbuildable: there was
        # no line naming the planted block to key on.
        # ⚠ Name the BLOCK, not just the file (RLY12-2). Keyed on the file alone, an unrelated
        # gap-only block elsewhere in the same file satisfies any predicate watching this line -
        # reproduced. The block title is what makes the row identify one block.
        for _k, key, _a, _l, line, _d in sorted(takeopen, key=lambda v: v[1]):
            parts = key.split("::")
            title = parts[3][:44] if len(parts) > 3 else ""
            print("      %s:%d  [%s]  (%s) close the Take with `---` or a heading"
                  % (parts[0], line, title,
                     "gap only" if key not in over else "also over cap"))
    print("=" * 40)

    for kind, key, actual, limit, line, detail in sorted(new, key=lambda v: -(v[2] - v[3])):
        rel = key.split("::")[0]
        if kind == "doc":
            print("  %s:%d  %s is %d lines on a %d-line declaration"
                  % (rel, line, detail, actual, limit))
        elif kind in ("undoc", "bare", "unlabelled"):
            print("  %s:%d  %s" % (rel, line, detail))
        else:
            print("  %s:%d  %s is %d lines (cap %d)"
                  % (rel, line, detail, actual, limit))

    if new:
        print("\n  The shape: a short header saying what the FILE does, then a statement on")
        print("  each declaration saying what THAT declaration does. Long-form reasoning")
        print("  belongs in .claude-local/notes/ with a pointer. The Take is exempt.")
        print("  Prose is the unchecked half of the file; code is kernel-checked.")
        if block_mode:
            print("\nPush blocked: new prose exceeds the cap.")
            return 1
    return 0


def selftest():
    """Detector verification: a must-fire control AND a must-suppress control."""
    import tempfile
    ok = True
    tmp = tempfile.mkdtemp()

    fire = os.path.join(tmp, "Fire.lean")
    io.open(fire, "w", encoding="utf-8", newline="\n").write(
        "/-- " + "\n".join("    padding line %d" % i for i in range(30)) + "\n-/\n"
        "theorem t : True := trivial\n"
        "/-!\n" + "\n".join("block line %d" % i for i in range(30)) + "\n-/\n"
    )
    v = scan_file(fire, "Fire.lean")
    kinds = set(k for k, *_ in v)
    if "doc" not in kinds:
        print("  SELFTEST FAIL: oversized docstring not detected"); ok = False
    if "block" not in kinds:
        print("  SELFTEST FAIL: oversized module-doc block not detected"); ok = False

    # MUST-SUPPRESS: the undocumented-declaration rule was RETIRED 2026-08-08 (119 sites removed by
    # amending a rule rather than by writing prose; the CI run summary already publishes every
    # declaration's footprint and signature, so a docstring restating a signature is a second copy
    # that can drift while the artifact cannot). This control was a MUST-FIRE for that rule and kept
    # failing after the retirement — a stale control that nobody ran, which is worse than no control
    # because a red selftest trains you to ignore the output. Inverted: bare declarations must now
    # produce NOTHING.
    undoc = os.path.join(tmp, "Undoc.lean")
    io.open(undoc, "w", encoding="utf-8", newline="\n").write(
        "theorem bare : True := trivial\n"
        "def alsoBare : Nat := 0\n"
    )
    v3 = scan_file(undoc, "Undoc.lean")
    stray = sorted(k for kind, k, *_ in v3)
    if stray:
        print("  SELFTEST FAIL: bare declarations flagged after the rule was retired (%s)" % stray)
        ok = False

    # must-suppress: documented, attribute-separated, private, and example
    exempt = os.path.join(tmp, "Exempt.lean")
    io.open(exempt, "w", encoding="utf-8", newline="\n").write(
        "/-- documented. -/\n"
        "theorem a : True := trivial\n"
        "/-- documented, attribute between doc and decl. -/\n"
        "@[simp]\n"
        "theorem b : True := trivial\n"
        "private theorem c : True := trivial\n"
        "example : True := trivial\n"
    )
    v4 = [x for x in scan_file(exempt, "Exempt.lean") if x[0] == "undoc"]
    if v4:
        print("  SELFTEST FAIL: undoc fired on exempt declarations: %s" % [x[1] for x in v4])
        ok = False

    # must-fire: a bare #check, and a glossed-but-unlabelled #check
    idx = os.path.join(tmp, "Index.lean")
    io.open(idx, "w", encoding="utf-8", newline="\n").write(
        "#check @Foo.bare_one\n"
        "#check @Foo.unlabelled_one  -- proves the thing about the other thing\n"
    )
    v5 = scan_file(idx, "Index.lean")
    k5 = set(k for k, *_ in v5)
    if "bare" not in k5:
        print("  SELFTEST FAIL: bare #check not detected"); ok = False
    if "unlabelled" not in k5:
        print("  SELFTEST FAIL: unlabelled #check gloss not detected"); ok = False

    # must-suppress: both label forms, same-line and line-above, plain and bolded
    idx2 = os.path.join(tmp, "Index2.lean")
    io.open(idx2, "w", encoding="utf-8", newline="\n").write(
        "#check @Foo.a  -- Statement: the map has no fixed point.\n"
        "#check @Foo.b  -- Reading: the framework reads this as the wall face.\n"
        "-- **Statement:** bolded label on the line above.\n"
        "#check @Foo.c\n"
    )
    v6 = scan_file(idx2, "Index2.lean")
    if v6:
        print("  SELFTEST FAIL: fired on correctly labelled #checks: %s" % [x[1] for x in v6])
        ok = False

    # must-suppress: a MULTI-LINE gloss whose label sits on the first line, not the adjacent one
    idx3 = os.path.join(tmp, "Index3.lean")
    io.open(idx3, "w", encoding="utf-8", newline="\n").write(
        "-- Statement: the map has no fixed point.\n"
        "-- Reading: and here is a second line that carries no label of its own.\n"
        "#check @Foo.multi\n"
        "-- Statement: a label on the first line only,\n"
        "-- with a plain continuation beneath it.\n"
        "#check @Foo.cont\n"
    )
    v8 = scan_file(idx3, "Index3.lean")
    if v8:
        print("  SELFTEST FAIL: fired on multi-line labelled glosses: %s" % [x[1] for x in v8])
        ok = False

    supp = os.path.join(tmp, "Suppress.lean")
    io.open(supp, "w", encoding="utf-8", newline="\n").write(
        "/-! ## Engineer's Take\n" + "\n".join("take line %d" % i for i in range(60)) + "\n-/\n"
        "/-- one line doc. -/\n"
        "theorem t : True := by\n  trivial\n  -- filler\n"
        "/-! short block\nsecond line\n-/\n"
    )
    # `takeopen` is filtered: this control tests that no VIOLATION fires on a pure Take.
    # A Take with nothing after it is still an unmeasured remainder and is reported as a
    # measurement gap (PRS-1) - that report is correct here, and is not a violation.
    v2 = [x for x in scan_file(supp, "Suppress.lean") if x[0] != "takeopen"]
    if v2:
        print("  SELFTEST FAIL: fired on exempt/compliant content: %s" % [x[1] for x in v2])
        ok = False

    # must-fire (PRS-1): an essay AFTER the Take, behind a `---`, must be measured. The
    # pre-existing control below puts the essay BEFORE the Take, which is why the latch
    # survived - the probe was in the wrong shape. Both shapes are now covered.
    after = os.path.join(tmp, "AfterTake.lean")
    io.open(after, "w", encoding="utf-8", newline="\n").write(
        "/-!\n# Title\n\n## Engineer's Take\n" + "\n".join("take %d" % i for i in range(4))
        + "\n\n---\n\n" + "\n".join("essay line %d" % i for i in range(30)) + "\n-/\n"
    )
    if not [x for x in scan_file(after, "AfterTake.lean") if x[0] == "block"]:
        print("  SELFTEST FAIL: essay after the Take behind `---` was not measured"); ok = False

    # must-report (PRS-1): with NO delimiter the two are indistinguishable, so the gap is
    # REPORTED rather than judged. Deliberately not a violation - the Take is Tim's voice.
    bare = os.path.join(tmp, "BareTake.lean")
    io.open(bare, "w", encoding="utf-8", newline="\n").write(
        "/-!\n# Title\n\n## Engineer's Take\n" + "\n".join("take %d" % i for i in range(4))
        + "\n\n" + "\n".join("essay line %d" % i for i in range(30)) + "\n-/\n"
    )
    if not [x for x in scan_file(bare, "BareTake.lean") if x[0] == "takeopen"]:
        print("  SELFTEST FAIL: unclosed Take was not reported as a measurement gap"); ok = False

    # must-fire: an essay hiding in the same block as the Take must NOT be exempted wholesale
    hide = os.path.join(tmp, "Hide.lean")
    io.open(hide, "w", encoding="utf-8", newline="\n").write(
        "/-!\n# Title\n" + "\n".join("essay line %d" % i for i in range(30)) +
        "\n## Engineer's Take\n" + "\n".join("take line %d" % i for i in range(40)) + "\n-/\n"
    )
    v7 = [x for x in scan_file(hide, "Hide.lean") if x[0] == "block"]
    if not v7:
        print("  SELFTEST FAIL: essay hiding beside the Take was exempted wholesale"); ok = False

    print("  selftest: %s" % ("PASS (fires on both, suppresses both)" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(run(block_mode="--block" in sys.argv,
                 write_baseline="--baseline" in sys.argv))
