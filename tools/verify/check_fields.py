"""Fail when rendered prose says a typeclass FIELD is proved that the Lean SUPPLIES.

WHY A CHECKER AND NOT A FIFTH CAREFUL PASS. Four consecutive gate rounds corrected this same
claim family and each fix was incomplete; each time the response was a wider grep. The fourth
miss is the one that settles the argument: `build_zpj_afa_addendum.py:141` renders *"the fields
of the target typeclass are proved as theorems from the source"* — the same false claim as the
two surfaces already fixed, in a sentence containing **no numeral at all**. Every pattern the
round-4 sweep used required the token `three`. A wider pattern would have missed it a fifth time.

⭐ THE PROPERTY IS STRUCTURAL, NOT LEXICAL, AND THAT IS THE WHOLE POINT. `CLAUDE.md` R-RECUR:
*1st an instance, 2nd a class with a detector, 3rd the trigger is wrong, 4th+ BUILD THE CHECKER.*
A grep only finds what you already suspect, so a checker made of better phrases rebuilds the same
blind spot in Python. What this asks instead is a fact about the LEAN:

    for each `instance I : C ... where`, each `field := binding`
      binding resolves to `theorem`/`lemma`  ->  PROVED   (a law, discharged)
      binding resolves to `def`/`abbrev`     ->  SUPPLIED (data, handed over)

A Lean typeclass field is one of two things. A LAW is a proposition you discharge with a proof.
DATA is a value you hand over — `selfMem : L → Prop` is a *predicate you choose*, not a
proposition you prove, and `toAFAStructure` supplies it with `def selfMemDerived`. A `def` is an
assignment. Saying it "becomes a theorem" describes data as a proof, which is the defect.

    python tools/verify/check_fields.py            # WARN  (advisory, exit 0)
    python tools/verify/check_fields.py --block    # BLOCK (exit 1 on any NEW site)
    python tools/verify/check_fields.py --truth    # print the Lean ground truth and stop

⚠ THE PROSE LEG IS A READING LIST, NEVER THE VERDICT (`R-NOCONV` rung 5). The ENUMERATION —
which blocks mention a class — is a text scan and can be wrong. The JUDGEMENT it is measured
against is computed from the Lean and cannot. A flagged block is *"this block claims proof about
a class that has data fields"*, which a human confirms; it is not *"this sentence is false"*.

⚠ BLOCK-SCOPED, NOT LINE-SCOPED, AND THAT IS WHAT CATCHES THE FOURTH SURFACE. The offending
sentence names no class; the paragraph it sits in names `AFAStructure` three lines up. Anchoring
on the line would reproduce the miss exactly.

⚠ IT CANNOT SEE INTO A PDF. It reads the GENERATORS. A claim rendered from a source this does not
scan is invisible to it, which is why the prose gates still measure the rendered bytes.
"""

import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

REPO = common.REPO
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fields_baseline.txt")

# A claim that a FIELD is proved. Deliberately generous — this leg only nominates, and a false
# nomination costs a read while a missed one costs a gate round.
_CLAIM = re.compile(
    r"(?:field|fields)[^.]{0,120}?(?:are|become|becomes|is|as)\s+(?:derived\s+)?"
    r"(?:theorems?|proved|proven|derived)"
    r"|(?:theorems?|proved|proven)[^.]{0,60}?\bfields?\b",
    re.I)
_DECL = re.compile(r"^\s*(theorem|lemma|def|abbrev|instance|noncomputable\s+def)\s+([A-Za-z_][\w'.]*)",
                   re.M)
_INST = re.compile(r"^instance\s+([A-Za-z_][\w'.]*)\s*:\s*([A-Za-z_][\w'.]*)[^\n]*\bwhere\b\s*$",
                   re.M)
_BIND = re.compile(r"^\s+([A-Za-z_][\w'?!]*)\s*:=\s*(.+?)\s*$")


def _lean_files(root=None):
    out = []
    base = os.path.join(root or REPO, "ZeroParadox")
    if not os.path.isdir(base):
        base = root or REPO
    for r, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d not in (".lake", "Vendored")]
        out += [os.path.join(r, f) for f in files if f.endswith(".lean")]
    return sorted(out)


def declarations(root=None):
    """`{name: kind}` for every declaration in the corpus — the resolver's dictionary."""
    kinds = {}
    for p in _lean_files(root):
        try:
            src = io.open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for kind, name in _DECL.findall(src):
            kinds.setdefault(name.strip(), kind.split()[-1])
    return kinds


def ground_truth(root=None):
    """`{Class: {"proved": [...], "supplied": [...], "inline": [...], "where": path}}`.

    ⚠ `inline` is its own bucket and is NOT counted as either. A field bound to a `by` block or an
    anonymous term is neither a named theorem nor a named def, and guessing which would be the
    proxy defect this checker exists to avoid — asserting a stand-in for the property instead of
    the property."""
    kinds = declarations(root)
    truth = {}
    for p in _lean_files(root):
        try:
            lines = io.open(p, encoding="utf-8", errors="replace").read().split("\n")
        except OSError:
            continue
        src = "\n".join(lines)
        for m in _INST.finditer(src):
            cls = m.group(2)
            start = src[:m.start()].count("\n") + 1
            rec = truth.setdefault(cls, {"proved": [], "supplied": [], "inline": [],
                                         "where": os.path.relpath(p, root or REPO).replace("\\", "/")})
            for ln in lines[start:]:
                if ln.strip() and not ln.startswith((" ", "\t")):
                    break
                b = _BIND.match(ln)
                if not b:
                    continue
                field, binding = b.group(1), b.group(2).strip()
                head = re.match(r"[A-Za-z_][\w'.]*", binding)
                kind = kinds.get(head.group(0)) if head else None
                if kind in ("theorem", "lemma"):
                    bucket = "proved"
                elif kind in ("def", "abbrev"):
                    bucket = "supplied"
                else:
                    bucket = "inline"
                if field not in rec[bucket]:
                    rec[bucket].append(field)
    return truth


def _prose_files():
    out = []
    sdir = os.path.join(REPO, "scripts")
    if os.path.isdir(sdir):
        out += [os.path.join(sdir, f) for f in sorted(os.listdir(sdir)) if f.endswith(".py")]
    out += [os.path.join(REPO, f) for f in sorted(os.listdir(REPO)) if f.endswith(".md")]
    return out


def _blocks(src):
    """(start_line, text) per blank-line-separated block — the unit a claim actually lives in."""
    out, buf, start = [], [], 1
    for i, ln in enumerate(src.split("\n"), 1):
        if ln.strip():
            if not buf:
                start = i
            buf.append(ln)
        elif buf:
            out.append((start, "\n".join(buf)))
            buf = []
    if buf:
        out.append((start, "\n".join(buf)))
    return out


_CHANGELOG = re.compile(r"^v\d+\.\d+[:.]", re.M)


def _is_dated_record(block):
    """True for a build script's module changelog — a DATED RECORD, exempt on the same grounds
    `check_moved` exempts `.claude-local/notes/` and register.md's Notes column.

    ⚠ NOT A CONVENIENCE EXEMPTION. A changelog entry records the document AS IT STOOD at a
    version — including, in several of these files, the very sentence a later version retracted.
    Rewriting it to match today's prose would falsify the record of the correction, and the
    correction is the thing worth keeping. Two or more entries, so a single stray version string
    in live prose is NOT exempted."""
    return len(_CHANGELOG.findall(block)) >= 2


def scan(truth):
    """Blocks that claim proof about a class the Lean shows has SUPPLIED fields."""
    risky = {c: r for c, r in truth.items() if r["supplied"]}
    hits, exempted = [], 0
    for p in _prose_files():
        rel = os.path.relpath(p, REPO).replace("\\", "/")
        try:
            src = io.open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for start, block in _blocks(src):
            if not _CLAIM.search(block):
                continue
            if _is_dated_record(block):
                exempted += 1
                continue
            for cls, rec in risky.items():
                if re.search(r"\b%s\b" % re.escape(cls), block):
                    hits.append((rel, start, cls, rec, block.strip()[:150]))
                    break
    return hits, exempted


_FIXTURE = '''
class Demo (L : Type*) where
  pick : L → Prop
  law_one : pick bot
  law_two : ∀ x, pick x → x = bot

def pickDerived (x : L) : Prop := x = bot

theorem derived_law_one : pickDerived bot := rfl

theorem derived_law_two : ∀ x, pickDerived x → x = bot := fun _ h => h

instance toDemo : Demo L where
  pick    := pickDerived
  law_one := derived_law_one
  law_two := derived_law_two
'''


def selftest():
    """Both halves, each expectation declared BEFORE the run (`DC-22`).

    ⚠ THE MUST-SUPPRESS HALF IS THE ONE THAT MATTERS MOST HERE. This checker nominates prose for
    a human to read, so a false positive spends attention on a true sentence — and a screen that
    cries wolf is one people learn to skip, which costs more than the defect it was built for.

    ⚠ THE GROUND-TRUTH HALF IS THE POINT OF THE WHOLE FILE. If `pick := pickDerived` is not
    classified SUPPLIED, every prose verdict downstream is measured against a wrong fact, and the
    checker becomes a slower grep with extra confidence."""
    import shutil
    import tempfile
    root = tempfile.mkdtemp(prefix="zp_fields_ctl_")
    fails = []
    try:
        d = os.path.join(root, "ZeroParadox")
        os.makedirs(d)
        io.open(os.path.join(d, "Demo.lean"), "w", encoding="utf-8").write(_FIXTURE)
        truth = ground_truth(root)

        # --- GROUND TRUTH: a def-bound field is DATA, a theorem-bound field is a LAW ------
        rec = truth.get("Demo")
        cases = [
            ("Demo is found at all", rec is not None),
            ("pick classified SUPPLIED (bound to a def)", bool(rec) and "pick" in rec["supplied"]),
            ("law_one classified PROVED (bound to a theorem)", bool(rec) and "law_one" in rec["proved"]),
            ("law_two classified PROVED", bool(rec) and "law_two" in rec["proved"]),
            ("pick NOT counted as proved", bool(rec) and "pick" not in rec["proved"]),
        ]
        # --- PROSE: must-fire and must-suppress, same class, same file ------------------
        prose = [
            ("MUST FIRE  claim + class, no numeral",
             "The Demo typeclass is central.\nAt each step the fields of the target\n"
             "typeclass are proved as theorems from the source.", True),
            ("MUST FIRE  claim + class, with numeral",
             "Demo has three fields.\nAll three fields are theorems.", True),
            ("MUST SUPPRESS  class named, no proof claim",
             "Demo abstracts the fixed-point pattern and is used downstream.", False),
            ("MUST SUPPRESS  proof claim, no risky class named",
             "At each step the fields of the target typeclass are proved as theorems.", False),
            ("MUST SUPPRESS  dated changelog naming Demo",
             "v1.2: Demo fields are theorems.\nv1.1: earlier note.\nv1.0: initial.", False),
        ]
        # ⚠⚠ THESE CALL `scan()`. THEY USED TO RE-IMPLEMENT ITS DECISION INLINE — recomputing
        # `_CLAIM.search`, `_is_dated_record` and the class-name test right here — which meant the
        # suite printed `10 of 10` over a `scan()` replaced with `return [], 0`. Measured by /rely
        # 2026-08-26 (RLY35-2). A control that re-derives the logic it is testing is asserting
        # about a COPY, and the copy passes while the original is gutted; that is the exact defect
        # class this checker was built to catch, arriving inside its own controls.
        #
        # The prose fixtures are written into the temp root and scanned through the real function,
        # so deleting or neutering `scan` now turns these red.
        pdir = os.path.join(root, "scripts")
        os.makedirs(pdir, exist_ok=True)
        for i, (label, block, want) in enumerate(prose):
            io.open(os.path.join(pdir, "build_ctl%d.py" % i), "w", encoding="utf-8").write(block)
        _real_repo = globals()["REPO"]
        try:
            globals()["REPO"] = root
            hits, _ = scan(truth)
        finally:
            globals()["REPO"] = _real_repo
        flagged = {os.path.basename(h[0]) for h in hits}
        for i, (label, block, want) in enumerate(prose):
            got = ("build_ctl%d.py" % i) in flagged
            cases.append((label, got == want))

        print("=== check_fields controls — MUST-FIRE and MUST-SUPPRESS ===")
        for label, ok in cases:
            print("  %-4s %s" % ("PASS" if ok else "FAIL", label))
            if not ok:
                fails.append(label)
    finally:
        shutil.rmtree(root, ignore_errors=True)
    print("  %d of %d control(s) behaved as required" % (len(cases) - len(fails), len(cases)))
    return 1 if fails else 0


def main(argv):
    if "--selftest" in argv:
        return selftest()
    truth = ground_truth()
    if "--truth" in argv:
        print("=== LEAN GROUND TRUTH — how each instance discharges its class's fields ===")
        for cls in sorted(truth):
            r = truth[cls]
            print("  %-24s proved=%-2d supplied=%-2d inline=%-2d  (%s)"
                  % (cls, len(r["proved"]), len(r["supplied"]), len(r["inline"]), r["where"]))
            if r["supplied"]:
                print("      SUPPLIED (data, not proved): %s" % ", ".join(r["supplied"]))
        return 0

    hits, exempted = scan(truth)
    known = common.load_baseline(BASELINE) if hasattr(common, "load_baseline") else set()
    if not known and os.path.exists(BASELINE):
        known = {l.strip() for l in io.open(BASELINE, encoding="utf-8")
                 if l.strip() and not l.startswith("#")}
    new = [h for h in hits if "%s:%s" % (h[0], h[1]) not in known]

    print("=" * 60)
    print("  typeclass FIELD-DISCIPLINE check")
    print("  classes with SUPPLIED (data) fields : %d"
          % len([c for c, r in truth.items() if r["supplied"]]))
    print("  blocks claiming proof about them    : %d" % len(hits))
    # ⚠ PRINTED EVERY RUN, INCLUDING AT ZERO. An exemption nobody counts manufactures coverage
    # that was never earned; a rising number is the only way a growing carve stays visible.
    print("  dated changelog blocks exempted     : %d" % exempted)
    print("  grandfathered (baseline)            : %d" % (len(hits) - len(new)))
    print("  NEW sites                           : %d" % len(new))
    print("=" * 60)
    for rel, start, cls, rec, snip in new:
        print("  %s:%s" % (rel, start))
        print("      class %s — the Lean SUPPLIES %s with a def; it is DATA, not a theorem"
              % (cls, ", ".join(rec["supplied"])))
        print("      proved=%d supplied=%d   (%s)"
              % (len(rec["proved"]), len(rec["supplied"]), rec["where"]))
        print("      %s" % snip.replace("\n", " ")[:140])
    if new:
        print("\n  ⚠ READING LIST, NOT A FINDING LIST. Each block CLAIMS proof about a class that")
        print("    has data fields. Confirm at the source before counting it a defect — the")
        print("    enumeration is a text scan; only the proved/supplied split is computed.")
    rc = common.record_if_asked(
        "check_fields",
        sorted({h[0] for h in hits}) or [f for f in ["README.md"]],
        sorted({h[0] for h in new}),
        "rendered prose claims a typeclass field is proved that the Lean supplies with a def",
        switches=[os.path.relpath(BASELINE, REPO).replace("\\", "/")])
    if rc:
        return rc
    return 1 if (new and "--block" in argv) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
