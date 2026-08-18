"""An ATTRIBUTION claim with no locator is unverifiable, and one of them reached a deposited PDF.

    check_attribution.py            # report
    check_attribution.py --block    # exit 1 on any NEW unbaselined site
    check_attribution.py --selftest # controls

WHY THIS EXISTS, measured 2026-08-17.  The corpus said *"Lawvere (1969) derives the recursion
theorem."*  Read at source, his section 2 p. 9 RAISES the recursive case as an open question --
*"Experts on recursive functions ... may also wish to consider whether the fixed-point theorem of
section one has any applications in those cases."*  The derivation is Yanofsky (2003) Theorem 5,
printed p. 18.  So the sentence credited an author with a result his own paper asks someone else to
attempt, and it rendered into a DOI-bearing PDF.

WHY THE EXISTING GATES MISSED IT, which is the whole design argument.  The prior-art gate's detector
was a LOCATOR DIFF: extract every `p. N` / `Thm N` token and check each against its source.  The
offending sentence had an author, a year, a verb -- and NO locator at all.  A locator diff has
nothing to compare when there is no page number, so the blindness is structural rather than an
oversight.  That gate said so itself and recommended this complementary pass.

WHAT IT FLAGS.  An AUTHOR + VERB claim -- `Lawvere derives`, `Rutten proves`, `Aczel shows` -- with
no locator anywhere near it.  That is precisely the shape whose truth cannot be checked without
guessing which page to open.

WHAT IT DELIBERATELY DOES NOT DO.  It does not verify attributions.  Only a reader with the source
can do that, and this checker never opens one.  A clean run means every attribution says WHERE to
look, never that it looks right.  Do not read exit 0 as "the citations are correct".

Baseline: `attribution_baseline.txt`, beside this file.  Blocks on NEW sites only; a baseline is
DEBT, not a decision.  Add entries BY HAND with a per-site reason.
"""
import io
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SELF = os.path.relpath(str(Path(__file__).resolve()), str(HERE.parent.parent))
sys.path.insert(0, str(HERE))
import common  # noqa: E402

BASELINE = HERE / 'attribution_baseline.txt'

# The checker's own source and its own baseline: every phrase below is quoted in this docstring, so
# scanning them reports the tool describing itself. Same exemption `check_modal` takes.
SKIP_NAMES = {'check_attribution.py', 'attribution_baseline.txt'}

# A surname (or `Author & Author`, `Author-Author`) followed by an optional year, then a verb of
# ATTRIBUTION. Deliberately not every reporting verb: `notes`, `writes` and `says` attach to
# quotations, which carry their own evidence.
ATTRIB = re.compile(
    r"\b([A-Z][A-Za-zÀ-ɏ'’-]{2,}"
    r"(?:\s*(?:&|and|–|-)\s*[A-Z][A-Za-zÀ-ɏ'’-]{2,}){0,2})"
    r"(?:\s*\((?:19|20)\d\d[a-z]?\))?\s+"
    r"(derives?|proves?|shows?|establishes?|introduces?|gives?|demonstrates?)\b")

# Anything that tells a reader WHERE to look. `arXiv:` counts: it identifies one document.
LOCATOR = re.compile(
    r"(?:pp?\.\s*\d|§\s*\d|\bsection\s+\d|\bch(?:apter|\.)\s*\d"
    r"|\b(?:thm|theorem|def(?:inition)?|lem(?:ma)?|cor(?:ollary)?|prop(?:osition)?|remark|example|"
    r"exercise|axiom|fig(?:ure)?)\.?\s*\d"
    r"|\barxiv:\s*\d|\bdoi:|\bp\.\s*\d)", re.I)

# Verbs that report SPEECH rather than a result, where a quotation carries the evidence itself.
QUOTED = re.compile(r"[“”\"‘’]|\*\"")

# ⚠ A CAPITALISED WORD BEFORE A VERB IS NOT AN AUTHOR, AND THE FIRST DRAFT BELIEVED IT WAS.
# Measured on the live corpus: 90 hits, of which roughly 4 were genuine attributions. The rest were
# `Lean derives` (13), `This proves`, `Mathlib gives`, `NOT show`, and framework labels like `ZP-H`
# and `T-COMP`. A false positive is the more expensive error here - it manufactures work that looks
# urgent - so the subject must survive three filters before it counts as a person.
NOT_AN_AUTHOR = {
    'this', 'that', 'it', 'these', 'those', 'we', 'one', 'here', 'there', 'both', 'each', 'all',
    'what', 'which', 'the', 'its', 'his', 'her', 'their', 'nothing', 'something', 'every', 'no',
    'not', 'lean', 'mathlib', 'coq', 'rocq', 'paradox', 'zero', 'python', 'none', 'neither',
    'either', 'nowhere', 'anything', 'everything', 'someone', 'together', 'first', 'second',
    # framework objects that read as surnames to a structural test
    'dom', 'snap', 'code', 'end', 'phase', 'wall', 'floor', 'bottom',
}
# A Lean identifier in CamelCase - `AbstractSelfApp`, `ValuationStructure`. An internal capital is
# the tell; surnames do not carry one (`Escardo`, `Carlstrom`, `Lawvere` all pass).
CAMEL = re.compile(r"^[A-Z][a-z]+(?:[A-Z][a-z]*)+$")
ACRONYM = re.compile(r"^[A-Z][A-Z0-9]*(?:[-_][A-Z0-9]+)*$")   # ZP-H, T-COMP, APG, NOT
FRAMEWORK_LABEL = re.compile(r"^(?:ZP|ZPJ|ZPX|T-|D-|L-|CC-|DP-|AX-|MC-|OQ-)", re.I)


def _is_author(name):
    """Three filters, because a surname is the ONLY thing this checker should treat as attributable.

    A person's name here is: not a stopword, not an acronym or framework label, and carries a
    lowercase letter after the first character. `Escardó` and `Carlström` pass; `Lean`, `ZP-H`,
    `T-COMP` and `This` do not.
    """
    head = name.split()[0]
    if head.lower() in NOT_AN_AUTHOR:
        return False
    if ACRONYM.match(head) or FRAMEWORK_LABEL.match(head) or CAMEL.match(head):
        return False
    return bool(re.search(r"[a-zà-ɏ]", head[1:]))


WINDOW = 160          # characters either side in which a locator discharges the claim
SKIP_LINE = re.compile(r"^\s*(?:#|--|//)?\s*(?:import|open|set_option)\b")


def _soften(text):
    """Blank comment prefixes to EQUAL LENGTH so a wrapped claim reads as one line and offsets hold.

    The same fix `check_modal` needed: a claim wrapped across two Lean docstring lines is invisible
    to a flat pattern, and Lean docstrings wrap constantly. Replacing the separator with spaces of
    the same width keeps every reported column honest.
    """
    return re.sub(r"(?m)^(\s*)(--|//|#)", lambda m: m.group(1) + ' ' * len(m.group(2)), text)


def scan_text(t):
    """Yield (line_no, author, verb) for attribution claims carrying no locator."""
    soft = _soften(t)
    flat = soft.replace('\n', ' ')
    starts = [0]
    for ch in soft:
        starts.append(starts[-1] + 1)
    out = []
    # map flat offsets back to line numbers
    line_of = []
    ln = 1
    for ch in soft:
        line_of.append(ln)
        if ch == '\n':
            ln += 1
    for m in ATTRIB.finditer(flat):
        i, j = m.start(), m.end()
        lo, hi = max(0, i - WINDOW), min(len(flat), j + WINDOW)
        near = flat[lo:hi]
        if LOCATOR.search(near) or QUOTED.search(near):
            continue
        line = line_of[i] if i < len(line_of) else 0
        raw = t.split('\n')[line - 1] if 0 < line <= len(t.split('\n')) else ''
        if SKIP_LINE.match(raw):
            continue
        if not _is_author(m.group(1)):
            continue
        out.append((line, m.group(1), m.group(2)))
    return out


def scan():
    hits = []
    for path, rel in common.targets(skip_names=SKIP_NAMES):
        try:
            t = path.read_text(encoding='utf-8', errors='replace')
        except OSError:
            continue
        for line, author, verb in scan_text(t):
            hits.append((rel, line, author, verb))
    return hits


def selftest():
    """⚠ Controls in the shapes the CORPUS uses, including the one that actually shipped."""
    must_fire = [
        ("the shape that reached a deposited PDF",
         "That Kleene's recursion theorem is standard: Lawvere (1969) derives the recursion theorem."),
        ("no year", "The engine is Lawvere, and Yanofsky proves the unified form."),
        ("wrapped across a Lean docstring", "/-- the framing is due to\n    Rutten proves the final\n    system. -/"),
        ("two authors", "Adamek & Milius establishes the coalgebraic form."),
    ]
    must_suppress = [
        ("a page locator discharges it",
         "Lawvere (1969) derives the recursion theorem -- see p. 9 for the open question."),
        ("a theorem locator discharges it",
         "Yanofsky (2003) proves it, Theorem 5, in the unified treatment."),
        ("a section locator discharges it",
         "Aczel shows this at § 2 of the manuscript."),
        ("an arXiv id discharges it",
         "Adamek-Milius-Moss establishes it, arXiv:1910.09401v2."),
        ("a quotation carries its own evidence",
         "Rutten shows the point: “only takes a step to itself”, which settles it."),
        ("a lowercase subject is not an author", "the functor derives the recursion theorem"),
        ("a demonstrative is not an author", "This proves the fork collapses."),
        ("a tool is not an author", "Lean derives the instance automatically."),
        ("a framework label is not an author", "ZP-H establishes the categorical bridge."),
        ("an acronym is not an author", "T-COMP proves the three characterisations equal."),
        ("a CamelCase identifier is not an author", "AbstractSelfApp gives the fixed point."),
        ("a framework object is not an author", "Snap shows the transition is irreversible."),
    ]
    bad = 0
    print('== attribution claims - CONTROLS ==')
    for label, group, want in (('MUST FIRE', must_fire, True),
                               ('MUST SUPPRESS', must_suppress, False)):
        print(label)
        for why, text in group:
            got = bool(scan_text(text))
            ok = (got == want)
            bad += 0 if ok else 1
            print('  %-52s %s' % (why[:52], 'ok' if ok else ('MISSED' if want else 'FALSE POSITIVE')))
    bad += common.check_vocabulary('check_attribution', globals())
    print('\nselftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return bad


def main():
    args = sys.argv[1:]
    if '--selftest' in args:
        return selftest()

    hits = scan()
    if '--baseline' in args:
        keys = sorted({'%s:%s:%s' % (r, a, v) for r, _l, a, v in hits})
        common.write_text_lf(str(BASELINE),
                             '# check_attribution baseline - ADD BY HAND, one reason per line.\n'
                             + '\n'.join(keys) + '\n')
        print('baseline written: %d key(s)' % len(keys))
        return 0

    base = common.load_baseline(BASELINE)
    new = [h for h in hits if '%s:%s:%s' % (h[0], h[2], h[3]) not in base]
    print('\n== attribution claims without a locator ==')
    print('  total sites            : %d' % len(hits))
    print('  grandfathered          : %d' % (len(hits) - len(new)))
    print('  NEW (unbaselined)      : %d' % len(new))
    for rel, line, author, verb in sorted(new)[:40]:
        print('    %s:%d  "%s %s" - no locator within %d chars' % (rel, line, author, verb, WINDOW))
    if len(new) > 40:
        print('    ... and %d more' % (len(new) - 40))
    print('\n  ⚠ THIS DOES NOT VERIFY ATTRIBUTIONS. A clean run means every claim says WHERE to')
    print('    look, never that it looks right. Only a reader with the source settles that.')
    if '--block' in args and new:
        print('\nBLOCKED: %d attribution claim(s) carry no locator.' % len(new))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
