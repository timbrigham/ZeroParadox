"""Encoding integrity for every tracked text file: decodable, no BOM, not double-encoded.

⚠ **"IS IT UTF-8?" IS THE WRONG QUESTION, AND ASKING ONLY THAT RETURNS A CONFIDENT PASS ON THE
DEFECT THIS CHECKER EXISTS FOR.** Measured 2026-08-20: a PowerShell 5.1 script wrote `CLAUDE.md`
with a six-character run beginning `Ã` where `📖 —` belonged. That file was **valid UTF-8 at every
byte** — the bytes are
a legal encoding of the wrong characters. `open(p, encoding='utf-8')` succeeds, a decodability test
passes, and the damage commits looking fine in a diff.

So there are THREE tests here and only the third fires on that:

  1. DECODES        — raw cp1252/latin-1 bytes written straight into a file. Cheap, exact.
  2. NO BOM         — `.gitattributes` normalises line endings and says nothing about a BOM; a
                      UTF-8 BOM shows up as a spurious whole-file diff and breaks any reader that
                      parses the first line (a shebang, a `#` heading, a front-matter fence).
  3. NOT DOUBLE-ENCODED — text decoded as cp1252 and re-encoded as UTF-8. The one that bites.

**THE DISCRIMINATOR FOR (3) IS A ROUND TRIP, NOT A PATTERN LIST.** A list of known-bad bigrams is an
enumeration, so it is unbounded and each fix closes only the holes its author thought of — CLAUDE.md
§ RUNG 5 names that shape exactly. Instead: take each maximal run of adjacent non-ASCII characters
and ask whether it can be read back as cp1252 bytes forming valid UTF-8. Double-encoded text
round-trips **by construction**, because that is literally how it was produced. Legitimate text does
not:

    a mangled em dash  -> cp1252 E2 80 94 -> valid UTF-8 '—'       FIRES  (it IS mojibake)
    'ü'                -> cp1252 FC       -> not valid UTF-8 alone silent (a real German umlaut)
    'Adámek'           -> cp1252 E1       -> not valid UTF-8 alone silent (a real citation)
    '⊥ ∞ ℤ₂'           -> not encodable in cp1252 at all           silent (the corpus's own glyphs)

⚠ **THIS FILE CONTAINS NO LITERAL MOJIBAKE, AND THAT IS A CONSTRAINT RATHER THAN A STYLE CHOICE.**
Its first version wrote the corrupted fixtures out by hand and the checker flagged **its own
source** — a detector whose test data are instances of what it detects can never report clean. The
exemption fix (skip this file) would have punched a hole in the one property it exists to hold.
Instead `_mangle()` derives each fixture from the CORRECT text at runtime, so the source stays ASCII
and the fixture stays byte-exact. Same reason the worked examples above are described rather than
shown. **If you add a fixture, add it as the intended string and let `_mangle` corrupt it.**

The run must be **two or more** characters and its first must land in the C2–F4 lead-byte range,
which is precisely the mojibake signature space. That is why this is not a heuristic with a
tolerance to tune.

⚠ **WHY A CHECKER AND NOT A RULE.** `selfheal.py` counts this shape as `SH-2` with nine ledger rows
and **no class row**, i.e. four rungs up CLAUDE.md's escalation ladder, where the file's own verdict
is *"discipline will not work here; build the mechanical check and stop writing prose about it."*
The proximate cause is not carelessness: PowerShell 5.1 parses a `.ps1` as the system ANSI codepage
unless the script itself carries a BOM, so a correct script writing correct text still corrupts it,
and the author sees the right characters in their editor. Nothing a human can reliably remember
defends against that. Argument and the safe write recipes: `tools/process/file-encoding.md`.

Usage — the tool NEVER writes its own invocation path down; `SELF` is derived:

    python tools/verify/check_encoding.py                 # scan every tracked text file
    python tools/verify/check_encoding.py <path> [...]    # pass/fail specific files, after writing
    python tools/verify/check_encoding.py --block         # non-zero exit on any violation
    python tools/verify/check_encoding.py --selftest      # controls, both directions
"""
import io
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

common.utf8_stdout()

SELF = common.self_rel(__file__)
REPO = common.REPO

BOM = b'\xef\xbb\xbf'

# Not text: there is no character content for any of these three tests to be about. Extension-keyed
# and deliberately short — anything not named here is treated as text, so a new text extension is
# covered by default and a new BINARY one fails loud as an undecodable file rather than silently
# skipping. Default-scan, explicit-exclude, the same polarity as `batch.EXEMPT_PATHS`.
BINARY_EXT = ('.pdf', '.png', '.jpg', '.jpeg', '.gif', '.ico', '.svgz',
              '.ttf', '.otf', '.woff', '.woff2', '.zip', '.gz', '.olean')


def tracked_text_files():
    """Every TRACKED file minus known binaries. `git ls-files`, never a glob.

    ⚠ Tracked-only is load-bearing twice over: the gitignored private folder stays out **by
    construction** rather than by remembering a skip list, and a scratch file in the working tree
    cannot fail a commit it is not part of. Same argument as `common.tracked_md`.

    ⚠ And this is a `git ls-files` call rather than `common.GLOBS` on purpose — `GLOBS` cannot reach
    the repo root (`RLY23-3`), and an enumerator that silently misses a directory is exactly the
    coverage-invariant failure `check_paths` § UNIVERSE was built for."""
    out = subprocess.run(['git', 'ls-files'], cwd=str(REPO),
                         capture_output=True, text=True, check=True).stdout.splitlines()
    return [rel for rel in out
            if rel and not rel.lower().endswith(BINARY_EXT)]


def double_encoded_runs(text):
    """Maximal non-ASCII runs that read back as cp1252 bytes forming valid UTF-8.

    Returns `[(start_offset, run), ...]`. See the module header for why a round trip rather than a
    pattern list — this predicate is the checker, and `--selftest` drives exactly this function.

    ⚠ THE OFFSET IS CARRIED, NOT RECOVERED. The first version returned bare runs and `inspect()`
    located each with `text.index(run)`, which returns the FIRST occurrence — so a file with the
    same mangled em-dash on twenty lines reported line 41 twenty times. Caught on this checker's
    first real scan, where the repetition was the tell. A location recovered by searching for the
    content is a second derivation of something already known, and it was wrong."""
    runs, cur, start = [], [], 0
    for i, ch in enumerate(text):
        if ord(ch) > 127:
            if not cur:
                start = i
            cur.append(ch)
            continue
        if cur:
            runs.append((start, ''.join(cur)))
            cur = []
    if cur:
        runs.append((start, ''.join(cur)))

    hits = []
    for offset, run in runs:
        if len(run) < 2:
            continue          # one accented character cannot be a multi-byte sequence
        try:
            raw = run.encode('cp1252')
        except UnicodeEncodeError:
            continue          # not representable in cp1252 => cannot have come from it
        try:
            raw.decode('utf-8')
        except UnicodeDecodeError:
            continue          # reads back as noise => genuine accented text, not mojibake
        hits.append((offset, run))
    return hits


def inspect(rel):
    """Return a list of (kind, detail) violations for one repo-relative path."""
    path = REPO / rel
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return [('unreadable', str(exc))]

    bad = []
    if raw.startswith(BOM):
        bad.append(('bom', 'file begins with a UTF-8 BOM (EF BB BF)'))
        raw = raw[len(BOM):]

    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError as exc:
        # Byte offset is a real location in a real file, not a citation into another artifact, so
        # it does not drift the way a line-number citation does.
        return bad + [('undecodable', 'byte %d: %s' % (exc.start, exc.reason))]

    for offset, run in double_encoded_runs(text):
        line = text.count('\n', 0, offset) + 1
        try:
            intended = run.encode('cp1252').decode('utf-8')
        except (UnicodeEncodeError, UnicodeDecodeError):   # pragma: no cover - guarded upstream
            intended = '?'
        bad.append(('double-encoded',
                    'line %d: %r should almost certainly be %r' % (line, run, intended)))
    return bad


def scan(paths=None):
    rels = paths if paths is not None else tracked_text_files()
    out = []
    for rel in rels:
        for kind, detail in inspect(rel):
            out.append((rel, kind, detail))
    return out


# --------------------------------------------------------------------------- controls
# ⚠ THE CONTROL TEXT IS THE CHECKER'S OWN, verbatim — `common.run_controls` records three agents
# who probed with a hand-written violation the checker does not detect, passed, and nearly drew the
# opposite conclusion.
#
# ⚠ THE MUST-SUPPRESS HALF IS THE EXPENSIVE ONE HERE. A false positive on this checker fires on
# every citation of Adámek, Schütte or Carlström and on the corpus's own glyphs, which would make it
# the checker everyone disables. Each suppression case below is a real string from this repository.
def _mangle(good):
    """Corrupt `good` exactly as a cp1252 mis-decode would: UTF-8 bytes read as cp1252.

    This is the inverse of the repair, and writing the fixtures this way is what keeps this file's
    own source free of the thing it detects. It also makes each control self-describing: the test
    data is written as what it SHOULD say."""
    return good.encode('utf-8').decode('cp1252')


_MUST_FIRE = [
    ('em dash, cp1252 round trip', _mangle('the rule — and its consequence')),
    ('curly apostrophe', _mangle('the checker’s own output')),
    ('emoji, doubly mangled', _mangle('\U0001f4d6 THE FULL ARGUMENT')),
    ('accented letter via cp1252', _mangle('Adámek–Milius–Moss')),
]
_MUST_SUPPRESS = [
    ('a real em dash', 'the rule — and its consequence'),
    ('real accented citations', 'Adámek–Milius–Moss, Schütte, Carlström, Escardó'),
    ('the corpus glyphs', 'the pole ⊥ = 0 = ∞ in ℤ₂ with ε₀ above it'),
    ('a real emoji pointer', '📖 THE FULL ARGUMENT — tools/verify/README.md'),
    ('pure ASCII', 'nothing here is non-ascii at all'),
    ('lone accented char between ascii', 'Sao Paulo becomes São Paulo here'),
]


def selftest():
    return common.fire_suppress(_MUST_FIRE, _MUST_SUPPRESS,
                                double_encoded_runs, 'double-encoded text')


def main(argv):
    if '--selftest' in argv:
        print('=' * 44)
        print('  encoding-integrity check - CONTROLS')
        print('=' * 44)
        return selftest()

    explicit = [a for a in argv if not a.startswith('-')]
    if explicit:
        rels = [os.path.relpath(os.path.abspath(a), str(REPO)).replace('\\', '/')
                for a in explicit]
        hits = scan(rels)
        scope = '%d file(s) named on the command line' % len(rels)
    else:
        rels = tracked_text_files()
        hits = scan(rels)
        scope = '%d tracked text file(s)' % len(rels)

    print('=' * 44)
    print('  encoding-integrity check')
    print('  scope                    : %s' % scope)
    print('  BOM                      : %d' % sum(1 for h in hits if h[1] == 'bom'))
    print('  undecodable              : %d' % sum(1 for h in hits if h[1] == 'undecodable'))
    print('  double-encoded           : %d' % sum(1 for h in hits if h[1] == 'double-encoded'))
    print('=' * 44)
    for rel, kind, detail in hits:
        print('  %s  [%s]' % (rel, kind))
        print('      %s' % detail)

    if hits:
        print('\nA file was written through a codepage that is not UTF-8.')
        print('DO NOT hand-repair character by character - rewrite the whole passage, then re-run.')
        print('Safe write recipes (and why PowerShell 5.1 does this): tools/process/file-encoding.md')
        return 1 if '--block' in argv else 0
    print('OK: every file in scope is clean UTF-8, no BOM, no double-encoding.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
