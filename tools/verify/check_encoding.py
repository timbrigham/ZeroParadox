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


# Windows-1252 AS WINDOWS IMPLEMENTS IT, which is the mis-decoder whose damage this file exists to
# catch. Python's `cp1252` codec is NOT that table: it leaves 0x81 0x8D 0x8F 0x90 0x9D UNDEFINED and
# raises, while the OS maps each to the C1 control of the same value.
#
# ⚠ THAT GAP WAS A FAIL-OPEN, MEASURED 2026-08-21 BY A `/rely` TRIAL ON THIS FILE'S FIRST VERSION.
# Those five bytes are ordinary UTF-8 continuation bytes, so real corpus glyphs mangle straight into
# them and the `except UnicodeEncodeError` swallowed the run as "not representable, cannot be
# mojibake" — the exact opposite of the truth. Corrupting this repository's own CLAUDE.md with a
# mangled star (U+2B50 = E2 AD 90, and 0x90 is one of the five) returned exit 0 and "no
# double-encoding". Blind glyphs included ℝ, ₁, ← and ⭐; worse, one blind character MASKED its
# neighbours, because the run is tested whole.
#
# The fix is the full 256-entry table, not another special case: encode by lookup and treat a
# missing key as "not representable", which is the same predicate the codec was meant to supply.
# ⚠ WRITTEN AS CODE POINTS, NOT LITERALS, AND THAT IS THIS FILE'S STANDING CONSTRAINT (see
# the header): a detector whose source contains instances of what it detects can never report
# clean. Spelling the five undefined slots out as the C1 controls Windows produces also makes the
# gap that caused the fail-open VISIBLE rather than implicit -- and the first draft of this very
# fix wrote the block as literals and silently dropped 0x81, which the length assert now catches.
_W1252_80_9F = (
    '\u20ac\u0081\u201a\u0192\u201e\u2026\u2020\u2021'   # 0x81 undefined -> U+0081
    '\u02c6\u2030\u0160\u2039\u0152\u008d\u017d\u008f'   # 0x8d, 0x8f undefined
    '\u0090\u2018\u2019\u201c\u201d\u2022\u2013\u2014'   # 0x90 undefined
    '\u02dc\u2122\u0161\u203a\u0153\u009d\u017e\u0178'   # 0x9d undefined
)
WIN1252_DECODE = (''.join(chr(b) for b in range(0x80))
                  + _W1252_80_9F
                  + ''.join(chr(b) for b in range(0xa0, 0x100)))
WIN1252_ENCODE = {ch: i for i, ch in enumerate(WIN1252_DECODE)}
assert len(_W1252_80_9F) == 32, 'the 0x80-0x9F block must be exactly 32 entries'
assert len(WIN1252_DECODE) == 256 and len(WIN1252_ENCODE) == 256, 'table must be total and 1:1'


def w1252_encode(s):
    """The bytes a Windows mis-decode would have produced this text from.

    Raises `ValueError` when `s` is not representable — which is the real signal, because text that
    Windows-1252 cannot express cannot have come from a Windows-1252 mis-decode."""
    try:
        return bytes(WIN1252_ENCODE[ch] for ch in s)
    except KeyError:
        raise ValueError('not representable in Windows-1252')


def w1252_decode(raw):
    """Read bytes the way Windows would. Total on all 256 values, unlike Python's codec."""
    return ''.join(WIN1252_DECODE[b] for b in raw)


def double_encoded_runs(text):
    """Maximal non-ASCII runs that read back as Windows-1252 bytes forming valid UTF-8.

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

    # ⚠⚠ SPLIT EACH RUN AT THE CHARACTERS WINDOWS-1252 CANNOT EXPRESS, AND TEST THE PIECES.
    # Testing a run WHOLE was a fail-open, measured 2026-08-21 (/rely round 2): one legitimate glyph
    # touching mojibake makes the whole run un-encodable, so `except ValueError` discarded it and the
    # file came back clean. `⊥<mangled apostrophe>s floor` — where the mojibake is this checker's own
    # control #2 verbatim — returned exit 0. Measured exposure: 3,077 multi-character non-ASCII runs
    # across 271 of 409 tracked files, and ANY single non-ASCII neighbour suppressed the lot.
    #
    # It is reachable rather than theoretical: this checker's own banner tells you to rewrite the
    # passage, and a partial repair produces exactly this mixed shape — clean glyph beside mojibake.
    #
    # ⚠ ROUND 1's MASKING CONTROL DID NOT COVER THIS AND LOOKED LIKE IT DID. `_mangle('a — ⭐ b')`
    # mangles BOTH characters, so it tests masking-by-mojibake; the hole is masking-by-GENUINE-glyph.
    # A control built by mangling everything can never exhibit a mixed run. See `_MUST_FIRE`.
    hits = []
    for offset, run in runs:
        piece, p_start = [], 0
        for i, ch in enumerate(run + '\0'):          # sentinel forces the final flush
            if ch != '\0' and ch in WIN1252_ENCODE:
                if not piece:
                    p_start = i
                piece.append(ch)
                continue
            if len(piece) >= 2:                      # one character cannot be a multi-byte sequence
                sub = ''.join(piece)
                try:
                    w1252_encode(sub).decode('utf-8')
                except (ValueError, UnicodeDecodeError):
                    pass          # reads back as noise => genuine accented text, not mojibake
                else:
                    hits.append((offset + p_start, sub))
            piece = []
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
            intended = w1252_encode(run).decode('utf-8')
        except (ValueError, UnicodeDecodeError):           # pragma: no cover - guarded upstream
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
    return w1252_decode(good.encode('utf-8'))


_MUST_FIRE = [
    ('em dash, cp1252 round trip', _mangle('the rule — and its consequence')),
    ('curly apostrophe', _mangle('the checker’s own output')),
    ('emoji, doubly mangled', _mangle('\U0001f4d6 THE FULL ARGUMENT')),
    ('accented letter via cp1252', _mangle('Adámek–Milius–Moss')),
    # ⚠ THE FIVE BYTES PYTHON'S `cp1252` LEAVES UNDEFINED. Every case below returned exit 0 and
    # "no double-encoding" against this checker's first version (/rely, 2026-08-21); each names the
    # blind byte so a regression is legible rather than just red. See the table above.
    ('blind 0x90 - a mangled star, from this repo\'s own CLAUDE.md', _mangle('⭐⭐ WHERE THINGS LIVE')),
    ('blind 0x9d - a mangled ℝ, 762 occurrences in the corpus', _mangle('the reals ℝ are where the snap fails')),
    ('blind 0x81 - a mangled subscript, 470 occurrences', _mangle('ε₁ is a fixed point of the tower')),
    ('blind 0x90 - a mangled left arrow, 167 occurrences', _mangle('the snap ⊥ ← ε₀ run backwards')),
    # ⚠ MASKING: the run is tested WHOLE, so one blind character used to silence a neighbour that
    # fires on its own. This case is the reason the fix had to be the full table and not a fifth
    # special case -- a per-character patch would still have missed it.
    ('a blind glyph MASKING an em dash that fires alone', _mangle('a — ⭐ b')),
    # ⚠⚠ MASKING BY A *GENUINE* GLYPH, WHICH IS A DIFFERENT SHAPE AND THE ONE THAT WAS OPEN.
    # Every case above is built by mangling the WHOLE string, so it can never produce a run that
    # mixes mojibake with a legitimate character -- and a mixed run is exactly what defeated the
    # whole-run test (/rely round 2). These are built by hand: real glyph ADJACENT to mangled text,
    # no separating ASCII. `⊥` and `ℝ` are not expressible in Windows-1252, which is precisely why
    # they used to suppress the neighbour they touch.
    ('mojibake touching a real ⊥', '⊥' + _mangle('’s floor is the pole')),
    ('mojibake touching a real ℝ', _mangle('the reals —') + 'ℝ'),
    ('mojibake fenced by real glyphs on BOTH sides', '∞' + _mangle('—') + 'ε'),
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
