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
    # ⚠⚠ NO CUT SITES. Scan for ANY window that round-trips; do not decide where the run divides.
    #
    # THIS IS THE THIRD SHAPE, AND THE FIRST TWO WERE THE SAME MISTAKE. Round 1 cut nowhere (test
    # the run whole) and a single inexpressible glyph suppressed it. Round 2 cut at inexpressible
    # characters — and an EXPRESSIBLE one (an em dash, `¹`, `·`, `¬`, `§`, any Latin-1 accent) is
    # then not a cut site, stays inside the piece, and suppresses it exactly as before:
    # `The gate —<mangled apostrophe>s verdict is final.` returned exit 0 and "clean" (/rely round 3).
    # Corpus exposure measured: 295 multi-character runs across 70 tracked files already carry such
    # a masker.
    #
    # Both failures were *"which cut is right"*, which is the enumeration shape CLAUDE.md § RUNG 5
    # names — each fix closes the cut its author thought of. A predicate with no cut point cannot get
    # the cut wrong. Measured on adoption: fires on all 12 `_MUST_FIRE` and all 3 round-3 attacks,
    # silent on all 6 `_MUST_SUPPRESS`, and **0 hits across the whole 409-file tracked corpus** — so
    # it is strictly more sensitive without being a false-positive generator.
    #
    # Longest window first, then skip past it: a longer round trip is MORE evidence of mojibake, not
    # less, and consuming it stops one mangled sentence reporting as a dozen overlapping fragments.
    hits = []
    for offset, run in runs:
        i, n = 0, len(run)
        while i < n - 1:
            found = None
            for j in range(n, i + 1, -1):
                sub = run[i:j]
                if len(sub) < 2:
                    break                 # one character cannot be a multi-byte sequence
                try:
                    w1252_encode(sub).decode('utf-8')
                except (ValueError, UnicodeDecodeError):
                    continue              # this window reads back as noise; try a shorter one
                found = sub
                break
            if found:
                hits.append((offset + i, found))
                i += len(found)
            else:
                i += 1
    return hits


# ═══ VERIFIED EXCLUSIONS ═══════════════════════════════════════════════════════════════════════
#
# Tim, 2026-08-21: *"make it warn instead of block, and keep a whitelist that have been verified
# exclusions."*
#
# ⚠ WHY THIS EXISTS, AND IT IS A REAL TRADE RATHER THAN A CONCESSION. The round-trip predicate
# cannot separate mojibake from some genuine Western-European typography, and the reason is
# structural, not a bug worth patching: UTF-8's 2-byte lead bytes C2-DF land exactly on
# `Â Ã ... × Ø ...` in Windows-1252, so `3 × 10²` encodes to D7 B2, which IS valid UTF-8. Measured
# (/rely round 4): 14 of 15 constructed GENUINE strings fire — French guillemets after an accented
# capital, an all-caps accented word in curly quotes, an engineering tolerance. No cut-site choice
# fixes it; rounds 1-3 each tried a different one.
#
# So the DOUBLE-ENCODED leg WARNS and the whitelist keeps the warning list short enough to read.
# ⚠ BOM AND UNDECODABLE STILL BLOCK — they are exact, have no false-positive class, and a warning
# nobody must act on is how the other two would rot.
#
# ⚠⚠ THIS IS NOT A BASELINE, AND THE DIFFERENCE IS THE WORD *VERIFIED*. A baseline grandfathers
# whatever happened to be there; every line here records the exact RUN a human confirmed is genuine
# typography, so the entry dies the moment the text changes and cannot silently cover new damage.
# It is a data switch of exactly the kind the four suppression baselines are, so it is hashed in
# `batch.CHECKERS` and registered in `guards.py`.
# Resolved from `common.HERE` (which derives from `__file__`), never written down as a literal
# path — a hardcoded path is a copy and drifts exactly like a mirrored file. The whitelist travels
# with the checker, the same rule the baselines follow.
WHITELIST = common.HERE / 'encoding_whitelist.txt'


def load_whitelist():
    """`{(rel, run)}` a human has verified is genuine typography, not mojibake.

    Format, one per line: `<repo-relative path>\\t<the exact run>\\t<why it is genuine>`. Keyed on
    the RUN and not on a line number, because a line number is a copy of a location and drifts —
    edit the line and the entry stops applying, which is the behaviour we want."""
    out = set()
    if not WHITELIST.exists():
        return out
    for line in WHITELIST.read_text(encoding='utf-8').splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split('\t')
        if len(parts) < 3 or not parts[2].strip():
            continue      # an entry with no stated reason is not a VERIFIED exclusion
        out.add((parts[0].strip().replace('\\', '/').lower(), parts[1]))
    return out


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

    allowed = load_whitelist()
    key = str(rel).replace('\\', '/').lower()
    for offset, run in double_encoded_runs(text):
        if (key, run) in allowed:
            continue                        # verified genuine typography, with a stated reason
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
    # ⚠⚠ MASKED BY A cp1252-EXPRESSIBLE GLYPH. The round-2 controls all mask with characters
    # Windows-1252 CANNOT express (⊥, ℝ, ∞), which the round-2 fix cut at — so they passed while
    # the em-dash case below returned exit 0 and "clean". A masker the codec CAN express is the
    # other half of the surface and the reason the predicate is now cut-site-free. Measured
    # corpus exposure for these: ¹ (187 runs), · (58), ¬ (51), § (15), – (5).
    ('mojibake masked by an em dash it CAN express', 'The gate —' + _mangle('’s verdict')),
    ('mojibake masked by a superscript one', _mangle('the rule —') + '¹'),
    ('mojibake masked by a section sign', '§' + _mangle('—') + '·'),
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

    # ⚠ THE REASON FIELD IS EMITTED EMPTY, DELIBERATELY. This automates the mechanical half — the
    # exact path and the exact run, which contains characters nobody wants to retype — and refuses
    # to automate the judgement. `load_whitelist()` ignores an entry with no stated reason, so an
    # appended line suppresses NOTHING until a human opens it and says why the text is genuine.
    # A generated placeholder would have made the entry live on write, which is the opposite of
    # what "verified exclusions" means.
    if '--emit-whitelist' in argv:
        rels = ([os.path.relpath(os.path.abspath(a), str(REPO)).replace('\\', '/')
                 for a in explicit] if explicit else tracked_text_files())
        # ⚠ ONE PASS PER FILE, and each (file, run) emitted ONCE. Iterating `scan()` rows and then
        # re-scanning each file inside that loop emitted the cross product — 4 lines for 2 hits —
        # and a duplicate whitelist entry is a second copy of a suppression, which is the drift this
        # whole bundle exists to stop. `inspect()` already tells us which files are implicated.
        flagged = sorted({rel for rel, kind, _d in scan(rels) if kind == 'double-encoded'})
        n = 0
        for rel in flagged:
            try:
                text = (REPO / rel).read_bytes().decode('utf-8')
            except (OSError, UnicodeDecodeError):       # pragma: no cover - blocked elsewhere
                continue
            for run in sorted({r for _off, r in double_encoded_runs(text)}):
                print('%s\t%s\t' % (rel, run))
                n += 1
        if not n:
            print('# nothing to whitelist: no suspected double-encoding in scope')
        return 0

    if explicit:
        rels = [os.path.relpath(os.path.abspath(a), str(REPO)).replace('\\', '/')
                for a in explicit]
        hits = scan(rels)
        scope = '%d file(s) named on the command line' % len(rels)
    else:
        rels = tracked_text_files()
        hits = scan(rels)
        scope = '%d tracked text file(s)' % len(rels)

    # ⚠ TWO TIERS, AND THE SPLIT IS THE POINT (Tim, 2026-08-21). `bom` and `undecodable` are EXACT
    # tests with no false-positive class, so they BLOCK. `double-encoded` is a heuristic that
    # provably cannot separate mojibake from some genuine typography (see WHITELIST above), so it
    # WARNS — a gate that can halt work on correct prose is one that gets disabled, and disabling it
    # would take the two exact tests down with it.
    blocking = [h for h in hits if h[1] in ('bom', 'undecodable', 'unreadable')]
    warning = [h for h in hits if h[1] == 'double-encoded']
    n_allowed = len(load_whitelist())

    print('=' * 44)
    print('  encoding-integrity check')
    print('  scope                    : %s' % scope)
    print('  BOM               BLOCK  : %d' % sum(1 for h in hits if h[1] == 'bom'))
    print('  undecodable       BLOCK  : %d' % sum(1 for h in hits if h[1] == 'undecodable'))
    print('  double-encoded    warn   : %d' % len(warning))
    print('  verified exclusions      : %d  (encoding_whitelist.txt)' % n_allowed)
    print('=' * 44)
    for rel, kind, detail in blocking:
        print('  %s  [%s]' % (rel, kind))
        print('      %s' % detail)
    for rel, kind, detail in warning:
        print('  %s  [%s — WARN]' % (rel, kind))
        print('      %s' % detail)

    if warning:
        print('\n%d suspected double-encoding(s) — WARNING, not a block.' % len(warning))
        print('DO NOT hand-repair character by character - rewrite the whole passage, then re-run.')
        print('If a site is GENUINE typography, whitelist it — the runs contain characters that are')
        print('painful to retype, so let the checker write the lines for you:')
        print('    python %s <paths> --emit-whitelist >> %s'
              % (SELF, os.path.relpath(str(WHITELIST), str(REPO)).replace('\\', '/')))
        print('then OPEN each appended line and state why it is genuine. The reason field is left')
        print('EMPTY on purpose: an entry without one is IGNORED, so nothing is suppressed until a')
        print('human has actually looked. Verified exclusions only.')
        print('Safe write recipes (and why PowerShell 5.1 does this): tools/process/file-encoding.md')
    if blocking:
        print('\nA file was written through a codepage that is not UTF-8, or could not be read.')
        print('Safe write recipes: tools/process/file-encoding.md')
        return 1 if '--block' in argv else 0
    if not warning:
        print('OK: every file in scope is clean UTF-8, no BOM, no double-encoding.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
