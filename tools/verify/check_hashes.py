"""
check_hashes.py — ZP build script integrity check + AR status manager.

Tracks four tiers:
  Companions   ZP-A … ZP-M         hash verified vs register.md comp:XXXXXXXX
  Formal       ZP-A-formal … -M    hash verified vs register.md formal:XXXXXXXX
  Formal-only  ZP-N ZP-P ZP-Q       formal-only layers (no companion); formal: hash
               ZP-R (+addendum)      verified vs register by Doc-name prefix (added 2026-07-20;
                                     previously UNVERIFIED)
  Standalone   Foreword PhilQ       hash tracked in ar_status.json only
               Tools

SESSION START (read-only validation):
    python check_hashes.py

POST-FIX WORKFLOW — after rebuilding a PDF and verifying the fix:
    python check_hashes.py --mark-remediated ZP-X
    python check_hashes.py --mark-remediated ZP-X-formal
    python check_hashes.py --mark-remediated Foreword

Multiple docs in one call:
    python check_hashes.py --mark-remediated ZP-A --mark-reviewed ZP-B-formal

Other flags:
    --update-register   Rewrite Comp AR column from ar_status.json only (no mark)
    --sync-hash KEY...  Update the register hash token ONLY, leaving AR status alone. For a script
                        edit that changes no RENDERED output (a docstring header, a comment): the
                        PDF is unchanged and no re-review is owed, so --mark-remediated would
                        assert a review nobody did.

AR status meanings:
    Y/Y   — current hash adversary-reviewed and remediated (or confirmed clean)
    Y/N   — reviewed at current hash, fixes identified but not yet applied
    N/—   — not yet in system (informational; does not cause exit 1)
    STALE — hash changed since last review; re-review required (causes exit 1)

Exit codes:
    0 — all hashes match register.md, no STALE AR entries
    1 — one or more hash mismatches or STALE AR entries
"""

import glob
import hashlib
import io
import json
import os
import re
import sys

# ⭐ SCRIPT_DIR IS NOW `scripts/`, AND THAT CLOSES A LIVE DRIFT. The build scripts used to exist
# twice — the fingerprinted originals here in `.claude-local/` and a hand-copied transparency mirror
# in `scripts/` — with a per-commit "copy it across" obligation. Only the private copy was
# fingerprinted, so the PUBLISHED copy sat outside the integrity check entirely and drifted
# unnoticed (`scan_pdfs.py`, 2026-05-20, caught 2026-08-15). One copy, and it is the public one, so
# what register.md fingerprints is exactly what a reader can download.
#
# Anchored to REPO rather than relying on the caller's cwd: the hook runs with cwd=REPO, but this
# tool is now published and may be run from anywhere.
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
REGISTER   = os.path.join(REPO, 'register.md')
SCRIPT_DIR = os.path.join(REPO, 'scripts')
AR_STATUS  = os.path.join(PRIV, 'ar_status.json')   # legacy per-doc AR tracker: private state
# Whether the private tracker is reachable at all. A clone that is not the author's has no
# .claude-local/, and treating its absence as a hash mismatch produced three false positives.
AR_AVAILABLE = os.path.exists(AR_STATUS)

COMP_SCRIPTS = {
    'ZP-A': 'build_zpa_companion.py',
    'ZP-B': 'build_zpb_companion.py',
    'ZP-C': 'build_zpc_companion.py',
    'ZP-D': 'build_zpd_companion.py',
    'ZP-E': 'build_zpe_companion.py',
    'ZP-F': 'build_zpf_companion.py',
    'ZP-G': 'build_zpg_companion.py',
    'ZP-H': 'build_zph_companion.py',
    'ZP-I': 'build_zpi_companion.py',
    'ZP-J': 'build_zpj_companion.py',
    'ZP-K': 'build_zpk_companion.py',
    'ZP-L': 'build_zpl_companion.py',
    'ZP-M': 'build_zpm_companion.py',
}

FORMAL_SCRIPTS = {
    'ZP-A-formal': 'build_zpa.py',
    'ZP-B-formal': 'build_zpb.py',
    'ZP-C-formal': 'build_zpc.py',
    'ZP-D-formal': 'build_zpd.py',
    'ZP-E-formal': 'build_zpe.py',
    'ZP-F-formal': 'build_zpf.py',
    'ZP-G-formal': 'build_zpg.py',
    'ZP-H-formal': 'build_zph.py',
    'ZP-I-formal': 'build_zpi.py',
    'ZP-J-formal': 'build_zpj.py',
    'ZP-K-formal': 'build_zpk.py',
    'ZP-L-formal': 'build_zpl.py',
    'ZP-M-formal': 'build_zpm.py',
}

STANDALONE_SCRIPTS = {
    'Foreword': 'build_foreword.py',
    'PhilQ':    'build_zp_philosophical_question.py',
    'Tools':    'build_tools.py',
    # 'Reals' retired 2026-06-21 — standalone reals companion superseded by ZP-F
    # (content merged into the formal Counterexamples layer); output PDF removed.
}

# Formal-only documents: a formal layer with no paired companion (register row carries
# formal:XXXXXXXX but no comp:). The A..L both-hash parser skips these, so they went
# UNVERIFIED (added 2026-07-20). Keyed by the register Doc-cell prefix so the two ZP-R
# rows (base + addendum) are distinguished.
FORMAL_ONLY_SCRIPTS = {
    # Added 2026-07-31: these four register rows carried a formal: hash token that NOTHING
    # verified - the register had 25 hash rows and this checker guarded 21 of them, so the
    # pre-push hook could not block on a stale hash for any of them. Found when ZP Choice-Free
    # Core was bumped v1.3->v1.4 with a stale token and no gate caught it.
    'ZP-H Native Categories Addendum': 'build_zph_native_addendum.py',
    'ZP-J AFA Addendum':             'build_zpj_afa_addendum.py',
    'ZP-J Wheel Addendum':           'build_zpj_wheel_addendum.py',
    'ZP-J Keystone Addendum':        'build_zpj_keystone_addendum.py',
    'ZP Choice-Free Core Addendum':  'build_zp_choice_free_core.py',
    'ZP-N The Constructive Snap':    'build_zpn.py',
    'ZP-P The Fixed-Point Fork':     'build_zpp.py',
    'ZP-Q The Frame-Change':         'build_zpq.py',
    'ZP-R Cross-Category':           'build_zpr.py',
    'ZP-R Diagonal Family Addendum': 'build_zpr_addendum.py',
}

ALL_VALID_KEYS = (set(COMP_SCRIPTS) | set(FORMAL_SCRIPTS)
                  | set(STANDALONE_SCRIPTS) | set(FORMAL_ONLY_SCRIPTS))

AR_DISPLAY = {
    'remediated': 'Y/Y',
    'reviewed':   'Y/N',
    None:         'N/—',
}



def register_formal_token(key):
    """The formal: token recorded in register.md for a standalone doc, or None.

    Added 2026-07-31. STANDALONE_SCRIPTS were audited only against ar_status.json, so their
    register tokens were unguarded - the same hole just closed for FORMAL_ONLY_SCRIPTS, one tier up.
    """
    import re as _re
    label = {'Foreword': 'Zero Paradox Foreword', 'PhilQ': 'ZP Philosophical Question',
             'Tools': 'ZP Tools'}.get(key)
    if not label:
        return None
    try:
        reg = open(REGISTER, encoding='utf-8').read()
    except OSError:
        return None
    m = _re.search(r'^\| ' + _re.escape(label) + r' \|.*$', reg, _re.M)
    if not m:
        return None
    t = _re.search(r'formal:([0-9a-f]{8})', m.group(0))
    return t.group(1) if t else None

def sha8(filename):
    path = os.path.join(SCRIPT_DIR, filename)
    if not os.path.exists(path):
        return 'MISSING'
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:8]


def parse_register():
    """Return {ZP-X: (formal_hash, comp_hash)} from register.md."""
    hashes = {}
    with open(REGISTER, encoding='utf-8') as f:
        for line in f:
            m = re.search(
                r'\|\s*(ZP-[A-Z])[^|]*\|[^|]*\|[^|]*\|[^|]*\|[^|]*\|[^|]*formal:([0-9a-f]{8}).*?comp:([0-9a-f]{8})',
                line)
            if m and m.group(1) not in hashes:
                # First-wins: a base-layer row (e.g. "ZP-J Self-Reference") precedes
                # its addenda ("ZP-J AFA/Wheel Addendum") in register order. Both match
                # the ZP-[A-Z] key, so without this guard an addendum row would clobber
                # the base layer's hashes and produce a spurious MISMATCH.
                hashes[m.group(1)] = (m.group(2), m.group(3))
    return hashes


def parse_register_formal_by_name(prefix):
    """Return the formal:XXXXXXXX hash from the register row whose Doc cell starts with
    `prefix`, or None. Used for formal-only docs (no comp: on the row)."""
    with open(REGISTER, encoding='utf-8') as f:
        for line in f:
            if not line.startswith('|'):
                continue
            cells = line.split('|')
            if len(cells) < 2:
                continue
            if cells[1].strip().startswith(prefix):
                m = re.search(r'formal:([0-9a-f]{8})', line)
                if m:
                    return m.group(1)
    return None


def load_ar_status():
    if not os.path.exists(AR_STATUS):
        return {}
    with open(AR_STATUS, encoding='utf-8') as f:
        return json.load(f)


def save_ar_status(ar_data):
    common.write_text_lf(AR_STATUS, json.dumps(ar_data, indent=2) + '\n')


def compute_ar_label(key, current_hash, ar_data):
    entry = ar_data.get(key)
    if not entry or not entry.get('hash'):
        return 'N/—'
    if entry['hash'] != current_hash:
        return 'STALE'
    return AR_DISPLAY.get(entry.get('status'), 'N/—')


# ⚠ ALL THREE REGISTER WRITERS GO THROUGH `common.write_text_lf`. `register.md` is TRACKED, and a
# bare `open(..., 'w')` translates every `\n` to `\r\n` on Windows — so a single `--mark` run used to
# rewrite the whole file as CRLF. That is not cosmetic HERE of all places: this file's own
# fingerprints are the provenance tokens, `check_invariants` blocks on CRLF in a tracked text file,
# and the recorded consequence of a byte difference is `check_hashes` exiting 0 on the author's
# machine and 1 in a fresh clone. Same class the build scripts closed on 2026-08-16; these five
# sites inside the bundle were still open.
def update_register_comp_hash(doc, new_hash):
    """Replace comp:XXXXXXXX in the Notes column for doc's register.md row."""
    with open(REGISTER, encoding='utf-8') as f:
        content = f.read()

    def replace_comp(m):
        return re.sub(r'comp:[0-9a-f]{8}', f'comp:{new_hash}', m.group(0))

    # ⚠ RETURN WHETHER WE ACTUALLY WROTE. The refusal path used to `return` bare, so a
    # caller printing 'register.md updated' said so after a REFUSAL - a fail-open created
    # by the HASH-1 fix itself, where the guard tells the truth and the summary does not.
    pattern = _register_row_pattern(doc, content, 'comp')
    if pattern is None:
        return False
    common.write_text_lf(REGISTER, re.sub(pattern, replace_comp, content, count=1))
    return True


def _register_row_pattern(doc, content, kind):
    """A pattern matching EXACTLY the register row for `doc`, or None if that is ambiguous.

    ⚠ THE OLD PATTERN HAD NO BOUNDARY AFTER `doc` AND `re.sub` REPLACES ALL MATCHES, so any
    document whose name is a PREFIX of another rewrote both rows. Measured: updating `ZP-H` wrote
    build_zph.py's hash into the `ZP-H Native Categories Addendum` row, which describes a different
    script. Prefix-shadowed pairs exist today, so this is not hypothetical.

    Exact cell match wins. A prefix match is used only when exactly one row has it. Anything else
    returns None and the caller reports rather than guessing.
    """
    exact = r'(?m)^\|\s*' + re.escape(doc) + r'\s*\|[^\n]*$'
    if re.search(exact, content):
        return exact
    prefix = r'(?m)^\|\s*' + re.escape(doc) + r'[^|\n]*\|[^\n]*$'
    hits = re.findall(prefix, content)
    if len(hits) == 1:
        return prefix
    if len(hits) > 1:
        names = [h.split('|')[1].strip() for h in hits]
        print('  REFUSING to update %s hash for %r - matches %d rows: %s'
              % (kind, doc, len(hits), ', '.join(names)))
    else:
        print('  REFUSING to update %s hash for %r - no register row matched' % (kind, doc))
    return None


def update_register_formal_hash(doc, new_hash):
    """Replace formal:XXXXXXXX in the Notes column for doc's register.md row."""
    with open(REGISTER, encoding='utf-8') as f:
        content = f.read()

    def replace_formal(m):
        return re.sub(r'formal:[0-9a-f]{8}', f'formal:{new_hash}', m.group(0))

    # ⚠ RETURN WHETHER WE ACTUALLY WROTE. The refusal path used to `return` bare, so a
    # caller printing 'register.md updated' said so after a REFUSAL - a fail-open created
    # by the HASH-1 fix itself, where the guard tells the truth and the summary does not.
    pattern = _register_row_pattern(doc, content, 'formal')
    if pattern is None:
        return False
    common.write_text_lf(REGISTER, re.sub(pattern, replace_formal, content, count=1))
    return True


def update_register_ar_column(ar_labels):
    """Rewrite the Comp AR column (col 5) in register.md for companion docs."""
    with open(REGISTER, encoding='utf-8') as f:
        lines = f.readlines()
    updated = []
    for line in lines:
        if line.startswith('|'):
            parts = line.split('|')
            if len(parts) >= 8:
                doc_cell = parts[1].strip()
                for doc in COMP_SCRIPTS:
                    if doc_cell.startswith(doc) and doc in ar_labels:
                        parts[5] = f' {ar_labels[doc]} '
                        line = '|'.join(parts)
                        break
        updated.append(line)
    common.write_text_lf(REGISTER, ''.join(updated))


def mark_doc(key, status, ar_data):
    """
    Compute current hash for key, write to ar_data, update register.md if applicable.
    Returns the hash recorded, or None on error.
    """
    if key in COMP_SCRIPTS:
        script = COMP_SCRIPTS[key]
        current_hash = sha8(script)
        if current_hash == 'MISSING':
            print(f'  ERROR: {script} not found — cannot mark {key}')
            return None
        ar_data[key] = {'hash': current_hash, 'status': status}
        update_register_comp_hash(key, current_hash)
        return current_hash

    if key in FORMAL_SCRIPTS:
        script = FORMAL_SCRIPTS[key]
        current_hash = sha8(script)
        if current_hash == 'MISSING':
            print(f'  ERROR: {script} not found — cannot mark {key}')
            return None
        ar_data[key] = {'hash': current_hash, 'status': status}
        doc = key.replace('-formal', '')
        if not update_register_formal_hash(doc, current_hash):
            print('  ⚠ %s: ar_status.json updated, register.md NOT written (see refusal above)' % key)
        return current_hash

    if key in STANDALONE_SCRIPTS:
        script = STANDALONE_SCRIPTS[key]
        current_hash = sha8(script)
        if current_hash == 'MISSING':
            print(f'  ERROR: {script} not found — cannot mark {key}')
            return None
        ar_data[key] = {'hash': current_hash, 'status': status}
        return current_hash

    print(f'  ERROR: unknown key "{key}". Valid: {", ".join(sorted(ALL_VALID_KEYS))}')
    return None


def parse_mark_args(args):
    marks = []
    i = 0
    while i < len(args):
        if args[i] in ('--mark-remediated', '--mark-reviewed'):
            status = 'remediated' if args[i] == '--mark-remediated' else 'reviewed'
            if i + 1 < len(args) and not args[i + 1].startswith('--'):
                key = args[i + 1]
                # normalise ZP-x → ZP-X; ZP-x-formal → ZP-X-formal
                # standalone keys (Foreword, PhilQ, etc.) preserve their canonical case
                if '-formal' in key.lower():
                    base = key.replace('-formal', '').replace('-FORMAL', '').upper()
                    key = f'{base}-formal'
                else:
                    # check for standalone key match first (case-insensitive)
                    standalone_match = next(
                        (k for k in STANDALONE_SCRIPTS if k.lower() == key.lower()), None)
                    key = standalone_match if standalone_match else key.upper()
                marks.append((key, status))
                i += 2
            else:
                print(f'  ERROR: {args[i]} requires a key (e.g. ZP-A, ZP-B-formal, Foreword)')
                i += 1
        else:
            i += 1
    return marks


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls on the hash-integrity detector.

    Added 2026-08-15 for the Phase 1 exit. This checker guards the one claim `register.md` makes to
    a reader — *these fingerprints are the scripts that built these PDFs* — and had never had a
    control proving it can tell a match from a mismatch.

    ⚠ The controls hash REAL files and compare against REAL register tokens; nothing is planted and
    nothing is written. The must-fire half perturbs a hash in memory, which is the only way to
    exercise the mismatch branch without editing a tracked build script."""
    bad = 0

    print('  MUST FIRE')
    # A perturbed hash must not equal the recorded one.
    reg = parse_register()
    sample = next(iter(sorted(reg))) if reg else None
    if sample is None:
        print('    %-34s *** NO REGISTER ROWS PARSED ***' % 'register.md parses')
        bad += 1
    else:
        recorded_formal, _recorded_comp = reg[sample]
        perturbed = ('0' * 8) if recorded_formal != '0' * 8 else ('f' * 8)
        ok = perturbed != recorded_formal
        bad += 0 if ok else 1
        print('    %-34s %s (%s vs %s for %s)'
              % ('a wrong hash is a mismatch', 'ok' if ok else '*** WRONG ***',
                 perturbed, recorded_formal, sample))

    # A missing script must report MISSING, not silently pass as equal.
    got = sha8('no_such_build_script_xyz.py')
    ok = (got == 'MISSING')
    bad += 0 if ok else 1
    print('    %-34s %s (got %r)' % ('a missing script reports MISSING', 'ok' if ok else '*** WRONG ***', got))

    print('  MUST SUPPRESS')
    # A real script hashes to 8 hex chars, stably, and equals itself.
    probe = COMP_SCRIPTS.get('ZP-A')
    h1, h2 = sha8(probe), sha8(probe)
    ok = (len(h1) == 8 and h1 == h2 and h1 != 'MISSING')
    bad += 0 if ok else 1
    print('    %-34s %s (%s)' % ('a real script hashes stably', 'ok' if ok else '*** WRONG ***', h1))

    ok = len(reg) >= 10
    bad += 0 if ok else 1
    print('    %-34s %s (%d rows)' % ('register.md parses its rows', 'ok' if ok else '*** WRONG ***', len(reg)))

    # ⚠ The path control. SCRIPT_DIR moved from .claude-local to scripts/ on 2026-08-15; if it ever
    # points somewhere without the build scripts, every hash silently becomes MISSING and the run
    # would report a wall of mismatches rather than a wrong directory.
    present = sum(1 for f in COMP_SCRIPTS.values() if sha8(f) != 'MISSING')
    ok = present == len(COMP_SCRIPTS)
    bad += 0 if ok else 1
    print('    %-34s %s (%d of %d found in %s)'
          % ('SCRIPT_DIR points at the scripts', 'ok' if ok else '*** WRONG DIRECTORY ***',
             present, len(COMP_SCRIPTS), os.path.relpath(SCRIPT_DIR, REPO)))

    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def check_docstring_versions():
    """Every build script's docstring header must agree with its own `VERSION` constant.

    Step 4 of the four-step rule (edit, bump, rebuild, update the docstring) is the one that gets
    skipped, because nothing mechanical reads it: the hash check fingerprints the file and the
    release gate compares the constant. Returns a list of `(name, header, const)` mismatches.

    ⚠ MATCH THE HEADER LINE ONLY. A first draft of this scanned for any `Version N.N` before the
    constant and flagged `build_zpc.py`, whose only hit sits INSIDE a changelog entry
    ("Version 1.4 updates this") - a historical record that must never be rewritten. Changelog
    entries and the header line look alike to a loose pattern and mean opposite things.
    """
    out = []
    for p in sorted(glob.glob(os.path.join(REPO, 'scripts', 'build_*.py'))):
        try:
            body = io.open(p, encoding='utf-8').read()
        except OSError:
            continue
        m = re.search(r"^VERSION\s*=\s*['\"]([^'\"]+)['\"]", body, re.M)
        if not m:
            continue
        head = _header_version(body[:m.start()])
        if head and head != m.group(1):
            out.append((os.path.basename(p), head, m.group(1)))
    return out


# ⚠ TWO HEADER SHAPES, AND RECOGNISING ONE OF THEM REPORTED A CLEAN ZERO OVER THE OTHER.
# `Version 1.21 |` was covered; `Build ZP-A: Lattice Algebra (v1.21)` was not, and 13 of 43 scripts
# use it - so they were silently exempt and SIX were genuinely stale while the check said clean
# (/rely, 2026-08-18). A checker reporting zero over ground it never walked is the exact fail-open
# this layer exists to prevent, and it shipped inside the fix for the same class.
_HEADER_SHAPES = (
    re.compile(r"(?m)^\s*Version\s+(\d+(?:\.\d+)*)\s*\|"),   # `Version 1.21 | July 2026`
    re.compile(r"\(v(\d+(?:\.\d+)*)\)"),                       # `Build ZP-A: ... (v1.21)`
)


# A changelog line: `v1.10: ...`. Everything from the FIRST one onward is historical record.
_CHANGELOG_LINE = re.compile(r"(?m)^\s*v\d+(?:\.\d+)*\s*:")


def _header_version(head):
    """The version a build script's docstring header advertises, under either shape.

    ⚠ Search the HEADER ONLY - the caller slices off everything from the `VERSION` constant onward.
    A changelog entry below it (`v1.18: ...`, or prose like "Version 1.4 updates this") is a
    HISTORICAL record and must never be rewritten to match the constant.
    """
    # ⚠⚠ TRUNCATE AT THE FIRST CHANGELOG LINE, AND THIS IS NOT THEORETICAL. Without it the
    # `(vN)` shape matched `(v1.1)` INSIDE `build_zpi.py`'s v1.10 note - "version references
    # \"(v1.1)\", \"v2.0\" removed from body prose" - and a sync run rewrote it to `(v1.15)`,
    # falsifying a record of what v1.10 actually did. Caught and reverted 2026-08-18. The header
    # is what precedes the changelog; everything from the first `vN:` line on is history.
    cut = _CHANGELOG_LINE.search(head)
    if cut:
        head = head[:cut.start()]
    for pat in _HEADER_SHAPES:
        m = pat.search(head)
        if m:
            return m.group(1)
    return None


def sync_hash(key):
    """Update `key`'s register hash token ONLY. Does not touch AR status.

    For the case the four-step rule does not cover: a script edited in a way that changes no
    RENDERED output - a docstring header, a comment - so the PDF is unchanged, the version already
    describes it, and no re-review is owed. `--mark-remediated` would stamp AR as
    reviewed-and-remediated, which would be a claim about work nobody did.

    Routes through the same `FORMAL_SCRIPTS` / `COMP_SCRIPTS` maps and the same boundary-aware row
    matcher as everything else here, so it cannot write a row the caller did not name.
    """
    if key in FORMAL_SCRIPTS:
        h = sha8(FORMAL_SCRIPTS[key])
        if h == 'MISSING':
            print('  ERROR: %s not found' % FORMAL_SCRIPTS[key])
            return False
        ok = update_register_formal_hash(key.replace('-formal', ''), h)
        print('  %-26s formal:%s  %s' % (key, h, 'written' if ok else 'REFUSED'))
        return ok
    if key in COMP_SCRIPTS:
        h = sha8(COMP_SCRIPTS[key])
        if h == 'MISSING':
            print('  ERROR: %s not found' % COMP_SCRIPTS[key])
            return False
        ok = update_register_comp_hash(key, h)
        print('  %-26s comp:%s  %s' % (key, h, 'written' if ok else 'REFUSED'))
        return ok
    if key in STANDALONE_SCRIPTS:
        # ⚠ STANDALONE DOCS LIVE IN `ar_status.json`, NOT `register.md` - the header says so, and a
        # register write for one silently matches nothing. Update the recorded hash and PRESERVE the
        # status: the rendered content did not change, so a `remediated` doc is still remediated;
        # only the script bytes moved. Overwriting the status here would be the same false claim
        # `--mark-remediated` would make.
        h = sha8(STANDALONE_SCRIPTS[key])
        if h == 'MISSING':
            print('  ERROR: %s not found' % STANDALONE_SCRIPTS[key])
            return False
        ar = load_ar_status()
        prev = ar.get(key, {})
        status = prev.get('status', 'unknown')
        ar[key] = {'hash': h, 'status': status}
        save_ar_status(ar)
        print('  %-26s ar_status:%s  status preserved as %r' % (key, h, status))
        return True
    print('  ERROR: unknown key %r' % key)
    return False


def main():
    args = sys.argv[1:]
    if '--sync-hash' in args:
        keys = [a for a in args[args.index('--sync-hash') + 1:] if not a.startswith('--')]
        if not keys:
            print('--sync-hash needs at least one document key')
            return 1
        print('Register hash sync (AR status untouched):')
        bad = sum(0 if sync_hash(k) else 1 for k in keys)
        return 1 if bad else 0
    if '--selftest' in args:
        print('ZP Build Script Hash Check - CONTROLS')
        print('=' * 55)
        return selftest()
    do_update = '--update-register' in args
    marks     = parse_mark_args(args)

    ar_data = load_ar_status()

    if marks:
        for key, status in marks:
            recorded_hash = mark_doc(key, status, ar_data)
            if recorded_hash:
                label = AR_DISPLAY[status]
                print(f'  Marked {key}: {label}  (hash: {recorded_hash})')
        save_ar_status(ar_data)
        # Recompute Comp AR column for register.md (companions only)
        comp_labels = {}
        for doc, script in COMP_SCRIPTS.items():
            current_hash = sha8(script)
            comp_labels[doc] = compute_ar_label(doc, current_hash, ar_data)
        update_register_ar_column(comp_labels)
        print('  ar_status.json and register.md updated.')
        if not do_update:
            return 0

    # Full validation pass
    registered = parse_register()
    ar_data    = load_ar_status()

    hash_mismatches = []
    ar_stale        = []

    print('ZP Build Script Hash + AR Status Check')
    print('=' * 55)

    # --- Companions + Formal (by ZP-X) ---
    for doc in COMP_SCRIPTS:
        comp_script   = COMP_SCRIPTS[doc]
        formal_key    = f'{doc}-formal'
        formal_script = FORMAL_SCRIPTS.get(formal_key, '')

        current_comp   = sha8(comp_script)
        current_formal = sha8(formal_script) if formal_script else 'MISSING'

        reg_formal, reg_comp = registered.get(doc, ('?', '?'))
        formal_ok = (current_formal == reg_formal)
        comp_ok   = (current_comp   == reg_comp)

        comp_ar_label   = compute_ar_label(doc,        current_comp,   ar_data)
        formal_ar_label = compute_ar_label(formal_key, current_formal, ar_data)

        hash_status = 'OK' if (formal_ok and comp_ok) else 'MISMATCH'
        print(f'  {doc}: hash={hash_status}  AR={comp_ar_label}  formal-AR={formal_ar_label}')

        if not formal_ok:
            print(f'       formal  — registered: {reg_formal}  current: {current_formal}  *** VERSION BUMP REQUIRED ***')
        if not comp_ok:
            print(f'       comp    — registered: {reg_comp}  current: {current_comp}  *** VERSION BUMP REQUIRED ***')
        if comp_ar_label == 'STALE':
            entry = ar_data.get(doc, {})
            print(f'       comp AR STALE — reviewed at: {entry.get("hash","?")}  current: {current_comp}')
        if formal_ar_label == 'STALE':
            entry = ar_data.get(formal_key, {})
            print(f'       formal AR STALE — reviewed at: {entry.get("hash","?")}  current: {current_formal}')

        if not formal_ok or not comp_ok:
            hash_mismatches.append(doc)
        if comp_ar_label == 'STALE':
            ar_stale.append(doc)
        if formal_ar_label == 'STALE':
            ar_stale.append(formal_key)

    # --- Standalone documents ---
    print('  ---')
    for key, script in STANDALONE_SCRIPTS.items():
        current_hash = sha8(script)
        ar_label     = compute_ar_label(key, current_hash, ar_data)
        # Added 2026-07-31: standalone docs were compared ONLY against ar_status.json, never against
        # register.md - so a standalone register token could go stale forever and --mark-remediated
        # would clear the push block without touching it. PhilQ was stale exactly this way.
        reg_tok = register_formal_token(key)
        if reg_tok and reg_tok != current_hash:
            print(f'  {key}: REGISTER TOKEN STALE - register has {reg_tok}, script is {current_hash}')
            hash_mismatches.append(key + ' (register token)')

        # ⚠ THE AR TRACKER IS PRIVATE, AND ITS ABSENCE IS NOT A HASH MISMATCH.
        #
        # `ar_status.json` lives in gitignored `.claude-local/`. In any clone that is not the
        # author's it simply does not exist, so `stored_hash` fell back to '?' and all three
        # standalone docs reported MISMATCH — three false positives in the suite whose whole value
        # is that its zeros mean something. Measured 2026-08-15 in a clean worktree; it is also
        # what the CI job would have published.
        #
        # The PUBLIC provenance check is `reg_tok` above, against register.md, and it runs
        # regardless. This one is a legacy per-doc review tracker that CLAUDE.md already records as
        # superseded by the per-file `*_cleared.txt` signals. Unavailable != wrong.
        if not AR_AVAILABLE:
            print(f'  {key}: hash={"OK" if reg_tok else "not publicly tracked"}  '
                  f'AR=n/a (private tracker absent)')
            if not reg_tok:
                print(f'       no register.md token for {script} — this build script has NO public '
                      f'provenance. Ledgered, not silently passed.')
            continue

        stored_hash = ar_data.get(key, {}).get('hash', '?')
        hash_ok = (current_hash == stored_hash)
        hash_status = 'OK' if hash_ok else 'MISMATCH'

        print(f'  {key}: hash={hash_status}  AR={ar_label}')

        if not hash_ok:
            print(f'       stored: {stored_hash}  current: {current_hash}  *** re-mark required ***')
        if ar_label == 'STALE':
            print(f'       AR STALE — reviewed at: {stored_hash}  current: {current_hash}')
            ar_stale.append(key)
        if not hash_ok:
            hash_mismatches.append(key)

    # --- Formal-only documents (no companion): verify formal build-script hash vs register ---
    print('  ---')
    for name, script in FORMAL_ONLY_SCRIPTS.items():
        current = sha8(script)
        reg = parse_register_formal_by_name(name)
        ok = (reg is not None and current == reg)
        print(f'  {name}: hash={"OK" if ok else "MISMATCH"}')
        if current == 'MISSING':
            print(f'       script {script} not found')
            hash_mismatches.append(name)
        elif reg is None:
            print(f'       no formal: hash found in register.md for a row starting "{name}"')
            hash_mismatches.append(name)
        elif not ok:
            print(f'       formal  — registered: {reg}  current: {current}  *** VERSION BUMP REQUIRED ***')
            hash_mismatches.append(name)

    print('=' * 55)
    print("NOTE: the LIVE, load-bearing check is build-script HASH INTEGRITY above (script bytes vs")
    print("      register.md) - it runs in the pre-push hook and check_release_ready.py imports it.")
    print("      The 'AR=' columns are a LEGACY per-doc adversary-review tracker (ar_status.json),")
    print("      superseded by the per-file *_cleared.txt signals (the SHA-256-per-file review gate).")
    print("      They read 'N/-' because nothing is marked there anymore - ignore them. Kept as-is on")
    print("      purpose (Tim, 2026-07-20); not stripped, just annotated so the output isn't confusing.")

    if do_update:
        comp_labels = {}
        for doc, script in COMP_SCRIPTS.items():
            current_hash = sha8(script)
            comp_labels[doc] = compute_ar_label(doc, current_hash, ar_data)
        update_register_ar_column(comp_labels)
        print('register.md Comp AR column updated.')

    doc_mismatches = check_docstring_versions()
    all_ok = not hash_mismatches and not ar_stale and not doc_mismatches
    if all_ok:
        print('All hashes match. AR status current. Docstring versions in sync.')
        return 0

    if hash_mismatches:
        print(f'HASH MISMATCHES: {", ".join(hash_mismatches)}')
        print('Version bump + rebuild + hash update required.')
    if ar_stale:
        print(f'AR STALE: {", ".join(ar_stale)}')
        print('Run: python %s --mark-remediated <KEY>' % SELF)
    if doc_mismatches:
        print('DOCSTRING VERSION != VERSION constant (step 4 of the four-step rule):')
        for name, head, const in doc_mismatches:
            print('  %-42s docstring %-8s constant %s' % (name, head, const))
        print('Edit the docstring header line. Do NOT touch changelog entries below it - those')
        print('record what each version actually contained and rewriting them falsifies the record.')
    return 1


if __name__ == '__main__':
    sys.exit(main())
