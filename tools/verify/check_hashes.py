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

import ast
import glob
import hashlib
import io
import subprocess
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



# ---------------------------------------------------------------------------------------------
# THE SHARED BUILD LAYER. Fingerprinted separately because the per-document tokens structurally
# cannot cover it: `register.md` records each build SCRIPT's bytes, and a script's bytes do not
# change when its IMPORT changes. `zp_utils.py` is imported by all 43 build scripts and renders the
# meta line of every document, so editing its `version_line` text altered every rendered PDF while
# this checker exited 0 printing "All hashes match" and `check_release_ready` printed
# "[PASS] Build-script hash integrity". (`RLY3-2`, /rely round 3, pre-existing.)
#
# Re-seed DELIBERATELY with `--seed-shared` after rebuilding what the change affects. That the
# re-seed is manual is the feature: a zp_utils change is precisely the event that should make
# someone think about every document rather than one.
SHARED_BUILD = ['zp_utils.py']
SHARED_BASELINE = os.path.join(HERE, 'shared_build_baseline.txt')


def check_shared_build():
    """Return [(name, recorded, current)] for shared build modules that moved."""
    recorded = {}
    if os.path.exists(SHARED_BASELINE):
        for line in io.open(SHARED_BASELINE, encoding='utf-8'):
            line = line.strip()
            if line and not line.startswith('#'):
                h, _, n = line.partition('  ')
                recorded[n.strip()] = h.strip()
    out = []
    for name in SHARED_BUILD:
        cur = sha8(name)
        was = recorded.get(name)
        if was != cur:
            out.append((name, was or '<UNRECORDED>', cur))
    return out


def seed_shared():
    lines = ['# Fingerprints of the SHARED build layer - modules imported by the build scripts and',
             '# therefore invisible to the per-document tokens in register.md. See RLY3-2.',
             '# Re-seed with: python tools/verify/check_hashes.py --seed-shared']
    for name in SHARED_BUILD:
        lines.append('%s  %s' % (sha8(name), name))
    common.write_text_lf(SHARED_BASELINE, '\n'.join(lines) + '\n')
    print('  seeded %s (%d module(s))' % (os.path.relpath(SHARED_BASELINE, REPO), len(SHARED_BUILD)))


# README rows look like `| [Title](FILE.pdf) | ZP-X | v1.21 | description |`.
_README_ROW = re.compile(r'^\|\s*\[[^\]]*\]\(([^)]+\.pdf[^)]*)\)\s*\|[^|]*\|\s*(v[\d.]+)\s*\|', re.M)
# ⚠ `\.pdf[^)]*` NOT `\.pdf` — an anchored link (`...pdf#page=2`) is a legal, rendering link, and
# requiring `)` immediately after `.pdf` made the whole row invisible. The basename+anchor strip at the
# use site is what turns the tolerated suffix back into a join key.
# register rows: `| ZP-X Title | v1.21 | FILE.pdf | comp | AR | notes |`
_REGISTER_ROW = re.compile(r'^\|\s*([^|]+?)\s*\|\s*(v[\d.]+|N/A)\s*\|\s*([^\s|]+\.pdf)\s*\|', re.M)


def check_readme_versions():
    """README's version column must agree with `register.md`. Returns [(pdf, readme_v, reg_v)].

    ⚠ **THIS OBLIGATION WAS DECIDABLE AND CARRIED BY MEMORY, AND IT FAILED TWICE IN ONE PUSH.**
    `register.md` is the canonical registry and README is required to be verified against it; nothing
    compared them. Measured 2026-08-18: the ZP-R row was corrected in one commit while the ZP-J
    Keystone row went stale in the SAME push, one row away - and this module reported "docstring
    versions in sync" throughout, because it was checking a different pair of records.

    ⚠ **JOINED ON THE PDF FILENAME, NEVER THE `ZP-X` CODE.** Four register rows begin `ZP-J`, so the
    code is ambiguous precisely where the addenda are; the filename is unique and appears in both. The
    prefix trap this avoids corrupted a neighbouring register row earlier in the same arc.

    GUIDE.md is deliberately not compared: measured 2026-08-18, it carries **no** version strings, so
    there is nothing in it that can drift.
    """
    # ⚠ AN UNREADABLE RECORD IS A FINDING, NOT A CLEAN RESULT (`T6`, editorial round 1; DC-10).
    # This returned `[]` on `OSError` — byte-identical to "the two records agree" — so deleting or
    # locking `register.md` silently disarmed the comparison. **The whole point of this check is that
    # two records were compared; if one could not be read, that did not happen.**
    try:
        readme = io.open(os.path.join(REPO, 'README.md'), encoding='utf-8').read()
        reg = io.open(REGISTER, encoding='utf-8').read()
    except OSError as e:
        return [('<unreadable>', 'ERROR', 'could not read README.md or register.md: %s' % e)]
    by_pdf = {}
    for _name, ver, pdf in _REGISTER_ROW.findall(reg):
        by_pdf.setdefault(os.path.basename(pdf.strip()), ver.strip())
    out = []
    parsed = set()
    for pdf, rv in _README_ROW.findall(readme):
        # ⚠ NORMALISE THE LINK. A `./ZP-A_...pdf` prefix parses fine and then joins to NOTHING, so
        # the row silently vanishes from the comparison while still rendering correctly on GitHub
        # (`RLY18-3`). Measured end to end: README `v0.1` against register `v1.21`, link prefixed
        # `./`, gave exit 0 and "README versions in sync".
        pdf = os.path.basename(pdf.strip().split('#')[0])
        parsed.add(pdf)
        reg_v = by_pdf.get(pdf)
        # A README link with no register row is a different defect (check_paths owns dead links);
        # only DISAGREEMENT between two present records is reported here.
        if reg_v and reg_v != 'N/A' and reg_v != rv.strip():
            out.append((pdf, rv.strip(), reg_v))

    # ⚠⚠ THE COVERAGE FLOOR, AND IT IS THE PART THAT MATTERS. A row shape the regex does not match is
    # invisible: it produces no finding and no complaint, so the check reports "in sync" over ground it
    # never walked — the RLY3-2 / RLY5-1 shape one level up, in a checker written to close exactly that.
    # /rely found SIX legal row shapes silently dropped. Chasing each shape is unbounded; asserting that
    # every table row carrying a `.pdf` link was PARSED is finite and cannot be talked past.
    # **NO SILENT TRUNCATION: a row this cannot read is reported, never skipped.**
    for line in readme.splitlines():
        s = line.strip()
        if not s.startswith('|') or '.pdf)' not in s:
            continue
        links = re.findall(r'\]\(([^)]+\.pdf)\)', s)
        if links and not any(os.path.basename(l.split('#')[0]) in parsed for l in links):
            out.append((os.path.basename(links[0].split('#')[0]),
                        'UNPARSED-ROW', 'this row carries a PDF link the comparator could not read'))
    return out


def all_hash_mismatches():
    """Every build input whose recorded hash does not match its bytes. PURE - prints nothing.

    ⚠ **THE FOUR TIERS PLUS THE SHARED LAYER, BECAUSE A SUBSET IS A PROXY** (`RLY5-1`, DC-18).
    `check_release_ready.py` used to iterate `COMP_SCRIPTS` alone and call that "build-script hash
    integrity" - so a stale FORMAL_ONLY script (10 of them), a stale standalone register token (3), or
    a moved `zp_utils.py` all left it printing `[PASS]` and `GO`. Measured: `zp_utils.py` moved alone
    gave `check_hashes.py` exit 1 and the release gate exit 0. **The push hook and CI blocked
    correctly; only the gate whose output is a permanent DOI was blind.**

    Returns a sorted list of human-readable reasons; empty means every recorded hash is current.
    """
    out = []
    registered = parse_register()
    for doc, script in COMP_SCRIPTS.items():
        reg_formal, reg_comp = registered.get(doc, (None, None))
        cur_comp = sha8(script)
        if reg_comp != cur_comp:
            out.append('%s comp: register %s vs script %s' % (doc, reg_comp, cur_comp))
        fscript = FORMAL_SCRIPTS.get(doc + '-formal')
        if fscript:
            cur_formal = sha8(fscript)
            if reg_formal != cur_formal:
                out.append('%s formal: register %s vs script %s' % (doc, reg_formal, cur_formal))
    for name, script in FORMAL_ONLY_SCRIPTS.items():
        cur = sha8(script)
        reg = parse_register_formal_by_name(name)
        if reg is None:
            out.append('%s: no formal: token in register.md' % name)
        elif reg != cur:
            out.append('%s formal: register %s vs script %s' % (name, reg, cur))
    for key, script in STANDALONE_SCRIPTS.items():
        cur = sha8(script)
        reg = register_formal_token(key)
        if reg and reg != cur:
            out.append('%s register token: %s vs script %s' % (key, reg, cur))
    for name, was, cur in check_shared_build():
        out.append('SHARED %s: recorded %s vs current %s (affects EVERY document)' % (name, was, cur))
    # ⚠ THE RELEASE GATE MUST NOT BE THE LAXER SURFACE (`RLY18-5`). These two checks lived only in
    # `main()`, so a README/register disagreement or a stale docstring header gave `check_hashes`
    # exit 1 and the release gate `GO` — the gate whose output is a permanent DOI seeing LESS than the
    # one whose output is an amendable push.
    for pdf, readme_v, reg_v in check_readme_versions():
        out.append('README %s: says %s, register says %s' % (pdf, readme_v, reg_v))
    for entry in check_docstring_versions():
        out.append('docstring version: %s' % (entry,))
    return sorted(out)


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
    """Rewrite the Comp AR column (col 5) in register.md for companion docs.

    ⚠ THIS CARRIED THE PREFIX BUG FIXED IN `d49e95d` FOR THE HASH WRITERS, AND KEPT IT because the
    fix was applied per-function rather than at the property. `doc_cell.startswith(doc)` matched 4
    rows for `ZP-J` and 2 for `ZP-H`. The sharp version is a SINGLE run: the hash writer printed
    "REFUSING to update comp hash for 'ZP-J' - matches 4 rows" and four lines later this stamped all
    four with an adversary-review verdict. One guarded writer beside one unguarded writer is not a
    fixed defect, it is a relocated one. (/rely, 2026-08-18.)

    Exact cell match wins; a prefix is used only when exactly one row carries it; anything else is
    refused and reported, matching `_register_row_pattern`.
    """
    with open(REGISTER, encoding='utf-8') as f:
        lines = f.readlines()

    cells = {}
    for i, line in enumerate(lines):
        if line.startswith('|') and len(line.split('|')) >= 8:
            cells[i] = line.split('|')[1].strip()

    targets = {}
    for doc in ar_labels:
        exact = [i for i, c in cells.items() if c == doc]
        rows = exact or [i for i, c in cells.items() if c.startswith(doc)]
        if len(rows) == 1:
            targets[rows[0]] = ar_labels[doc]
        elif len(rows) > 1:
            print('  REFUSING to update AR column for %r - matches %d rows: %s'
                  % (doc, len(rows), ', '.join(cells[i] for i in rows)))
        else:
            print('  REFUSING to update AR column for %r - no register row matched' % doc)

    updated = []
    for i, line in enumerate(lines):
        if i in targets:
            parts = line.split('|')
            parts[5] = f' {targets[i]} '
            line = '|'.join(parts)
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
        # ⚠ CHECK THE WRITER'S RETURN. This branch used to ignore it, so `--mark-remediated ZP-J`
        # printed "Marked ZP-J: Y/Y" and "register.md updated" after BOTH writers refused an
        # ambiguous prefix - exit 0, empty diff, a claim of work not done. The FORMAL branch below
        # already checked. (`/rely` round 3.)
        if not update_register_comp_hash(key, current_hash):
            print('  NOT marked %s: the register write was refused (see above)' % key)
            return None
        ar_data[key] = {'hash': current_hash, 'status': status}
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

    # ⚠ 10 OF 39 VALID KEYS HAD NO BRANCH HERE AT ALL (`RLY4-5`). Every FORMAL_ONLY document - ZP-N,
    # ZP-P, ZP-Q, ZP-R and the addenda - fell through to "unknown key", which is why three register
    # rows had to be hand-edited this round. `parse_mark_args` also upper-cased them into
    # nonexistence; it preserves case for standalone keys and now for these.
    if key in FORMAL_ONLY_SCRIPTS:
        script = FORMAL_ONLY_SCRIPTS[key]
        current_hash = sha8(script)
        if current_hash == 'MISSING':
            print(f'  ERROR: {script} not found — cannot mark {key}')
            return None
        if not update_register_formal_hash(key, current_hash):
            print('  NOT marked %s: the register write was refused (see above)' % key)
            return None
        ar_data[key] = {'hash': current_hash, 'status': status}
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
                    # ⚠ MATCH THE MULTI-WORD MAPS BEFORE UPPER-CASING, OR THE BRANCH CANNOT BE
                    # REACHED. `mark_doc` grew a FORMAL_ONLY branch and this function still
                    # upper-cased, so 0 of 10 keys arrived: `--mark-remediated "ZP-Q The
                    # Frame-Change"` returned `unknown key "ZP-Q THE FRAME-CHANGE"` - printing the
                    # correct key one column from the mangled one. A fix behind a locked door is not
                    # a fix. (`RLY4-6`, /rely rounds 4 and 5.)
                    named = next(
                        (k for k in list(STANDALONE_SCRIPTS) + list(FORMAL_ONLY_SCRIPTS)
                         if k.lower() == key.lower()), None)
                    key = named if named else key.upper()
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


    # ---- THE OTHER TWO DETECTORS IN THIS MODULE -------------------------------------------------
    # ⚠ BOTH SHIPPED WITH NO CONTROLS, AND BOTH THEN FAILED OPEN OVER GROUND THEY NEVER WALKED.
    # Neutering `_HEADER_SHAPES` used to leave this selftest reporting PASS exit 0 while
    # check_checkers printed "every audited gate has passing controls in both directions" - a
    # module-level audit cannot see a second detector inside the module, which is how HASH-1 and the
    # `(vN, revised ...)` shape both survived. (/rely, 2026-08-18.)
    print('  MUST FIRE  (docstring-version detector)')
    for head, want, why in (
            ('"""Build ZP-A: Lattice Algebra (v1.21)\n"""', '1.21', 'paren shape'),
            ('"""Foreword (v2.14, revised July 2026)\n"""', '2.14', 'paren-comma shape'),
            ('"""Build ZP-C\n\nVersion 1.4 | July 2026\n"""', '1.4', 'pipe shape'),
            ('"""ZP-I\n\nVersion 1.15 | July\n\nv1.10: refs "(v1.1)" removed\n"""',
             '1.15', 'header beats a changelog line below it')):
        got = _header_version(head)
        ok = got == want
        bad += 0 if ok else 1
        print('    %-34s %s (%r)' % (why, 'ok' if ok else '*** WRONG ***', got))

    print('  MUST SUPPRESS  (docstring-version detector)')
    for head, why in (
            ('"""Build something with no version anywhere\n"""', 'no version is not a version'),
            ('"""ZP-X\n\nv1.10: version refs "(v1.1)" removed from body prose\n"""',
             'a changelog line alone is NOT a header')):
        got = _header_version(head)
        ok = got is None
        bad += 0 if ok else 1
        print('    %-34s %s (%r)' % (why, 'ok' if ok else '*** WRONG ***', got))

    # The --sync-hash laundering guard. Rendered text lives in `body()` string literals, which are
    # CODE, so an edit there must be visible; comments and docstrings must not be.
    _base = ('"""ZP-X\n\nVersion 1.0 | July\n"""\n'
             'VERSION = "1.0"\n'
             'def body(sp):\n'
             '    sp("the monotone regime is free of it literally")\n')
    _prose = ('"""ZP-X\n\nVersion 1.0 | July\n\nv1.0: initial\n"""\n'
              'VERSION = "1.0"\n'
              'def body(sp):\n'
              '    # a new comment, changing nothing rendered\n'
              '    sp("the monotone regime is free of it literally")\n')
    _rendered = ('"""ZP-X\n\nVersion 1.0 | July\n"""\n'
                 'VERSION = "1.0"\n'
                 'def body(sp):\n'
                 '    sp("free of it LITERALLY, on a complete lattice")\n')

    print('  MUST FIRE  (--sync-hash laundering guard)')
    for a, b, why in ((_base, _rendered, 'an edit to RENDERED text is refused'),
                      (_base, 'def body(:\n', 'an unparsable side vouches for nothing')):
        got = _code_identical_ignoring_prose(a, b)
        ok = got is not True
        bad += 0 if ok else 1
        print('    %-34s %s (%r)' % (why, 'ok' if ok else '*** WRONG ***', got))

    print('  MUST SUPPRESS  (--sync-hash laundering guard)')
    for a, b, why in ((_base, _prose, 'a comment/docstring edit is allowed'),
                      (_base, _base, 'an identical script is allowed')):
        got = _code_identical_ignoring_prose(a, b)
        ok = got is True
        bad += 0 if ok else 1
        print('    %-34s %s (%r)' % (why, 'ok' if ok else '*** WRONG ***', got))


    # ⚠ TWO MORE DETECTORS IN THIS MODULE HAD NO CONTROLS (`/rely` round 3, after round 2 found the
    # first two). Neutering `_register_row_pattern` back to the exact `d49e95d` prefix bug, or
    # `compute_ar_label`'s STALE branch, both left `--selftest` PASS exit 0. The module keeps
    # growing detectors and the audit is per-MODULE, so each new one is invisible until controlled.
    print('  MUST FIRE  (register row matcher)')
    _reg = io.open(REGISTER, encoding='utf-8').read()
    for doc, why in (('ZP-J', 'an ambiguous prefix refuses'), ('ZP-H', 'an ambiguous prefix refuses')):
        got = _register_row_pattern(doc, _reg, 'control')
        ok = got is None
        bad += 0 if ok else 1
        print('    %-34s %s' % ('%s: %s' % (doc, why), 'ok' if ok else '*** WRONG ***'))

    print('  MUST SUPPRESS  (register row matcher)')
    _uniq = next((d for d in FORMAL_ONLY_SCRIPTS
                  if _register_row_pattern(d, _reg, 'control') is not None), None)
    ok = _uniq is not None
    bad += 0 if ok else 1
    print('    %-34s %s (%s)' % ('an unambiguous name still matches',
                                 'ok' if ok else '*** WRONG ***', _uniq))

    print('  MUST FIRE  (AR staleness)')
    _probe = {'k': {'hash': 'deadbeef', 'status': 'remediated'}}
    got = compute_ar_label('k', 'cafef00d', _probe)
    ok = 'STALE' in str(got).upper() or got != AR_DISPLAY['remediated']
    bad += 0 if ok else 1
    print('    %-34s %s (%r)' % ('a moved hash is not still Y/Y', 'ok' if ok else '*** WRONG ***', got))


    # ⚠⚠ `sha8` IS THIS MODULE'S PRIMARY DETECTOR AND HAD NO CONTROL (`RLY4-2`, /rely round 4).
    # Replacing it with a `register.md` lookup left `--selftest` at exit 0 and the run reporting
    # "All hashes match" on a genuinely modified script. The old must-suppress hashed the same file
    # TWICE - which a lookup table and a constant both satisfy. A control must distinguish the
    # function from its impostors, not merely observe that it is deterministic.
    print('  MUST FIRE  (sha8 is a real content hash)')
    # ⚠⚠ CALL `sha8` (not `hashlib`) AND WRITE NOTHING INTO `scripts/`. THESE ARE BOTH ACHIEVABLE,
    # AND TREATING THEM AS A TRADEOFF WAS THE ERROR — twice, in opposite directions:
    #   * the first version wrote `_sha8_control_probe.py` into `scripts/`, so a killed run left an
    #     untracked file in a tracked directory (the `ZZTestOrd.lean` shape already in this project's
    #     permanent history);
    #   * the "fix" moved it to a tempdir and computed the hashes with `hashlib` directly, which
    #     silently changed the SUBJECT — instrumented calls to `sha8` in this block reached ZERO, so a
    #     CACHING `sha8` passed the whole selftest (`ORD-6-1`).
    # `sha8` resolves against the module-level `SCRIPT_DIR`, so REDIRECTING that for the duration
    # makes the real call land in the tempdir. The subject is `sha8`; the repo is never written to.
    # **A control's subject is what it CALLS — relocating a probe is exactly the edit that quietly
    # changes it.** (/rely round 5 and the re-signature; the false dilemma was named by the gate.)
    # (assigned through `globals()` rather than `global`, which must precede every use of the name
    # in the function and `SCRIPT_DIR` is read above — same form already used for `SHARED_BUILD`.)
    import tempfile as _tf
    _saved_dir = globals()['SCRIPT_DIR']
    with _tf.TemporaryDirectory() as _d:
        try:
            globals()['SCRIPT_DIR'] = _d
            io.open(os.path.join(_d, 'probe.py'), 'w', encoding='utf-8', newline='\n').write('X = 1\n')
            h1 = sha8('probe.py')
            io.open(os.path.join(_d, 'probe.py'), 'w', encoding='utf-8', newline='\n').write('X = 2\n')
            h2 = sha8('probe.py')
            # `sha8` must also report MISSING rather than raising on an absent name.
            h_missing = sha8('no_such_probe_at_all.py')
        finally:
            globals()['SCRIPT_DIR'] = _saved_dir
    ok = h_missing == 'MISSING'
    bad += 0 if ok else 1
    print('    %-34s %s (%r)' % ('an absent script reports MISSING',
                                 'ok' if ok else '*** WRONG ***', h_missing))
    # and sha8 itself must agree with that contract on a REAL tracked script
    _real = COMP_SCRIPTS['ZP-A']
    _direct = hashlib.sha256(
        io.open(os.path.join(SCRIPT_DIR, _real), 'rb').read()).hexdigest()[:8]
    ok = sha8(_real) == _direct
    bad += 0 if ok else 1
    print('    %-34s %s (%s)' % ('sha8 IS sha256-of-bytes on disk',
                                 'ok' if ok else '*** WRONG ***', _direct))
    ok = h1 != h2 and 'MISSING' not in (h1, h2) and len(h1) == 8
    bad += 0 if ok else 1
    print('    %-34s %s (%s vs %s)' % ('changed CONTENT changes the hash',
                                       'ok' if ok else '*** WRONG ***', h1, h2))
    # and it must be the real SHA-256 of those bytes, not any stable function of them
    expect = hashlib.sha256(b'X = 2\n').hexdigest()[:8]
    ok = h2 == expect
    bad += 0 if ok else 1
    print('    %-34s %s (%s, expected %s)' % ('and it is SHA-256 of the bytes',
                                              'ok' if ok else '*** WRONG ***', h2, expect))

    print('  MUST FIRE  (shared build layer)')
    _saved = globals().get('SHARED_BUILD')
    try:
        globals()['SHARED_BUILD'] = ['_no_such_shared_module.py']
        ok = bool(check_shared_build())
    finally:
        globals()['SHARED_BUILD'] = _saved
    bad += 0 if ok else 1
    print('    %-34s %s' % ('an unrecorded module is reported', 'ok' if ok else '*** WRONG ***'))


    # ⚠ `all_hash_mismatches()` IS A SECOND READER OF THE SAME PROPERTY, so it must agree with the
    # display loops in `main()` - which /rely verified cover all four tiers plus the shared layer.
    # Two readers that can disagree is how `check_release_ready.py` drifted into checking a SUBSET
    # and calling it integrity (`RLY5-1`). This control is the thing that makes the delegation safe.
    print('  MUST SUPPRESS  (full-coverage mismatch scan)')
    _m = all_hash_mismatches()
    # ⚠ `isinstance(_m, list)` alone is satisfied by `return []` — it asserts a TYPE, not a scan.
    # The MUST FIRE block below is what establishes coverage; this only pins the shape and the
    # clean-tree expectation. (`RLY18-1`.)
    ok = isinstance(_m, list) and all(isinstance(x, str) for x in _m)
    bad += 0 if ok else 1
    print('    %-34s %s (%d mismatch(es) on this tree)'
          % ('scans without raising', 'ok' if ok else '*** WRONG ***', len(_m)))
    # ⚠⚠ THIS CONTROL MUST *CALL* `all_hash_mismatches()`, AND THE FIRST VERSION DID NOT (`RLY18-1`).
    # It checked `key in mapping and sha8(...) != 'MISSING'` — map membership, which is true of a
    # function that scans nothing. /rely restored the exact `RLY5-1` defect (COMP-only) and `--selftest`
    # returned PASS, exit 0. **THIRD TIME IN ONE ARC that a control's SUBJECT was wrong** — after
    # `ORD-6-1` (hashlib in place of `sha8`) and the README control's hard-coded baseline. Each read
    # plausibly; none tested what it named.
    #
    # The real control perturbs a COPY of one script per tier, with `SCRIPT_DIR` redirected at a
    # tempdir (the `sha8` pattern), and requires the function itself to name that tier. Drop a tier
    # from the scan and its case fails.
    print('  MUST FIRE  (every tier is reachable — via the real function)')
    import shutil as _sh
    import tempfile as _tf2
    _tiers = [('COMP', COMP_SCRIPTS['ZP-A']),
              ('FORMAL', FORMAL_SCRIPTS['ZP-A-formal']),
              ('FORMAL_ONLY', FORMAL_ONLY_SCRIPTS['ZP-Q The Frame-Change']),
              ('STANDALONE', STANDALONE_SCRIPTS['Foreword']),
              ('SHARED', SHARED_BUILD[0])]
    _saved_sd = globals()['SCRIPT_DIR']
    with _tf2.TemporaryDirectory() as _sd:
        try:
            for _f in os.listdir(_saved_sd):
                if _f.endswith('.py'):
                    _sh.copyfile(os.path.join(_saved_sd, _f), os.path.join(_sd, _f))
            globals()['SCRIPT_DIR'] = _sd
            # unperturbed copies must be quiet, or every case below is meaningless
            _base = all_hash_mismatches()
            ok = _base == []
            bad += 0 if ok else 1
            print('    %-34s %s%s' % ('untouched copies are quiet', 'ok' if ok else '*** WRONG ***',
                                      '' if ok else ' — %s' % (_base[:2],)))
            for _label, _script in _tiers:
                _p = os.path.join(_sd, _script)
                _orig = io.open(_p, 'rb').read()
                try:
                    io.open(_p, 'wb').write(_orig + b'\n# perturbation\n')
                    _hits = all_hash_mismatches()
                finally:
                    io.open(_p, 'wb').write(_orig)
                _seen = len(_hits) > len(_base)
                bad += 0 if _seen else 1
                print('    %-34s %s' % ('%s tier is actually scanned' % _label,
                                        'ok' if _seen else '*** NOT SCANNED ***'))
        finally:
            globals()['SCRIPT_DIR'] = _saved_sd


    # ⚠ THE TWO-RECORD COMPARATOR (README vs register.md). Editorial rated this above the claim sweep
    # because it is DECIDABLE, and this arc is why: README's ZP-R row was fixed in one commit while its
    # ZP-J Keystone row went stale in the SAME push, one row away, with this module reporting
    # "docstring versions in sync" the whole time - a true statement about a different pair of records.
    print('  MUST SUPPRESS  (README vs register)')
    _before = check_readme_versions()
    ok = _before == []
    bad += 0 if ok else 1
    print('    %-34s %s%s' % ('the real tables agree', 'ok' if ok else '*** DRIFT ***',
                              '' if ok else ' — %s' % (_before,)))

    print('  MUST FIRE  (README vs register)')
    _rm = io.open(os.path.join(REPO, 'README.md'), encoding='utf-8').read()
    _hit = _README_ROW.search(_rm)
    if _hit:
        _broken = _rm[:_hit.start(2)] + 'v0.1' + _rm[_hit.end(2):]
        _saved = globals()['_README_ROW']
        import types as _types
        # Re-run the comparison against a PERTURBED copy without touching the file on disk.
        _orig_open = io.open

        def _fake_open(p, *a, **k):
            if str(p).endswith('README.md'):
                import io as _io
                return _io.StringIO(_broken)
            return _orig_open(p, *a, **k)
        io.open = _fake_open
        try:
            drift = check_readme_versions()
        finally:
            io.open = _orig_open
        # ⚠ COMPARE AGAINST THE BASELINE, DO NOT HARD-CODE IT. The first version asserted
        # `len(drift) == 1`, which silently assumed the real tables already agreed - and on the very
        # run that added this check they did NOT (two live drifts, one of them pre-existing). A
        # control pinned to the world's current state fails the moment the world is the thing you are
        # measuring.
        ok = any(d[1] == 'v0.1' for d in drift) and len(drift) == len(_before) + 1
        bad += 0 if ok else 1
        print('    %-34s %s (+%d over baseline %d)'
              % ('a wrong README version is caught', 'ok' if ok else '*** WRONG ***',
                 len(drift) - len(_before), len(_before)))
    else:
        bad += 1
        print('    %-34s *** NO README ROWS PARSED ***' % 'the row pattern matches')

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
    # ⚠ A THIRD SHAPE, and the fix for the second shipped without it: `build_foreword.py`
    # writes `(v2.14, revised July 2026)` - a COMMA where this pattern demanded `)`. Planted
    # staleness there was SILENT while the identical plant in build_zpa/zpe/zpi was CAUGHT
    # (/rely, 2026-08-18).
    re.compile(r"\(v(\d+(?:\.\d+)*)\s*[,)]"),                   # `(v1.21)` and `(v2.14, revised ...)`
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


# How far back the attestation walk looks. Exhaustion is REPORTED, never silently treated as
# "not found" - see `_register_attested_source`.
_ATTEST_WALK = 400


def _strip_docstrings(tree):
    """Remove every docstring node, in place. Comments are absent from an AST already."""
    for node in ast.walk(tree):
        body = getattr(node, 'body', None)
        if not isinstance(body, list) or not body:
            continue
        if not isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        first = body[0]
        if (isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant)
                and isinstance(first.value.value, str)):
            del body[0]
    return tree


def _code_identical_ignoring_prose(a, b):
    """Do two versions of a script differ ONLY in comments and docstrings? Takes BYTES.

    Exact, not heuristic. Comments never reach an AST, docstrings are stripped, and everything a
    build script RENDERS lives in ordinary string literals inside `body()` / `cbody()` - which are
    code, so any edit reaching rendered text shows up here. Returns None when either side will not
    parse, and the caller treats that as "cannot vouch".

    ⚠⚠ **BYTES, NOT STR, AND THE FIRST VERSION TOOK STR** (`RLY3-1`, `/rely` round 3). `ast.parse`
    on a **str** ignores the PEP 263 encoding cookie BY DESIGN. So inserting
    `# -*- coding: latin-1 -*-` as line 1 - a COMMENT, invisible to any AST - changed **40 of 179**
    string constants in `build_foreword.py`, every em-dash and arrow becoming mojibake, and the guard
    ALLOWED it: exit 0, `status preserved as 'remediated'`, `hash=MISMATCH AR=STALE` turned into
    `hash=OK AR=Y/Y`. Parsing bytes honours the cookie and returns False. **A comment that changes how
    every literal in the file is decoded is exactly the case "comments cannot affect rendering"
    misses.**"""
    try:
        ta, tb = ast.parse(a), ast.parse(b)
    except (SyntaxError, ValueError):
        return None
    return ast.dump(_strip_docstrings(ta)) == ast.dump(_strip_docstrings(tb))


def _register_attested_source(script, recorded_hash):
    """The last committed content of `script` that the recorded token actually attests to.

    ⚠ COMPARING AGAINST HEAD WOULD BE A HOLE, and it is the obvious implementation. Commit a
    rendered change, then `--sync-hash`: HEAD and the working tree agree, the diff is empty, and the
    laundering sails through. The honest reference is the last state the REGISTER was correct about,
    so this walks history for the blob whose short hash equals the recorded token.
    """
    rel = 'scripts/' + script
    try:
        revs = subprocess.run(['git', 'log', '--format=%H', '--follow',
                               '-%d' % _ATTEST_WALK, '--', rel],
                              cwd=REPO, capture_output=True, text=True, timeout=60)
        # ⚠ A `git log` that FAILS without raising used to fall through to exhausted=False and print
        # "no committed version hashes to the recorded X" - fails closed, but for a false reason, and
        # a wrong reason sends the reader to look for the wrong thing. (`RLY4-7`.)
        if revs.returncode != 0:
            return None, True
        for rev in revs.stdout.split():
            blob = subprocess.run(['git', 'show', '%s:%s' % (rev, rel)],
                                  cwd=REPO, capture_output=True, timeout=60)
            if blob.returncode != 0:
                continue
            if hashlib.sha256(blob.stdout).hexdigest()[:8] == recorded_hash:
                return blob.stdout, False   # BYTES - see _code_identical_ignoring_prose (RLY3-1)
    except (OSError, subprocess.SubprocessError):
        return None, False
    # ⚠ DISTINGUISH "not found" FROM "ran out of history". The walk is bounded, and without this a
    # blob sitting beyond the limit produced "no committed version hashes to the recorded X" - a
    # FALSE statement, not a conservative one. measured: the deepest history is build_zpe.py at 57 commits, so 400 is ample.
    return None, len(revs.stdout.split()) >= _ATTEST_WALK


def _recorded_token(key):
    """The hash `register.md` (or `ar_status.json`) currently records for `key`, or None.

    ⚠ **MY OWN BUG, AND IT MADE THE GUARD UNREACHABLE** (`/rely` round 3). The first version called
    `parse_register().get(key).get('comp')` - but `parse_register` returns **tuples**, so every one
    of the 13 companion keys raised `AttributeError`, and the 23 formal keys fell to
    `register_formal_token`, which knows only the three STANDALONE labels and so refused them all
    with a FALSE reason. The guard was operable on **3 of 39 keys** and had therefore never once run
    against a register token. It failed closed, which is why nothing noticed.
    """
    if key in STANDALONE_SCRIPTS:
        return load_ar_status().get(key, {}).get('hash') or register_formal_token(key)
    if key in COMP_SCRIPTS:
        row = parse_register().get(key)
        return row[1] if row else None          # (formal, comp)
    if key in FORMAL_SCRIPTS:
        row = parse_register().get(key.replace('-formal', ''))
        return row[0] if row else None
    if key in FORMAL_ONLY_SCRIPTS:
        return parse_register_formal_by_name(key)
    return None


def _refuses_as_laundering(key, script, recorded_hash):
    """Would `--sync-hash` here skip a re-review the four-step rule owes?

    FAILS CLOSED. No attested source, unparsable either side, or any code-level difference all
    refuse; only a provably prose-only edit is allowed through. Returns the reason, or None to allow.
    """
    if not recorded_hash:
        return 'the register records no hash to compare against'
    path = os.path.join(REPO, 'scripts', script)
    if not os.path.exists(path):
        return 'the script is missing'
    was, exhausted = _register_attested_source(script, recorded_hash)
    if was is None:
        if exhausted:
            return ('the attestation walk reached its %d-commit limit for %s without finding the '
                    'recorded %s - this is a LIMIT, not evidence the blob is absent'
                    % (_ATTEST_WALK, script, recorded_hash))
        return ('no committed version of %s hashes to the recorded %s, so what the register last '
                'attested to cannot be established' % (script, recorded_hash))
    verdict = _code_identical_ignoring_prose(was, io.open(path, 'rb').read())
    if verdict is None:
        return 'the script does not parse on one side, so the change cannot be characterised'
    if verdict is False:
        return ('the change reaches CODE, not only comments and docstrings - rendered output may '
                'have moved, so a rebuild and a re-review are owed')
    return None


def sync_hash(key):
    """Update `key`'s register hash token ONLY. Does not touch AR status.

    For the case the four-step rule does not cover: a script edited in a way that changes no
    RENDERED output - a docstring header, a comment - so the PDF is unchanged, the version already
    describes it, and no re-review is owed. `--mark-remediated` would stamp AR as
    reviewed-and-remediated, which would be a claim about work nobody did.

    Routes through the same script maps and the same boundary-aware row matcher as everything else
    here, so it cannot write a row the caller did not name.

    ⚠ **GUARDED, after `/rely` demonstrated the laundering the previous docstring merely described.**
    A prose MISUSE BOUNDARY is not a control. `_refuses_as_laundering` compares the working script
    against the last COMMITTED content the register's own token attests to, and allows the write only
    when the two are identical modulo comments and docstrings - so any change reaching a rendered
    string literal is refused. It fails closed on every uncertainty.
    """
    _script = (FORMAL_SCRIPTS.get(key) or COMP_SCRIPTS.get(key)
               or FORMAL_ONLY_SCRIPTS.get(key) or STANDALONE_SCRIPTS.get(key))
    if _script:
        _why = _refuses_as_laundering(key, _script, _recorded_token(key))
        if _why:
            print('  REFUSING --sync-hash for %r: %s.' % (key, _why))
            print('    --sync-hash is ONLY for a script edit that changes no rendered output.')
            print('    After a real render change: bump VERSION, rebuild, then --mark-remediated')
            print('    once the review has actually run.')
            return False

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
    if key in FORMAL_ONLY_SCRIPTS:
        # ⚠ A FOURTH MAP EXISTS AND THE FIRST VERSION OF THIS FUNCTION WALKED THREE. `--sync-hash
        # "ZP-R Cross-Category"` returned "unknown key" while the document sat mismatched - a tool
        # reporting nothing over ground it never covered, which is the shape this layer exists to
        # refuse. Found by using it, one commit after adding it.
        h = sha8(FORMAL_ONLY_SCRIPTS[key])
        if h == 'MISSING':
            print('  ERROR: %s not found' % FORMAL_ONLY_SCRIPTS[key])
            return False
        ok = update_register_formal_hash(key, h)
        print('  %-26s formal:%s  %s' % (key, h, 'written' if ok else 'REFUSED'))
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
    if '--seed-shared' in args:
        seed_shared()
        return 0
    if '--selftest' in args:
        print('ZP Build Script Hash Check - CONTROLS')
        print('=' * 55)
        return selftest()
    do_update = '--update-register' in args
    marks     = parse_mark_args(args)

    ar_data = load_ar_status()

    if marks:
        # ⚠ COUNT THE FAILURES. This returned 0 unconditionally, so
        # `--mark-remediated "ZP-Q The Frame-Change"` printed `ERROR: unknown key`, then
        # "register.md updated", then exited 0 - three statements, two of them false. (`RLY4-5`.)
        marked, failed = 0, []
        for key, status in marks:
            recorded_hash = mark_doc(key, status, ar_data)
            if recorded_hash:
                marked += 1
                label = AR_DISPLAY[status]
                print(f'  Marked {key}: {label}  (hash: {recorded_hash})')
            else:
                failed.append(key)
        # ⚠ ONLY PERSIST IF SOMETHING WAS MARKED. This ran unconditionally, so a FAILED mark wrote
        # `{}` over ar_status.json, flipped `AR_AVAILABLE`, and made the next plain run report three
        # false MISMATCHes (Foreword, PhilQ, Tools) on an UNMODIFIED tree - re-creating the exact
        # false positives fixed on 2026-08-15. It compounded with `RLY4-6` above: the natural trigger
        # was the very command that fix was meant to enable. (/rely round 5.)
        if marked:
            save_ar_status(ar_data)
        # Recompute Comp AR column for register.md (companions only).
        # ⚠ ONLY WHEN SOMETHING WAS ACTUALLY MARKED — same class as the `save_ar_status` guard above.
        # A wholly failed `--mark` used to reach here and rewrite the column from unchanged state,
        # printing two REFUSING lines that read as errors caused by the mark rather than as a guard
        # firing on an unrelated ambiguous prefix.
        comp_labels = {}
        if marked:
            for doc, script in COMP_SCRIPTS.items():
                current_hash = sha8(script)
                comp_labels[doc] = compute_ar_label(doc, current_hash, ar_data)
            update_register_ar_column(comp_labels)
        if marked:
            print('  ar_status.json and register.md updated.')
        if failed:
            print('  NOT marked (%d): %s' % (len(failed), ', '.join(failed)))
        if not do_update:
            return 1 if failed else 0

    # Full validation pass
    registered = parse_register()
    ar_data    = load_ar_status()

    hash_mismatches = []
    ar_stale        = []

    print('ZP Build Script Hash + AR Status Check')
    print('=' * 55)
    shared_moved = check_shared_build()

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

        # ⚠ SAY WHEN THE ONLY WITNESS IS PRIVATE. With no `formal:` token in `register.md`, `hash=OK`
        # here rests entirely on the gitignored `ar_status.json` — so a PUBLISHED document with no
        # public provenance printed a green line indistinguishable from a fully-guarded one. Measured
        # by the editorial gate: `ZP_Tools_and_Methods.pdf` is published and linked twice from GUIDE,
        # has no register row and no `VERSION` in its build script, and still read `Tools: hash=OK`.
        # The absent-tracker branch above already said this; the ordinary branch did not.
        _public = '' if reg_tok else '  (no register token — private tracker only)'
        print(f'  {key}: hash={hash_status}  AR={ar_label}{_public}')

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

    # ⚠⚠ REPORT BEFORE THE EARLY RETURN, AND COUNT IT IN `all_ok`. Both were wrong on first write
    # (`RLY4-1`, /rely round 4): `shared_moved` was computed, excluded from `all_ok`, and printed
    # AFTER `return 0` - so a shared-layer change alone exited 0 in silence, and the block spoke only
    # when some OTHER check had already failed. That is the SAME SHAPE as `RLY3-2`, the hole it was
    # written to close: RLY3-2 reported a clean zero over ground it never walked; this walked the
    # ground, saw the problem, and returned zero anyway.
    if shared_moved:
        print()
        print('  SHARED BUILD LAYER CHANGED - this affects EVERY rendered document, and the')
        print('  per-document fingerprints in register.md cannot see it (RLY3-2):')
        for name, was, cur in shared_moved:
            print('    %-22s registered: %-10s current: %s' % (name, was, cur))
        print('  Rebuild what it affects, then: python %s --seed-shared' % SELF)

    doc_mismatches = check_docstring_versions()
    readme_drift = check_readme_versions()
    if readme_drift:
        print()
        print('  README DISAGREES WITH register.md, which is the canonical registry:')
        for pdf, rv, gv in readme_drift:
            print('    %-44s README %-8s register %s' % (pdf, rv, gv))
        print('  Update register.md FIRST, then propagate to README (and GUIDE if it ever carries one).')
    all_ok = (not hash_mismatches and not ar_stale and not doc_mismatches
              and not shared_moved and not readme_drift)
    if all_ok:
        print('All hashes match. AR status current. Docstring and README versions in sync.')
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
