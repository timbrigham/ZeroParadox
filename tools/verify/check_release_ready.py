"""
check_release_ready.py - ZP pre-release readiness gate.

Run from the repo ROOT, BEFORE drafting a release body / cutting a tag:

    python check_release_ready.py <tag>      e.g.  v2.7

Exit 0 = all BLOCKING (mechanical) checks pass -> GO, pending the printed
          judgment checklist (editorial/adversary/etc., which a script cannot decide).
Exit 1 = one or more blocking checks failed -> NO-GO.
Exit 2 = usage error.

Design: the deterministic checks are auto-verified and split into
  [FAIL]  blocking, high-confidence, unambiguous;
  [WARN]  best-effort / fragile-to-parse / hygiene -> surfaced, not blocking;
  [INFO]  context.
The judgment items (gates run, companion sync, version-bump decision, release
body approved) are PRINTED for the human to confirm - they are not mechanizable.

Spec + rationale: .claude-local/notes/release_readiness_gate_2026-06-24.md
Reuses check_hashes.py for register parsing + script hashes.
"""

import json
import os
import re
import subprocess
import sys
import glob

# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3), coerced to
# `str` because this module speaks `os.path`.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
# ⚠ THE ONE REMAINING CHECKER-IMPORTS-A-CHECKER EDGE, AND IT IS DELIBERATE. This is the RELEASE
# gate re-running the HASH gate's own parser rather than a second copy of it: `check_hashes` owns
# `register.md`'s format, and the alternative is two parsers for one file, which is the mirror
# defect this bundle spent its length removing. It is a gate composing a gate, not a checker
# borrowing a peer's text utilities — which is what MIG-3 objected to.
import check_hashes as ch  # noqa: E402  (sha8, parse_register, *_SCRIPTS dicts)

HERE = str(common.HERE)
REPO = str(common.REPO)
SELF = common.self_rel(__file__)

REGISTER = 'register.md'
RELEASES = 'RELEASES.md'
REGISTRY = 'LEAN_CUSTOM_REGISTRY.md'
ZENODO = '.zenodo.json'
README = 'README.md'
GUIDE = 'GUIDE.md'
LEAN_GLOB = 'ZeroParadox/**/*.lean'
LOCAL = os.path.join(REPO, '.claude-local')   # signals only; per-push state, still private

fails = []
warns = []


def fail(msg):
    fails.append(msg)


def warn(msg):
    warns.append(msg)


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


def git(*args):
    r = subprocess.run(['git', *args], capture_output=True, text=True)
    return r.stdout


def norm_ver(v):
    return (v or '').strip().lstrip('vV').strip()


# --------------------------------------------------------------------------- checks

# Files that legitimately carry NO Engineer's Take (permanent). Basenames.
# Rationale: the Engineer's Take convention covers ZP-X *framework* layers; vendored/ported
# infrastructure and dev tooling are not ZP-original content and carry none by design.
TAKE_EXEMPT = {
    'Basic.lean',           # removed in v3.0 reorg (kept for back-compat)
    'NaturalOps.lean',      # verbatim VENDORED from Mathlib (Violeta Hernandez) - not ZP content
    'NaturalOpsPow.lean',   # PORTS Violeta Hernandez's CGT proof (Apache-2.0) - not ZP-original
    'ExtractDeps.lean',     # dev tooling (Meta/, "not framework content" per MANIFEST)
    'Snapshot.lean',        # dev tooling (Meta/, axiom-footprint snapshot generator)
}
# Files that OWE a take but are explicitly deferred — backlog, NOT exempt. Tolerated
# as a non-blocking WARN, never a silent pass. Burn this down; do NOT add new files
# here — every new ZP-X Lean file must ship a filled take from creation.
# See .claude-local/notes/deferred_engineers_takes_2026-06-26.md
DEFERRED_TAKES = {
    'ZPB_PadicTree.lean',
    'ZPJ_AczelConn.lean',
    'ZPJ_Scale.lean',
    'ZPJ_SelfApp.lean',
    'ZPJ_WheelFrac.lean',
}


def c_engineers_takes():
    """Every ZP-X Lean file carries a filled Engineer's Take.

    Fails on a MISSING section, not only an empty or TODO-flagged one. The
    DEFERRED_TAKES backlog is tolerated as a WARN (owed, not exempt); TAKE_EXEMPT
    files are skipped. The heading match allows both the '## Engineer's Take'
    markdown form and the bare 'Engineer's Take:' form (ZPM).
    """
    hits = []
    # heading + body up to the next markdown heading or EOF; '#' is optional so the
    # bare 'Engineer's Take:' form is recognised too.
    take_re = r'((?:#+\s*)?Engineer.?s Take[^\n]*)\n(.*?)(?=\n#+\s|\Z)'
    for path in glob.glob(LEAN_GLOB, recursive=True):
        norm = path.replace('\\', '/')
        if '.lake' in norm:
            continue
        base = os.path.basename(norm)
        if base in TAKE_EXEMPT:
            continue
        txt = read(path)
        for pat in ('TODO (Tim)', 'TODO: Engineer'):
            if pat in txt:
                hits.append(f'{path}: contains "{pat}"')
        if not re.search(r'Engineer.?s Take', txt, re.I):
            # no section at all
            if base in DEFERRED_TAKES:
                warn(f"Engineer's Take deferred (owed, not exempt) - {path}")
            else:
                hits.append(f'{path}: no "Engineer\'s Take" section')
            continue
        for m in re.finditer(take_re, txt, re.S | re.I):
            body = re.sub(r'(?m)^\s*--.*$', '', m.group(2)).strip()
            if not body:
                hits.append(f'{path}: empty "{m.group(1).strip()}" section')
    if hits:
        for h in hits:
            fail(f'Engineer\'s Take unfilled - {h}')
    return not hits


def c_hash_integrity():
    """Every recorded build-input hash matches its bytes - all four tiers, plus the shared layer.

    ⚠ **THIS USED TO ITERATE `COMP_SCRIPTS` ALONE AND CALL THAT INTEGRITY** (`RLY5-1`, DC-18 proxy
    check). It was blind to the 10 FORMAL_ONLY scripts, the 3 standalone register tokens, and
    `zp_utils.py` - which all 43 build scripts import and which renders the meta line of every
    document. Measured: `zp_utils.py` moved ALONE gave `check_hashes.py` exit 1 while this printed
    `[PASS] Build-script hash integrity` and the gate said `GO`.

    **The push hook and CI both blocked correctly; only this one was blind - and this is the one whose
    output is a permanent Zenodo DOI.** Now DELEGATES to `check_hashes.all_hash_mismatches()`, which is
    the single definition of the property.

    ⚠ **THE TWO READERS ARE NOT CONTROL-BOUND, AND THIS DOCSTRING CLAIMED THEY WERE.** `hooks.py`
    judges `check_hashes.main()`'s EXIT CODE; this imports `all_hash_mismatches()`. The tier controls
    in `--selftest` cover only the second — measured (/rely round 4): deleting a tier's accumulator
    from `main()` leaves `--selftest` green, and `main()` then PRINTS the mismatch and returns zero.
    Nothing passes through that gap today, so it is ledger debt rather than a live fail-open — but
    the delegation's stated ground was stronger than what exists, which is the same overclaim shape
    this file's own history is full of. Binding them is the mutation harness's first control set.
    A second copy of the logic here is what produced the drift in the first place.
    """
    bad = ch.all_hash_mismatches()
    for b in bad:
        # ⚠ NAME THE ACTUAL REMEDY. One label for two different faults sent readers to the wrong fix:
        # a MISSING provenance token is not staleness, and no amount of bumping or rebuilding closes
        # it — the fix is to add a `formal:` token. (Editorial round 4; the wording is theirs.)
        if 'no formal: token in register.md' in b:
            fail(f'No register provenance token (add a formal: token; do NOT bump or rebuild) - {b}')
        else:
            fail(f'Hash mismatch (version bump/rebuild overdue) - {b}')
    return not bad


def _register_versions():
    """{ZP-X: (formal_ver, comp_ver)} from register.md columns (first-wins, base layer)."""
    out = {}
    for line in read(REGISTER).splitlines():
        if not line.strip().startswith('|'):
            continue
        cols = [c.strip() for c in line.split('|')]
        if len(cols) < 5:
            continue
        m = re.match(r'(ZP-[A-Z])', cols[1])
        if m and m.group(1) not in out:
            out[m.group(1)] = (cols[2], cols[4])
    return out


def _script_version(script):
    """The `VERSION` constant of a build script, or None if it cannot be read.

    ⚠ **THIS READ FROM `.claude-local/`, WHICH HAS HELD NO BUILD SCRIPTS SINCE 2026-08-15**
    (`RLY18-2`). The mirror was retired that day and `scripts/` became the only home, so every lookup
    returned None, `if rv and sv` never fired, and `c_register_vs_script_version` reported
    `[PASS] register <-> script VERSION` having resolved **0 of 26**. Measured live: `VERSION='9.99'`
    against a register row of `v1.21` still printed `[PASS]`.

    Same class as `RLY5-1` in this same file - a check reporting clean over ground it never walked.
    That is now twice here, which is why the caller below asserts a RESOLUTION FLOOR rather than
    trusting that silence means agreement.
    """
    path = os.path.join(ch.SCRIPT_DIR, script)
    if not os.path.exists(path):
        return None
    m = re.search(r"^VERSION\s*=\s*['\"]([^'\"]+)['\"]", read(path), re.M)
    return m.group(1) if m else None


def c_register_vs_script_version():
    """register version columns match each build script's VERSION (best-effort -> WARN)."""
    regv = _register_versions()
    issues = []
    for doc in ch.FORMAL_SCRIPTS:
        base = doc.replace('-formal', '')
        rv = regv.get(base, (None, None))[0]
        sv = _script_version(ch.FORMAL_SCRIPTS[doc])
        if rv and sv and norm_ver(rv) != norm_ver(sv):
            issues.append(f'{base} formal: register "{rv}" vs script "{sv}"')
    for doc in ch.COMP_SCRIPTS:
        rv = regv.get(doc, (None, None))[1]
        sv = _script_version(ch.COMP_SCRIPTS[doc])
        if rv and sv and norm_ver(rv) != norm_ver(sv):
            issues.append(f'{doc} comp: register "{rv}" vs script "{sv}"')

    # ⚠⚠ THE RESOLUTION FLOOR. Every comparison above is guarded by `if rv and sv`, so a script whose
    # VERSION cannot be read is skipped SILENTLY — and when the path was wrong, that was all 26 of
    # them and this still printed `[PASS]` (`RLY18-2`). **A comparison that ran zero times is not a
    # comparison that passed.** Count what actually resolved and fail when the answer is nothing.
    _total = len(ch.FORMAL_SCRIPTS) + len(ch.COMP_SCRIPTS)
    _resolved = sum(1 for s in list(ch.FORMAL_SCRIPTS.values()) + list(ch.COMP_SCRIPTS.values())
                    if _script_version(s) is not None)
    if _resolved == 0:
        fail(f'register<->script VERSION resolved 0 of {_total} build scripts - the check did not '
             f'run at all (bad path?), so its silence means nothing')
        return False
    if _resolved < _total:
        warn(f'register<->script VERSION: only {_resolved} of {_total} scripts had a readable '
             f'VERSION; the rest were skipped silently')

    for i in issues:
        warn(f'register<->script VERSION - {i} (authoritative check: /editorial-review)')
    return not issues


def c_registry_invariant():
    """LEAN_CUSTOM_REGISTRY '### ' entry count == [ZP-CUSTOM] tag count in the Lean sources."""
    entries = len(re.findall(r'(?m)^###\s', read(REGISTRY)))
    tags = 0
    for path in glob.glob(LEAN_GLOB, recursive=True):
        if '.lake' in path.replace('\\', '/'):
            continue
        tags += read(path).count('[ZP-CUSTOM]')
    if entries != tags:
        fail(f'LEAN_CUSTOM_REGISTRY out of sync: {entries} entries vs {tags} [ZP-CUSTOM] tags')
    return entries == tags, entries, tags


def c_zenodo():
    """.zenodo.json is valid JSON; surface the layer-count phrase for human check."""
    try:
        d = json.loads(read(ZENODO))
    except Exception as e:
        fail(f'.zenodo.json invalid JSON: {e}')
        return False, None
    desc = d.get('description', '')
    m = re.search(r'([A-Za-z]+|\d+)\s+formal layers', desc)
    phrase = m.group(0) if m else '(no "N formal layers" phrase found)'
    return True, phrase


def c_conflict_markers():
    """No unresolved git conflict markers in tracked files."""
    out = git('grep', '-lE', r'^(<<<<<<<|>>>>>>>)')
    files = [f for f in out.splitlines() if f.strip()]
    if files:
        for f in files:
            fail(f'Conflict marker present in {f}')
    return not files


def c_releases_entry(tag):
    """RELEASES.md contains a '## <tag>' header for the version being cut."""
    txt = read(RELEASES)
    if re.search(r'(?m)^##\s+' + re.escape(tag) + r'\b', txt):
        return True
    fail(f'RELEASES.md has no "## {tag}" entry')
    return False


def c_doc_links():
    """Every PDF linked from README/GUIDE exists in the repo; em-dashes flagged."""
    ok = True
    for f in (README, GUIDE):
        if not os.path.exists(f):
            warn(f'{f} not found')
            continue
        txt = read(f)
        for m in re.finditer(r'\[[^\]]*\]\(([^)]+\.pdf)\)', txt):
            target = m.group(1).split('#')[0]
            if target.startswith('http'):
                continue
            if not os.path.exists(target):
                fail(f'{f}: linked PDF missing -> {target}')
                ok = False
        if '—' in txt:
            warn(f'{f}: contains em-dash (U+2014) - use hyphens (editorial enforces)')
    return ok


def c_scripts_mirror():
    """RETIRED 2026-08-15 — there is no mirror left to check, so the check is a deletion.

    This used to WARN when `scripts/build_X.py` had drifted from its `build_X.py`
    source. The honest reading of that check is that it existed to police a hazard the LAYOUT
    created: two live copies with a per-commit hand-copy obligation between them. It also could
    not do its job — only the private copy was fingerprinted in register.md, so the published copy
    was outside the integrity check, and `scan_pdfs.py` drifted for three months undetected.

    `scripts/` is now the single home. A stale mirror is not something to warn about; it is
    something that can no longer exist. Kept as a named no-op so the check list stays legible and
    nobody re-adds it — deleting the mirror is what closed the class."""
    return True


def c_signals(tag):
    """Report gate-signal freshness vs HEAD (INFO: post-merge HEAD may differ from reviewed commit)."""
    head = git('rev-parse', 'HEAD').strip()
    rows = []
    for name in ('er', 'ar', 'cr', 'pa'):
        p = os.path.join(LOCAL, f'{name}_cleared.txt')
        if not os.path.exists(p):
            rows.append(f'{name}: (absent)')
            continue
        val = read(p).strip()
        rows.append(f'{name}: {"==HEAD" if val == head else "!=HEAD (" + val[:8] + ")"}')
    return rows


def c_untracked_pdfs():
    """Untracked PDFs in the repo root (the ZP_Reals_Companion.pdf class) -> WARN."""
    out = git('status', '--porcelain')
    pdfs = []
    for line in out.splitlines():
        if line.startswith('??'):
            path = line[3:].strip()
            if path.lower().endswith('.pdf') and '/' not in path.replace('\\', '/'):
                pdfs.append(path)
    for p in pdfs:
        warn(f'untracked PDF in root: {p} (archive / finish / .gitignore?)')
    return not pdfs


# --------------------------------------------------------------------------- runner

def line(status, name, detail=''):
    print(f'  [{status:4}] {name}{("  - " + detail) if detail else ""}')


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls on the release gate's decidable parts.

    Added 2026-08-15 for the Phase 1 exit. This gate is PROCEDURAL — no git event fires on tag
    creation, so nothing runs it automatically and a broken check here is invisible until a release
    is being cut, which is the worst moment to discover it.

    Scope is honest and narrow: the mechanically decidable helpers, plus the two structural facts a
    release depends on. It does NOT simulate a whole release; the judgement checklist this gate
    prints is not mechanizable and is not pretended to be."""
    bad = 0

    print('  MUST FIRE')
    # An absent tag must be NO-GO, never a silent pass.
    txt = read(RELEASES)
    ghost = 'v99.99'
    ok = ('## %s' % ghost) not in txt
    bad += 0 if ok else 1
    print('    %-34s %s' % ('an unknown tag has no RELEASES row', 'ok' if ok else '*** WRONG ***'))

    # A version mismatch must compare unequal after normalisation.
    ok = norm_ver('v1.2') != norm_ver('1.3')
    bad += 0 if ok else 1
    print('    %-34s %s' % ('differing versions compare unequal', 'ok' if ok else '*** WRONG ***'))

    print('  MUST SUPPRESS')
    # Normalisation must NOT invent a difference across the forms actually used in register.md.
    ok = norm_ver('v1.2') == norm_ver('1.2') == norm_ver(' V1.2 ')
    bad += 0 if ok else 1
    print('    %-34s %s' % ('v-prefix/space/case normalise equal', 'ok' if ok else '*** WRONG ***'))

    # The files this gate reads must exist; a missing one would make every check vacuous.
    missing = [f for f in (REGISTER, RELEASES, REGISTRY, ZENODO, README, GUIDE)
               if not os.path.exists(os.path.join(REPO, f))]
    ok = not missing
    bad += 0 if ok else 1
    print('    %-34s %s%s' % ('every input file exists', 'ok' if ok else '*** MISSING ***',
                              '' if ok else ' ' + ', '.join(missing)))

    # ⚠ The retired mirror check must stay a no-op returning True. If someone "restores" it, it
    # would compare scripts/ against a .claude-local/ that no longer holds build scripts and warn
    # on all 43 forever.
    ok = c_scripts_mirror() is True
    bad += 0 if ok else 1
    print('    %-34s %s' % ('the retired mirror check is inert', 'ok' if ok else '*** REVIVED ***'))

    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def main():
    args = [a for a in sys.argv[1:]]
    if args and args[0] == '--selftest':
        print('ZP Release-Readiness Gate - CONTROLS')
        print('=' * 64)
        return selftest()
    if not args or args[0].startswith('-'):
        print('usage: python %s <tag>   (e.g. v2.7)' % SELF)
        return 2
    tag = args[0]

    print(f'ZP Release-Readiness Gate - tag {tag}')
    print('=' * 64)
    print('MECHANICAL (blocking unless noted):')

    line('PASS' if c_engineers_takes() else 'FAIL', "Engineer's Takes filled")
    line('PASS' if c_hash_integrity() else 'FAIL', 'Build-script hash integrity (register tokens)')
    inv_ok, ent, tg = c_registry_invariant()
    line('PASS' if inv_ok else 'FAIL', 'LEAN_CUSTOM_REGISTRY invariant', f'{ent} entries / {tg} tags')
    z_ok, z_phrase = c_zenodo()
    line('PASS' if z_ok else 'FAIL', '.zenodo.json valid JSON', f'description says: {z_phrase}')
    line('PASS' if c_conflict_markers() else 'FAIL', 'No conflict markers (tracked files)')
    line('PASS' if c_releases_entry(tag) else 'FAIL', f'RELEASES.md has "## {tag}" entry')
    line('PASS' if c_doc_links() else 'FAIL', 'README/GUIDE linked PDFs exist')

    print('BEST-EFFORT / HYGIENE (warn-only):')
    line('PASS' if c_register_vs_script_version() else 'WARN', 'register <-> script VERSION')
    line('PASS' if c_scripts_mirror() else 'WARN', 'scripts/ mirror current')
    line('PASS' if c_untracked_pdfs() else 'WARN', 'No untracked root PDFs')

    print('INFO:')
    for r in c_signals(tag):
        print(f'    gate signal {r}')
    print('    (post-merge HEAD legitimately differs from the reviewed PR commit;')
    print('     signal freshness is context, not a blocker - confirm gates ran on the PR.)')

    if warns:
        print('-' * 64)
        print('WARNINGS (review, not blocking):')
        for w in warns:
            print(f'  ! {w}')

    print('-' * 64)
    print('JUDGMENT CHECKLIST (a human must confirm - not mechanizable):')
    for item in (
        'Editorial + adversary review ran on all touched prose (this release\'s PR).',
        'claim-review ran if any claim status changed; prior-art-review if a synthesis layer was created/strengthened.',
        'Companion synced for every formal doc whose version bumped.',
        'Major-vs-minor version decision is correct; Lean-only-change release question raised if applicable.',
        '.zenodo.json description reflects this release (cannot be updated retroactively).',
        'Release body drafted and Tim approved it BEFORE `gh release create`.',
        'Post-release: confirm the Zenodo snapshot minted. README badge is the CONCEPT DOI '
        '(auto-resolves to latest) - NO per-release badge edit needed.',
    ):
        print(f'  [ ] {item}')

    print('=' * 64)
    if fails:
        print(f'NO-GO - {len(fails)} blocking failure(s):')
        for f in fails:
            print(f'  X {f}')
        return 1
    print('GO (mechanical checks pass). Now confirm the judgment checklist above before cutting the tag.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
