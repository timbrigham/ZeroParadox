"""The accepted-defect baselines are FROZEN: they may only SHRINK, never grow.

WHY THIS IS THE WHOLE MECHANISM (Tim, 2026-08-22):

    "We should never be adding anything to the baseline at this point, period... all we need to do is
     work through the backlog. Step one is to stop the bleeding -- no new additions. **You don't have
     to guard a backlog that's impossible to be written.**"

An earlier design built a retired-entry list, a check that no retired entry could reappear, and a
git-history check guarding that check -- three mechanisms, every one of them there to catch an entry
coming BACK. If the file can never be written, nothing can come back. One property replaces all
three, and `common.refuse_baseline_write` makes the ordinary path refuse before this ever fires.

⚠⚠ SUBSET, NOT COUNT -- AND THE DIFFERENCE IS THE WHOLE CHECK. Comparing entry COUNTS would pass a
change that deletes one line and adds another: the total is unmoved and a brand-new defect is now
suppressed. Counting is a PROXY for the property; the property is that today's set contains nothing
that yesterday's did not. This bundle committed the proxy-instead-of-property error twice on
2026-08-21 (a routing PATTERN standing in for enforcement, a source SUBSTRING standing in for use),
so it is spelled out rather than left to be rediscovered a third time.

⚠ COMPARED AGAINST `git show HEAD:<path>`, WHICH IS A DELIBERATE EXCEPTION to CLAUDE.md's *"every
hash in this scheme is of the FILE ON DISK, never a git value."* That rule exists because a REVIEWER
must certify the bytes they actually read. The question here is the opposite one -- *has the on-disk
file diverged upward from the record?* -- and it is load-bearing that the comparison is against
something the file's editor does not control. A check of the file against itself is satisfiable by
editing the file.

⚠ NOT EVERY DATA FILE NEARBY IS DEBT. The frozen set is `common.FROZEN_BASELINES` and it holds only
the accepted-defect backlog. `decl_baseline.txt` is a high-water mark of known declarations and MUST
grow; `encoding_whitelist.txt` holds verified permanent carve-outs; `scope_baseline.txt` and
`pattern_baseline.txt` are configuration. Freezing any of those breaks something.

Usage (this tool prints its own invocation path; never hardcode one):
  check_frozen.py            report
  check_frozen.py --block    non-zero exit if any frozen baseline grew
  check_frozen.py --selftest controls, both directions
"""
import io
import os
import shutil
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402
import report                                                    # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
REPO = str(common.REPO)


def entries(text):
    """Baseline keys, by the same reading `common.load_baseline` uses: strip, drop blanks and `#`."""
    out = set()
    for line in text.splitlines():
        s = line.strip()
        if s and not s.startswith('#'):
            out.add(s)
    return out


def at_ref(rel, ref='HEAD'):
    """The file's content at `ref`, or None if it does not exist there."""
    p = subprocess.run(['git', 'show', '%s:%s' % (ref, rel)], cwd=REPO, capture_output=True,
                       text=True, encoding='utf-8', errors='replace')
    return p.stdout if p.returncode == 0 else None


def at_head(rel):
    """Retained name — see `at_ref`. The BASIS is a parameter now (`FRZ-2`)."""
    return at_ref(rel, 'HEAD')


def check_one(name, base='HEAD'):
    """Returns (status, added, removed, n_now, n_base). status is ok / GREW / NEW / gone."""
    rel = 'tools/verify/%s' % name
    disk = os.path.join(REPO, 'tools', 'verify', name)
    head = at_ref(rel, base)
    if not os.path.exists(disk):
        # Draining a baseline to zero and deleting it is the SUCCESS condition, not a failure.
        return ('gone', set(), entries(head) if head is not None else set(), 0,
                len(entries(head)) if head is not None else 0)
    now = entries(io.open(disk, encoding='utf-8-sig', errors='replace').read())
    if head is None:
        # ⚠ A frozen baseline that does not exist at HEAD is being CREATED. Every entry in it is an
        # addition, so this fails closed rather than treating "no prior version" as permission.
        return ('NEW', now, set(), len(now), 0) if now else ('ok', set(), set(), 0, 0)
    before = entries(head)
    added = now - before
    removed = before - now
    return ('GREW' if added else 'ok'), added, removed, len(now), len(before)


# ═══ THE REMOVAL TRIGGER ══════════════════════════════════════════════════════════════════════
#
# ⭐ REMOVING GRANDFATHERED STATUS IS WHAT TRIGGERS A CONTENT REVIEW (Tim, 2026-08-22: *"we
# shouldn't need to do anything except remove the grandfathered status right? not showing up at all
# should trigger a content review"*).
#
# **A baseline entry IS the record that a site was let through UNEXAMINED.** So deleting one retires
# the evidence of a liability; it does not discharge it. The checkers cannot tell the difference,
# because they measure the SHAPE of prose (volume, vocabulary), never whether a claim is true — a
# block that drops under cap is not a block whose claims were checked.
#
# ⚠⚠ MEASURED THE DAY THIS WAS WRITTEN, WHICH IS WHY IT BLOCKS. Two entries were removed from
# `prose_baseline.txt` and `modal_baseline.txt` for `Kruskal.lean` on the strength of a green
# `check_prose` run. A claim review afterwards returned FAIL-BEDROCK: the file's central modal claim
# rested on a witness that proves a DIFFERENT theorem (`af`-formulated, where the corpus proves the
# sequential form, and the two are not intuitionistically equivalent). The edit that removed the
# entry had also silenced the checker that had been catching it. Nothing mechanical noticed; a human
# did.
#
# ⚠ FAIL-CLOSED, AND "THE KEY STOPPED MATCHING" IS NOT ENOUGH. A removal has two very different
# causes that look identical to every checker:
#     content GONE  — the site was deleted or its duplication collapsed. Nothing to review.
#     content MOVED — the site was relocated or re-worded, so its PATH-KEYED entry died while the
#                     claim lived on somewhere else. This is the Kruskal case exactly.
# Distinguishing them requires knowing whether the text survives, which is not decidable here. So the
# only exemption is that the FILE ITSELF is gone; everything else owes a review.


_UNSET = object()


def path_of(key):
    """The repo-relative path a baseline key refers to.

    Verified against all six frozen formats 2026-08-22 — the path is always the first field, and the
    separator is one of `::` (prose/pov/figures/negatives), `|` (modal) or a tab (pov's trailing
    locator and snippet). Taking the earliest of the three is uniform across every one."""
    cut = len(key)
    for sep in ('::', '|', '\t'):
        i = key.find(sep)
        if i != -1:
            cut = min(cut, i)
    return key[:cut].strip().replace('\\', '/')


def claim_signal():
    """The SET of paths a current `claim_review` record covers, or None when there is no coverage.

    ⚠⚠ THE LEDGER, NOT A FILE. `cr_cleared.txt` is RETIRED (2026-08-24) — the last of the
    `*_cleared.txt` scheme to go. `gitRobot.md` § 12-0-ter set the precondition exactly: *"Register
    `rely` and `claim_review` as types, and admit them, BEFORE the signal path is removed."* Both are
    registered and admitted, so the precondition was met and the reader moved.

    ⚠ THE READER MOVED IN THE SAME CHANGE AS THE WRITER, AND THAT ORDER IS THE WHOLE POINT. Retiring
    the file while this still opened it would have made a baseline removal FREE — the contract's
    words: *"a suppression mechanism losing its price."* That is the direction that fails OPEN.

    ⚠ RETURNS None WHEN THE LEDGER CANNOT BE ASKED, and None here means "no signal", which makes
    every removal owe a review. Fail-CLOSED on purpose: an unreachable ledger must never look like a
    discharged one.

    ⚠ THE VALUE IS A SET, NOT A HASH MAP. The old file stored a SHA-256 per path and this function's
    caller re-hashed the file on disk to detect drift — a second staleness predicate, which
    `gitRobot.md` § 12-0-alpha names as the thing to delete: *"does it make the client compute
    something it could have asked for?"* The ledger keys coverage by blob ID and already answers
    STALE; a path present here is covered AND current, and the caller re-checks nothing."""
    try:
        import record
        out = record._call('inventory', {'ref': common.INDEX, 'action': 'commit'})
        if not out or not out.get('ok') or not isinstance(out.get('rows'), list):
            return None
        rid = None
        for r in out['rows']:
            if r.get('step') == 'claim_review':
                # ⚠ ONLY `SATISFIED` DISCHARGES. `STALE` means the reviewed bytes moved and
                # `MISSING` means nothing ran; both must read as "no coverage", never as a pass.
                if not discharges(r.get('status')):
                    return None
                rid = r.get('record_id')
                break
        if not rid:
            return None
        # ⚠ THE ROW CARRIES COUNTS, NOT PATHS — `subjects_covered` is an int. The paths live on the
        # RECORD. Verified against the live server 2026-08-24: `get` returns `record.subjects` as
        # `[{path, git_blob_id}]`.
        got = record._call('get', {'id': rid})
        rec = (got or {}).get('record') or {}
        return {s.get('path', '').replace('\\', '/') for s in rec.get('subjects', [])
                if s.get('path')}
    except Exception:                                          # noqa: BLE001 — cannot ask == no signal
        return None


def review_owed(removed, sig=_UNSET, exists=None, hash_of=None):
    """[(path, why)] for removals that still owe a content review.

    `sig` is the SET of paths the claim review covers at their current bytes — see `claim_signal`.
    Membership discharges; the freshness question was already answered server-side, by the one
    staleness predicate, so nothing is re-hashed here.

    ⚠ `hash_of` IS RETAINED AND UNUSED, deliberately: it is part of this function's control surface
    and removing a parameter a control passes would break the control silently. It is ignored."""
    # ⚠ THE LOOKUPS ARE INJECTABLE SO A CONTROL CAN DRIVE THIS. Without that the predicate could
    # only be exercised against whatever happens to be on disk, i.e. never against the cases that
    # matter — which is how a control ends up being a hypothesis nobody has seen fail. That matters
    # more now, not less: the signal comes from a SERVER, so `sig=` is the only way to exercise the
    # covered case without either polluting the live stream or inventing a test-only switch.
    exists = exists or os.path.exists
    owed = []
    if sig is _UNSET:
        sig = claim_signal()
    for rel in sorted({path_of(k) for k in removed}):
        if not rel:
            continue
        disk = os.path.join(REPO, rel.replace('/', os.sep))
        if not exists(disk):
            continue                       # the file itself is gone — nothing left to review
        # ⚠ THE MIGRATION CASE, AND IT IS THE ONE THAT ACTUALLY BIT. An entry naming `Foo.lean` can
        # die because the claim MOVED to the `Foo.md` ride-along — dead key, live content. Reviewing
        # only `Foo.lean` would then miss the text entirely, so a sibling ride-along is demanded too.
        targets = [rel]
        if rel.endswith('.lean') and exists(os.path.join(
                REPO, (rel[:-5] + '.md').replace('/', os.sep))):
            targets.append(rel[:-5] + '.md')
        for t in targets:
            note = '' if t == rel else ' (ride-along carrying the moved content)'
            if sig is None:
                # ⚠ Covers BOTH "no record" and "the ledger could not be asked". They are different
                # facts and neither discharges anything, so both land here — fail-CLOSED.
                owed.append((t, 'no current claim_review record covers this ref' + note))
                continue
            if t not in sig:
                # ⚠ STALE IS ALREADY EXCLUDED UPSTREAM. `claim_signal` returns paths only from a
                # SATISFIED record, so "covered at different bytes" cannot reach here — the whole
                # record would have been STALE and `sig` would be None. One predicate, server-side.
                owed.append((t, 'not among the subjects of the claim_review record' + note))
    return owed


def push_base():
    """What the remote already has — the correct basis for a PUSH gate.

    ⚠⚠ `FRZ-2`. This used to be `git show HEAD:`, which makes the whole check VACUOUS the moment the
    change is committed: HEAD then contains the edit, the diff is empty, and a grown or drained
    baseline reads `ok (+0)`. Measured 2026-08-22 — uncommitted growth exited 1, the identical
    growth committed exited 0 with "no frozen baseline grew". The gate only ever saw the working
    tree, which is not what a push sends.

    Falls back to HEAD when there is no upstream (a fresh clone, a detached probe), and the basis is
    PRINTED on every run so a fallback can never be mistaken for a comparison."""
    p = subprocess.run(['git', 'rev-parse', '--abbrev-ref', '@{upstream}'], cwd=REPO,
                       capture_output=True, text=True, encoding='utf-8', errors='replace')
    ref = (p.stdout or '').strip()
    return (ref, 'upstream') if p.returncode == 0 and ref else ('HEAD', 'HEAD (no upstream)')


def run(block=False, base=None, record_to_ledger=False):
    base, why_base = (base, 'explicit --base') if base else push_base()
    report.banner('frozen accepted-defect baselines', [
        ('purpose', 'the accepted-defect backlog may only SHRINK'),
        ('property', "today's set is a SUBSET of the basis below — not merely the same size"),
        # ⚠ `FRZ-4`. The basis line used to say "what the REMOTE already has" UNCONDITIONALLY, in a
        # function whose own docstring says it falls back to HEAD. In the fallback branch that
        # sentence is false, and it is false in the direction that reassures: a committed change
        # reads as already-accepted, which is the FRZ-2 vacuity wearing the banner of a remote
        # comparison. Say which basis this actually is.
        ('basis', 'git show %s:<path> (%s) — %s' % (
            base, why_base,
            'what the REMOTE already has, not the working tree' if why_base == 'upstream' else
            'NOT the remote — nothing upstream was resolved, so this compares against your own '
            'tree and anything already committed reads as accepted')),
        ('trigger', 'removing an entry OWES a /claim-review signal — the entry recorded that the '
                    'site was never examined'),
        ('scope', '%d frozen file(s); decl/scope/pattern/whitelist are NOT debt and are excluded'
         % len(common.FROZEN_BASELINES)),
        ('mode', 'BLOCK' if block else 'report only (pass --block to enforce)'),
    ])
    bad, grew, total_now, total_head, all_removed = 0, 0, 0, 0, set()
    grown = set()                     # which baselines FAILED — the per-subject half of the verdict
    for name in sorted(common.FROZEN_BASELINES):
        status, added, removed, n_now, n_head = check_one(name, base)
        if status in ('GREW', 'NEW'):
            grown.add(name)
        all_removed |= removed
        total_now += n_now
        total_head += n_head
        delta = n_now - n_head
        print('  %-26s %-5s %5d entr%s (%+d)'
              % (name, status if status != 'ok' else 'ok', n_now,
                 'y' if n_now == 1 else 'ies', delta))
        if status in ('GREW', 'NEW'):
            bad += 1
            grew += 1
            for a in sorted(added)[:5]:
                print('        + %s' % a[:110])
            if len(added) > 5:
                print('        + ... %d more' % (len(added) - 5))
    print('')
    # ⚠ THE TOTAL PRINTS ON EVERY RUN, CLEAN OR NOT. A debt figure that only surfaces when something
    # is wrong cannot show progress, and `selfheal.py`'s lesson is that a number reachable only from
    # the rarest command surfaces never. DOWN is the point of this file.
    print('  ACCEPTED-DEFECT BACKLOG: %d  (was %d at the basis above, %+d)'
          % (total_now, total_head, total_now - total_head))

    # ⚠⚠ THE REMOVAL TRIGGER. Shrinking is the POINT of this file, so a removal is never itself a
    # failure — but the entry was the record that a site went UNEXAMINED, so retiring it obliges the
    # examination it was standing in for. See the block above `path_of`.
    owed = review_owed(all_removed)
    if all_removed:
        print('')
        print('  GRANDFATHERED STATUS REMOVED: %d entr%s across %d file(s)'
              % (len(all_removed), 'y' if len(all_removed) == 1 else 'ies',
                 len({path_of(k) for k in all_removed})))
        for k in sorted(all_removed)[:5]:
            print('        - %s' % k[:110])
        if len(all_removed) > 5:
            print('        - ... %d more' % (len(all_removed) - 5))
    if owed:
        bad += len(owed)
        print('')
        print('  CONTENT REVIEW OWED — a baseline entry is the record that a site was let through')
        print('  UNEXAMINED. Removing it retires that record; it does not discharge the liability.')
        print('  These checkers measure the SHAPE of prose, never whether a claim is TRUE.')
        for rel, why in owed:
            print('    FAIL  %-52s %s' % (rel, why))
        print('')
        print('  Run  /claim-review <path>  and let it record a claim_review verdict, or put')
        print('  the entry back. Measured 2026-08-22: two entries removed on a green volume check,')
        print('  and the review afterwards returned FAIL-BEDROCK on the claim underneath.')
    elif all_removed:
        print('  every affected file is covered by a current claim-review signal.')
    if grew:
        print('')
        print('  A frozen baseline GREW. Nothing is ever added to these again — fix the site, or if')
        print('  the finding is wrong then the CHECKER is wrong and that is a DEFECTS.md row, not a')
        print('  suppression. `python %s` in a checker refuses the write for the same reason.'
              % SELF)
    report.done('frozen accepted-defect baselines', bad == 0,
                'no growth; every removal reviewed' if bad == 0 else
                '%d problem(s): growth and/or unreviewed removal' % bad)

    # ⚠⚠ THE PROPERTY IS VERIFIED AGAINST A FILE SET, AND HERE THE SET IS THE BASELINES THEMSELVES
    # (Tim, 2026-08-23). "The accepted-defect backlog only shrinks" is a statement ABOUT these six
    # files, so they are the subjects — change one and the verdict must be re-earned. The paths that
    # OWE a review are subjects too, and they FAIL: the removal trigger is a claim about them, not
    # about the baseline that recorded them.
    _argv = ['--record'] if record_to_ledger else []
    rc = common.record_if_asked(
        'check_frozen',
        ['tools/verify/%s' % n for n in sorted(common.FROZEN_BASELINES)],
        {'tools/verify/%s' % n for n in grown} | {rel for rel, _why in owed},
        'a frozen baseline grew, or a removal owes a /claim-review',
        argv=_argv)
    if rc:
        return rc

    # ⚠⚠ `claim_review` IS RECORDED ON EVERY RUN, NOT ONLY WHEN A REMOVAL HAPPENED. Emitter contract
    # from mcp-mayhem (REQ-2 reply), and the reason is one this project already knows: the registry's
    # `when` is a PATH GLOB, so it cannot express "conditional on an EVENT" — a baseline entry being
    # removed. A key that appears only sometimes is indistinguishable from a key nobody ran, which is
    # absence rendering as success through the door marked "not applicable".
    #
    # So: PASS over the baselines when nothing was removed; FAIL over the paths that owe a review
    # when something was. The verdict is about the SAME subjects either way — the baselines are what
    # a removal is a removal FROM.
    rc = common.record_if_asked(
        'claim_review',
        ['tools/verify/%s' % n for n in sorted(common.FROZEN_BASELINES)],
        {rel for rel, _why in owed},
        'a grandfathered entry was removed and its content review is not discharged',
        argv=_argv, tier='H')
    if rc:
        return rc

    return 1 if (bad and block) else 0


# The controls, in the two-group shape `common.fire_suppress` expects. Each case is the TEXT of a
# baseline as it would stand after an edit; the predicate asks whether that edit GREW the set.
_BEFORE = '# header\na\tsite one\nb\tsite two\n'

_MUST_FIRE = [
    ('a new entry appended', '# header\na\tsite one\nb\tsite two\nc\tbrand new\n'),
    # ⚠⚠ THE CASE A COUNT CHECK PASSES, and it is the reason this is a SUBSET test. One entry out,
    # one in: the total is unchanged and a brand-new defect is now suppressed. Counting is a PROXY
    # for the property; the property is that today's set adds nothing. This bundle shipped the
    # proxy-instead-of-property error twice on 2026-08-21 and this control is the standing answer.
    ('one swapped for another at EQUAL count', '# header\na\tsite one\nc\tbrand new\n'),
    ('everything replaced', '# header\nx\tone\ny\ttwo\n'),
    ('an entry re-added after being drained', '# header\na\tsite one\nb\tsite two\nb2\tback again\n'),
]

_MUST_SUPPRESS = [
    ('unchanged', _BEFORE),
    ('one entry removed — progress', '# header\na\tsite one\n'),
    ('drained to empty — the success condition', '# header\n'),
    ('reordered', '# header\nb\tsite two\na\tsite one\n'),
    ('a comment added', '# header\n# a note about the work\na\tsite one\nb\tsite two\n'),
    ('indented comment, blank lines', '# header\n\n   # indented note\na\tsite one\nb\tsite two\n'),
]


def _grew(text):
    """The predicate under test: did this candidate ADD anything to `_BEFORE`?"""
    return bool(entries(text) - entries(_BEFORE))




# ═══ CONTROLS FOR THE REMOVAL TRIGGER ═════════════════════════════════════════════════════════
#
# ⚠ SEPARATE FROM THE GROWTH CONTROLS ABOVE, because they test a different property. Growth asks
# "was anything ADDED"; this asks "was a removal PAID FOR". `_MUST_SUPPRESS` above still lists
# 'one entry removed — progress' and that is still correct: a removal is not growth. It is,
# however, a debt.
_R_KEY = 'ZeroParadox/Demo/Thing.lean::block::abc123abc123::A demo block'
_R_PATH = 'ZeroParadox/Demo/Thing.lean'
_R_HASH = 'a' * 64


def discharges(status):
    """Does a `claim_review` inventory status discharge a removal? ONLY `SATISFIED` does.

    ⚠⚠ EXTRACTED SO THE STALE CASE KEEPS A CONTROL. It used to live in `review_owed`, which compared
    a stored SHA-256 against the file on disk — *"reviewed, then edited"*. That comparison is gone
    (the ledger owns freshness now, and re-deriving it here would be a second staleness predicate),
    but **the rule it enforced must not leave with it.** This is the same fact at its new boundary:
    a STALE record means the reviewed bytes moved, and it must read as NO coverage.

    ⚠ `NOT_APPLICABLE` does not discharge either. It means the step did not apply — nothing was
    examined — and *"it did not apply"* is not *"the liability was reviewed"*."""
    return status == 'SATISFIED'


def _owes(case):
    """The predicate under test: does this removal still owe a content review?"""
    sig, present, _unused = case
    return bool(review_owed({_R_KEY}, sig=sig,
                            exists=lambda pth: any(pth.endswith(x) for x in present)))


_R_MUST_FIRE = [
    ('no record, or the ledger could not be asked', (None, ('Thing.lean',), None)),
    ('a record exists but does not cover the file', ({'other/File.lean'},
                                                     ('Thing.lean',), None)),
    # ⚠⚠ THE MIGRATION CASE — dead key, LIVE content. The entry names the .lean, the claim moved to
    # the .md ride-along, and reviewing only the .lean would miss the text entirely. Measured on
    # Kruskal 2026-08-22, where exactly this shape reached a FAIL-BEDROCK claim.
    ('.lean covered but its ride-along .md is not', ({_R_PATH},
                                                    ('Thing.lean', 'Thing.md'), None)),
]

_R_MUST_SUPPRESS = [
    ('the file itself is gone — nothing left to review', (set(), (), None)),
    ('covered by the record', ({_R_PATH}, ('Thing.lean',), None)),
    ('covered by the record, ride-along too',
     ({_R_PATH, 'ZeroParadox/Demo/Thing.md'}, ('Thing.lean', 'Thing.md'), None)),
]

# ⚠ THE STALE CASE, RELOCATED. `_owes` can no longer express it — by the time `sig` exists the
# freshness question is already answered — so it is controlled where the decision now lives.
_S_MUST_FIRE = [
    ('STALE - reviewed, then edited', 'STALE'),
    ('MISSING - never ran', 'MISSING'),
    ('FAIL - the review found something', 'FAIL'),
    ('UNDECIDED - it could not decide', 'UNDECIDED'),
    ('NOT_APPLICABLE - nothing was examined', 'NOT_APPLICABLE'),
]
_S_MUST_SUPPRESS = [('SATISFIED - recorded and current', 'SATISFIED')]


# ═══ BEHAVIOURAL CONTROLS — THEY DRIVE THE PROGRAM, NOT ITS PREDICATES ════════════════════════
#
# ⚠⚠ `FRZ-3` / `FRZ-4`, AND THE TWO ARE ONE DEFECT WEARING TWO FACES: every control above drives a
# PREDICATE through injected lookups, and a predicate that is correct in a program which never
# calls it is worth nothing. `DC-18` — a proxy control.
#
#   `FRZ-3`  `owed = review_owed(all_removed)` -> `owed = []` in `run()` took a grandfathered
#            removal from exit 1 to PASS — printed two lines under `GRANDFATHERED STATUS REMOVED` —
#            while `--selftest` PASSED, `check_checkers --block` reported `violations : 0` and
#            `guards.py` exited 0. Three gates, all green, over a deleted trigger.
#   `FRZ-4`  `push_base()` had NO control at all. `_grew()` compares two in-memory strings and never
#            reaches `at_ref` / `check_one` / `push_base`, so reverting the `FRZ-2` fix to an
#            unconditional `HEAD` basis was invisible to all three.
#
# So these run THE ACTUAL FILE AS A SUBPROCESS against a THROWAWAY git repository and assert what a
# caller sees — the exit code and the text. Nothing is injected. `common.REPO` is
# `Path(__file__).resolve().parent.parent`, so a copy of the bundle under `<tmp>/tools/verify`
# roots the whole checker at `<tmp>` with no environment variable and no seam to stub.
#
# ⚠ THE FIXTURE NEVER TOUCHES THE SHARED CHECKOUT. It is built under `tempfile.mkdtemp()` and
# removed. The `git` calls below run inside that directory, from a Python subprocess — the same way
# `at_ref` and `push_base` themselves shell git.
#
# ⚠⚠ EACH CASE NAMES THE MUTATION IT EXISTS TO CATCH. A control whose failure mode is not written
# down cannot be audited, and both defects here were controls nobody had seen fail.

_FIX_BL = 'prose_baseline.txt'                       # any member of common.FROZEN_BASELINES
_FIX_SRC = 'ZeroParadox/Demo/Thing.lean'
_FIX_A = '%s::block::aaa111::demo block one' % _FIX_SRC
_FIX_B = '%s::block::bbb222::demo block two' % _FIX_SRC


def _fix_git(args, cwd):
    """git INSIDE THE FIXTURE. Identity is pinned so the control does not depend on the machine."""
    return subprocess.run(
        ['git', '-c', 'user.email=control@example.invalid', '-c', 'user.name=control',
         '-c', 'commit.gpgsign=false'] + list(args),
        cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace')


def _plant(root, baseline, source=True):
    """Write the fixture tree: this bundle, one frozen baseline, and the source the key names."""
    vdir = os.path.join(root, 'tools', 'verify')
    if not os.path.isdir(vdir):
        os.makedirs(vdir)
        for mod in ('check_frozen.py', 'common.py', 'report.py'):
            shutil.copyfile(os.path.join(str(common.HERE), mod), os.path.join(vdir, mod))
    with io.open(os.path.join(vdir, _FIX_BL), 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(baseline)
    src = os.path.join(root, _FIX_SRC.replace('/', os.sep))
    if source:
        if not os.path.isdir(os.path.dirname(src)):
            os.makedirs(os.path.dirname(src))
        with io.open(src, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write('-- demo\n')
    elif os.path.exists(src):
        os.remove(src)


# ⚠⚠ `_sign()` IS GONE, AND ITS ABSENCE IS THE POINT. It planted a `cr_cleared.txt` fixture, and that
# file is RETIRED — coverage is a `claim_review` record now. There is no honest way to plant one from
# a control: writing to the live stream pollutes an append-only ledger with fixtures, and a test-only
# switch that makes the checker read a file again is the exemption class this layer keeps paying for.
#
# **So the covered case moved to where it can be driven honestly — `review_owed(..., sig={...})`,
# in-process.** That parameter has always existed for exactly this, and its docstring says so. The
# split is now: the PREDICATE is exercised both ways in `_R_MUST_FIRE`/`_R_MUST_SUPPRESS`, and the
# SUBPROCESS covers the uncovered case end to end, which is the direction that must block.
#
# ⚠ What is deliberately NOT claimed any more: that the end-to-end path clears on a real signal.
# Nothing proves that here, and pretending otherwise with a fixture would be a control passing for
# the wrong reason (`DC-22`). The gap is named in `queue/tooling-retire-last-two-signal-files.md`.


def _invoke(root):
    """Run the checker the way a caller does: as a subprocess, reading only exit code and text."""
    p = subprocess.run([sys.executable, os.path.join(root, 'tools', 'verify', 'check_frozen.py'),
                        '--block'], cwd=root, capture_output=True, text=True,
                       encoding='utf-8', errors='replace')
    return p.returncode, (p.stdout or '') + (p.stderr or '')


def _seed(root, baseline, source=True):
    """A fixture whose FIRST COMMIT holds `baseline`."""
    os.makedirs(root)
    _plant(root, baseline, source=source)
    _fix_git(['init'], root)
    _fix_git(['add', '-A'], root)
    _fix_git(['commit', '-m', 'base'], root)


def _case_removal(root, source=True):
    """Committed {A,B}; on disk {A}. A grandfathered entry has lost its grandfathered status.

    Drives the REMOVAL TRIGGER through `run()` — the wiring `FRZ-3` deleted."""
    _seed(root, '# header\n%s\n%s\n' % (_FIX_A, _FIX_B))
    _plant(root, '# header\n%s\n' % _FIX_A, source=source)
    return _invoke(root)


def _case_growth_behind_upstream(root, bare):
    """Growth COMMITTED after the upstream point — the case where the BASIS decides the answer.

    Against the upstream the baseline GREW; against `HEAD` the growth is inside the basis and the
    diff is empty. That is exactly `FRZ-2`, and this is the control it never had."""
    _seed(root, '# header\n%s\n' % _FIX_A)
    _fix_git(['init', '--bare', bare], os.path.dirname(bare))
    _fix_git(['remote', 'add', 'origin', bare], root)
    branch = (_fix_git(['rev-parse', '--abbrev-ref', 'HEAD'], root).stdout or '').strip()
    _fix_git(['push', '-u', 'origin', branch], root)
    _plant(root, '# header\n%s\n%s\n' % (_FIX_A, _FIX_B))          # GROW …
    _fix_git(['add', '-A'], root)
    _fix_git(['commit', '-m', 'grow'], root)                       # … and COMMIT it
    return _invoke(root)


def selftest_behaviour():
    """Drive `run()` and `push_base()` end to end, as a subprocess. `FRZ-3` / `FRZ-4`."""
    import tempfile
    print('')
    print('  BEHAVIOURAL — the program, as a subprocess, against a throwaway repo')
    tmp = tempfile.mkdtemp(prefix='frozenctl-')
    rows = []
    try:
        code, out = _case_removal(os.path.join(tmp, 'removal'))
        rows.append(('unreviewed removal EXITS 1 and names the liability',
                     code == 1 and 'CONTENT REVIEW OWED' in out,
                     'FRZ-3: owed = review_owed(all_removed) -> owed = []'))

        # ⚠⚠ THE "COVERED REMOVAL PASSES" CASE IS GONE, AND ITS ABSENCE IS DELIBERATE. It planted a
        # `cr_cleared.txt` fixture; coverage is a `claim_review` RECORD now, and there is no honest
        # way to plant one from a throwaway worktree — writing to an append-only ledger from a
        # control pollutes the real stream, and a test-only switch that makes the checker read a file
        # again is the exemption class this layer keeps paying for. Faking it would be a control
        # passing for the wrong reason (`DC-22`), which is worth less than not having it.
        #
        # ⚠ ITS GUARANTEE — *"a control that is always red proves nothing"* — IS STILL HELD, by the
        # file-gone case immediately below: that drives the same program to exit 0 with no liability
        # reported, so an unconditionally-red checker still fails this suite. The covered-removal
        # path itself is now exercised at the PREDICATE (`_R_MUST_SUPPRESS`, both directions) rather
        # than end to end, and that reduction in coverage is named rather than hidden:
        # `queue/tooling-retire-last-two-signal-files.md`.

        code, out = _case_removal(os.path.join(tmp, 'filegone'), source=False)
        rows.append(('…and a removal whose FILE is gone PASSES',
                     code == 0 and 'CONTENT REVIEW OWED' not in out,
                     'the one sanctioned exemption must survive'))

        code, out = _case_growth_behind_upstream(os.path.join(tmp, 'grown'),
                                                 os.path.join(tmp, 'origin_bare'))
        rows.append(('growth COMMITTED past the upstream still EXITS 1',
                     code == 1 and 'GREW' in out,
                     'FRZ-4: push_base() -> return ("HEAD", "HEAD")'))
        rows.append(('…and the basis it reports is the UPSTREAM, not HEAD',
                     'upstream' in out and 'what the REMOTE already has' in out,
                     'FRZ-4: a silent fallback must never read as a remote comparison'))

        code, out = _case_removal(os.path.join(tmp, 'noupstream'))
        rows.append(('with NO upstream the banner does NOT claim the remote',
                     'what the REMOTE already has' not in out and 'NOT the remote' in out,
                     'FRZ-4: the unconditional "what the REMOTE already has" line'))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    bad = 0
    for label, passed, mutation in rows:
        print('  %-56s %s' % (label, 'ok' if passed else '*** FAILED ***'))
        if not passed:
            print('  %-56s   catches: %s' % ('', mutation))
            bad += 1
    print('  %d behavioural control(s), %d failing' % (len(rows), bad))
    return bad


def selftest():
    print('=' * 44)
    print('  frozen-baseline check - CONTROLS')
    print('=' * 44)
    bad = common.fire_suppress(_MUST_FIRE, _MUST_SUPPRESS, _grew, 'baseline growth')
    print('')
    print('  REMOVAL TRIGGER')
    bad += common.fire_suppress(_R_MUST_FIRE, _R_MUST_SUPPRESS, _owes, 'unreviewed removal')
    print('')
    print('  COVERAGE STATUS — only SATISFIED discharges')
    bad += common.fire_suppress(_S_MUST_FIRE, _S_MUST_SUPPRESS,
                                lambda st: not discharges(st), 'non-discharging status')
    # ⚠ IN `selftest()` DELIBERATELY, not behind a separate flag. `FRZ-3`'s whole finding was that
    # the mutation stayed green through `--selftest`, `check_checkers` and `guards.py` — all three
    # reach the checker HERE, so this is the one placement that closes all three at once.
    bad += selftest_behaviour()
    return bad


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    _b = None
    if '--base' in sys.argv:
        _i = sys.argv.index('--base')
        _b = sys.argv[_i + 1] if _i + 1 < len(sys.argv) else None
    sys.exit(run(block='--block' in sys.argv, base=_b,
                 record_to_ledger='--record' in sys.argv))
