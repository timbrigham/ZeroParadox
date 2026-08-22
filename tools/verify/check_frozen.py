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


def at_head(rel):
    """The file's content at HEAD, or None if it does not exist there."""
    p = subprocess.run(['git', 'show', 'HEAD:%s' % rel], cwd=REPO, capture_output=True,
                       text=True, encoding='utf-8', errors='replace')
    return p.stdout if p.returncode == 0 else None


def check_one(name):
    """Returns (status, added, n_now, n_head). status is ok / GREW / NEW / gone."""
    rel = 'tools/verify/%s' % name
    disk = os.path.join(REPO, 'tools', 'verify', name)
    head = at_head(rel)
    if not os.path.exists(disk):
        # Draining a baseline to zero and deleting it is the SUCCESS condition, not a failure.
        return 'gone', set(), 0, len(entries(head)) if head is not None else 0
    now = entries(io.open(disk, encoding='utf-8-sig', errors='replace').read())
    if head is None:
        # ⚠ A frozen baseline that does not exist at HEAD is being CREATED. Every entry in it is an
        # addition, so this fails closed rather than treating "no prior version" as permission.
        return ('NEW', now, len(now), 0) if now else ('ok', set(), 0, 0)
    before = entries(head)
    added = now - before
    return ('GREW' if added else 'ok'), added, len(now), len(before)


def run(block=False):
    report.banner('frozen accepted-defect baselines', [
        ('purpose', 'the accepted-defect backlog may only SHRINK'),
        ('property', "today's set is a SUBSET of HEAD's — not merely the same size"),
        ('basis', 'git show HEAD:<path>, which the editor of the file does not control'),
        ('scope', '%d frozen file(s); decl/scope/pattern/whitelist are NOT debt and are excluded'
         % len(common.FROZEN_BASELINES)),
        ('mode', 'BLOCK' if block else 'report only (pass --block to enforce)'),
    ])
    bad, total_now, total_head = 0, 0, 0
    for name in sorted(common.FROZEN_BASELINES):
        status, added, n_now, n_head = check_one(name)
        total_now += n_now
        total_head += n_head
        delta = n_now - n_head
        print('  %-26s %-5s %5d entr%s (%+d)'
              % (name, status if status != 'ok' else 'ok', n_now,
                 'y' if n_now == 1 else 'ies', delta))
        if status in ('GREW', 'NEW'):
            bad += 1
            for a in sorted(added)[:5]:
                print('        + %s' % a[:110])
            if len(added) > 5:
                print('        + ... %d more' % (len(added) - 5))
    print('')
    # ⚠ THE TOTAL PRINTS ON EVERY RUN, CLEAN OR NOT. A debt figure that only surfaces when something
    # is wrong cannot show progress, and `selfheal.py`'s lesson is that a number reachable only from
    # the rarest command surfaces never. DOWN is the point of this file.
    print('  ACCEPTED-DEFECT BACKLOG: %d  (was %d at HEAD, %+d)'
          % (total_now, total_head, total_now - total_head))
    if bad:
        print('')
        print('  A frozen baseline GREW. Nothing is ever added to these again — fix the site, or if')
        print('  the finding is wrong then the CHECKER is wrong and that is a DEFECTS.md row, not a')
        print('  suppression. `python %s` in a checker refuses the write for the same reason.'
              % SELF)
    report.done('frozen accepted-defect baselines', bad == 0,
                'no frozen baseline grew' if bad == 0 else '%d baseline(s) grew' % bad)
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


def selftest():
    print('=' * 44)
    print('  frozen-baseline check - CONTROLS')
    print('=' * 44)
    return common.fire_suppress(_MUST_FIRE, _MUST_SUPPRESS, _grew, 'baseline growth')


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    sys.exit(run(block='--block' in sys.argv))
