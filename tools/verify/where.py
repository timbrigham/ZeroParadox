# -*- coding: utf-8 -*-
"""where.py — map a phrase in Tim's language to the subsystem folder to load before development.

WHY THIS EXISTS (2026-07-31). Measured this session: the failures were retrieval, not reasoning.
Targeted grep needs the right word and the words move; four sweeps missed a claim that changed
vocabulary each time. But the framework is small enough to READ: most subfolders are 5k-66k tokens,
and the conceptual spine (the CannotBe indexes + MANIFEST/CLAIMS/BOTTOMELEMENT/SNAP) is ~50k.

The point is NOT error-finding (that has its own discipline, and its unit is the rendered PDF).
The point is DEVELOPMENT: every real finding this session came from colliding two facts, and you
cannot collide facts you are fetching one at a time. Load the section, then think.

Scoring is distinctiveness, not raw frequency: a term counts for a folder in proportion to how
concentrated it is there. Tim's Engineer's Takes are weighted 3x, because his phrasing is the
input this is meant to accept, and his Takes are the closest thing in the repo to his language.

Usage:
    python tools/verify/where.py "it's a recursive algorithm, not a loop"
    python tools/verify/where.py --files "destructive acts bleed onto the infinity side"
    python tools/verify/where.py --spine          # what the always-load spine costs
"""
import collections
import glob
import io
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                            # noqa: E402

# ⚠⚠ `common.REPO`, NOT a hand-rolled dirname chain. The original was
# `dirname(dirname(abspath(__file__)))` — two levels up from the FILE, which is correct
# at depth 1 (the old private location, one level down) and WRONG at depth 2: from here it
# resolves to `REPO/tools`. The failure mode is the nasty one — it would glob `.lean`
# under `tools/`, find nothing, and return its NULL, which `R-EDITLEAN` itself calls
# UNINFORMATIVE. Broken would read as merely unhelpful, on the one command the manual
# requires before every Lean edit. `common.REPO` is `HERE.parent.parent` where `HERE` is
# the DIRECTORY, which is why every other tool in this bundle survives living here.
ROOT = str(common.REPO)

SPINE = [
    'ZeroParadox/BottomCannotBe.lean',
    'ZeroParadox/Order/SnapCannotBe.lean',
    'ZeroParadox/Ordinal/Epsilon0CannotBe.lean',
    'ZeroParadox/DiagonalFixedPoint.lean',
    'ZeroParadox/Category/ChoiceCannotBe.lean',
    'ZeroParadox/MANIFEST.md',
    'CLAIMS.md', 'BOTTOMELEMENT.md', 'SNAP.md',
]

STOP = set('''the a an and or of to in is are was were be been it its this that these those with for on at
by from as not no if then else we our you your i he she they them their there here what which who whom
whose when where why how all any both each few more most other some such only own same so than too very
can will just should now also into out up down over under again further once but do does did doing have
has had having would could may might must shall lean mathlib theorem lemma def instance structure class
proof proved file section note statement reading claim framework zeroparadox zp'''.split())


def toks(s):
    return [w for w in re.findall(r"[A-Za-z][A-Za-z0-9_']+", s.lower()) if w not in STOP and len(w) > 2]


def folder_profiles():
    """term -> {folder: weight}, weighted by distinctiveness; Tim's Takes count 3x."""
    per = collections.defaultdict(collections.Counter)
    sizes = {}
    for d in sorted(glob.glob(os.path.join(ROOT, 'ZeroParadox', '*/'))):
        name = 'ZeroParadox/' + os.path.basename(d.rstrip('\\/'))
        files = glob.glob(os.path.join(d, '**', '*.lean'), recursive=True)
        if not files:
            continue
        nbytes = 0
        for f in files:
            try:
                txt = io.open(f, encoding='utf-8', errors='replace').read()
            except Exception:
                continue
            nbytes += len(txt)
            per[name].update(toks(txt))
            m = re.search(r"## Engineer's Take(.*?)(\n---|\n## )", txt, re.S)
            if m:                                     # Tim's own language, weighted
                for _ in range(3):
                    per[name].update(toks(m.group(1)))
        sizes[name] = (len(files), nbytes)
    # invert with an idf-style distinctiveness factor
    docfreq = collections.Counter()
    for name, c in per.items():
        for t in c:
            docfreq[t] += 1
    n = len(per)
    prof = collections.defaultdict(dict)
    for name, c in per.items():
        tot = sum(c.values()) or 1
        for t, k in c.items():
            if docfreq[t] == n and k < 12:
                continue
            # Rarity DOMINATES. A term occurring in one folder must outweigh common words,
            # or a single decisive hit ("subtraction", in Order/Snap.lean once) is drowned by
            # "bottom" and "unique", which are everywhere. Measured 2026-07-31: linear idf
            # routed "no subtraction, unique to bottom" to State/ and missed Order/ entirely.
            rarity = math.log(1 + n / docfreq[t]) ** 3
            prof[t][name] = (k / tot) * rarity
    return prof, sizes


def takes_index():
    """filename -> Tim's Engineer's Take. His phrasing, attached to the file it describes.

    This is the signal that actually bridges the vocabulary gap. The Lean body says `cx`,
    `member`, `infinitude`; Tim says "bottom itself is infinitely complex". Only the Takes are
    written in the language the query arrives in.
    """
    out = {}
    for f in glob.glob(os.path.join(ROOT, 'ZeroParadox', '**', '*.lean'), recursive=True):
        try:
            txt = io.open(f, encoding='utf-8', errors='replace').read()
        except Exception:
            continue
        m = re.search(r"## Engineer's Take(.*?)(\n---|\n## )", txt, re.S)
        if m and len(m.group(1).strip()) > 60:
            out[os.path.relpath(f, ROOT).replace('\\', '/')] = m.group(1)
    return out


def closest_takes(q, k=3):
    idx = takes_index()
    df = collections.Counter()
    prof = {}
    for f, t in idx.items():
        c = collections.Counter(toks(t))
        prof[f] = c
        for w in c:
            df[w] += 1
    n = len(prof) or 1
    sc = collections.Counter()
    for w in toks(q):
        if w not in df:
            continue
        for f, c in prof.items():
            if w in c:
                sc[f] += (c[w] / (sum(c.values()) or 1)) * math.log(1 + n / df[w]) ** 3
    return sc.most_common(k), idx


def main():
    args = [a for a in sys.argv[1:]]
    show_files = '--files' in args
    args = [a for a in args if not a.startswith('--')]
    prof, sizes = folder_profiles()

    if '--spine' in sys.argv[1:]:
        tot = 0
        print('\nALWAYS-LOAD SPINE (the framework\'s own compression of itself):')
        for f in SPINE:
            p = os.path.join(ROOT, f)
            if os.path.exists(p):
                b = os.path.getsize(p); tot += b
                print('   %-46s ~%2.0fk tok' % (f, b / 4000))
        print('   %-46s ~%2.0fk tok' % ('TOTAL SPINE', tot / 4000))
        return

    if not args:
        print(__doc__)
        return

    q = ' '.join(args)
    score = collections.Counter()
    for t in toks(q):
        for folder, w in prof.get(t, {}).items():
            score[folder] += w

    print('\nquery: %r' % q)
    if not score:
        print('  no folder matched — try more specific vocabulary, or load the spine (--spine).')
        return
    print('\nload these, in order:')
    top = score.most_common(4)
    hi = top[0][1] or 1
    run = 0
    for folder, s in top:
        if s < hi * 0.18:
            break
        nf, nb = sizes.get(folder, (0, 0))
        run += nb
        print('   %-26s %3d files  ~%3.0fk tok   (relevance %.2f)' % (folder, nf, nb / 4000, s / hi))
        if show_files:
            for f in sorted(glob.glob(os.path.join(ROOT, folder, '**', '*.lean'), recursive=True)):
                print('        ' + os.path.relpath(f, ROOT).replace('\\', '/'))
    print('   %-26s            ~%3.0fk tok  + ~50k spine' % ('RUNNING TOTAL', run / 4000))

    hits, idx = closest_takes(q)
    if hits and hits[0][1] > 0:
        print("\nclosest Engineer's Takes (your own words, attached to the file):")
        for f, s2 in hits:
            first = ' '.join(idx[f].split())[:96]
            print('   %s' % f)
            print('        "%s..."' % first)


if __name__ == '__main__':
    main()
