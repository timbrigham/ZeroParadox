"""footprints.py -- MEASURE the axiom footprint of every declaration in the corpus.

WHY THIS EXISTS (2026-09-19). Three BEDROCK overclaims (`ZPK-BED-1..3`) are live in deposited
PDFs under permanent DOIs, and an attempt to fix them by rewriting the prose did not converge:
BEDROCK 3 -> 3 -> 4 across three gate rounds, with two of the last four findings written BY the
fix. Every one of those findings has the same shape:

    A UNIVERSAL QUANTIFIER OVER A SET OF DECLARATIONS, ASSERTED IN PROSE, NEVER ENUMERATED.

  * "all ZP-K theorems carry the standard foundational axioms"
  * "shared by all Mathlib computability results"
  * "`Classical.choice` is required at each diagonal step"

The reviewer's own line: *"One measurement catches all four -- enumerate the set the quantifier
ranges over and run `collectAxioms` on every member. None of the four is visible by reading."*

So this tool does not read prose. It RUNS `Lean.collectAxioms` on every constant in every
`ZeroParadox.*` module and writes the table. (`R-DEFECTCLASS`: prefer a detector whose verb is RUN.)

⛔⛔ THIS TOOL REFUTES. IT DOES NOT CONFIRM. READ THIS BEFORE QUOTING ANY OUTPUT.
  A REFUTED verdict is a POSITIVE FACT: a named declaration, measured, that makes the sentence
  false. You can rely on it.
  There is deliberately NO "not refuted" verdict, and it is not an oversight -- it was REMOVED on
  2026-09-19 (Tim's ruling) after two `/rely` rounds in which every attempt to make such a verdict
  safe introduced a new fail-open. "Not refuted" is an ABSENCE CLAIM over a set whose completeness
  nothing can check at read time, and `R-NOTINLIB` says an absence is never asserted -- it is
  "not located as of <date>, searched as follows". So that is what this prints.
  ⭐ THE SHAPE CHANGE WAS THE FIX. Round 1 made the violation sets correct; round 2 found the
  coverage counter counted the wrong object and that the query paths never read it. The lesson is
  not "add a third checker" -- it is that a tool which never claims completeness cannot fail open
  about completeness. DO NOT REINTRODUCE A CONFIRMING VERDICT.

HOW IT WORKS
  1. Generates a Lean file importing every module under `ZeroParadox/` (the umbrella root imports
     exactly ONE module -- `lakefile.toml` builds the rest through a `globs` entry -- so importing
     `ZeroParadox` alone would silently measure a fraction of the corpus).
  2. `lake env lean` it. A `run_cmd` walks `env.header.moduleData`, and for each constant declared
     in a `ZeroParadox.*` module calls `collectAxioms`, printing one TSV row.
  3. Parses those rows into `footprints.json` beside this file.

  The generated Lean file is written to a TEMP directory, never into the tree: a generated artifact
  in the repo is the defect `7ff3db98` was written to remove.

WHAT A ROW MEANS, AND IT IS EASY TO MISREAD
  `collectAxioms` follows the STATEMENT as well as the proof. A TYPE can carry an axiom, in which
  case NO proof of any statement mentioning it is clean. A footprint is therefore a fact about
  `(statement, proof)` together, never about the theorem's difficulty, and never on its own
  evidence that choice is NEEDED. See `R-COREOBJ` and `check_modal.py`.

  The pair that killed the "the cost rides on the statement's TYPE" redraft is at
  `ZeroParadox/Computability/Kleene.lean:410-415` --
      theorem da1_closed_concrete : IsQuineAtom (bot : MachinePhase) := da1_computational
      example                     : IsQuineAtom (bot : MachinePhase) :=
        @bot_is_quine_atom MachinePhase _ machinePhaseAFA
  Same type, two proofs. Verified by elaboration twice (`/rely` rounds 1 and 2): the THEOREM
  carries the full triple, the EXAMPLE reports "does not depend on any axioms".
  THE COST RIDES ON THE PROOF.

  ⛔ THE SECOND MEMBER IS THE `example`, NOT `bot_is_quine_atom`. An earlier version of this
  comment named the theorem. Elaborated 2026-09-19, they are not the same statement:
      da1_closed_concrete :              IsQuineAtom ZPSemilattice.bot
      bot_is_quine_atom   : forall {L} [ZPSemilattice L] [AFAStructure L], IsQuineAtom ...bot
  One is the GENERAL lemma, the other its INSTANTIATION -- and the difference between them is
  exactly the instance arguments, which is the "cost rides on the TYPE" reading the pair was cited
  to refute. Citing them as one statement argued the opposite of the intended point.

  ⚠⚠ AND THAT WITNESS IS STRUCTURALLY INVISIBLE TO THIS TOOL. The harvest walks
  `ModuleData.constNames`, and an anonymous `example` declares no constant, so it is never
  measured here. `R-TOLEAN` PREFERS that form ("it declares nothing, so it owes no `#print
  axioms` entry, no `ssot.json` row and no SJV sync"). Measured 2026-09-19 in four phrasings
  varied by axis: 97 `example` lines in the corpus sit outside this table. This is the single
  biggest reason a missing counterexample here means nothing.

Usage:
    footprints.py --build            # re-measure; writes footprints.json  (SLOW: full import)
    footprints.py --selftest         # check the table against recorded footprints
    footprints.py --module <pat>     # footprint distribution over matching modules
    footprints.py --decl <name>      # one declaration's footprint
    footprints.py --universal <pat>  # try to REFUTE the standard universals over a module set

Exit codes:  0 completed, nothing refuted  ·  1 could not run (no table, no match)  ·
             2 at least one universal REFUTED (a finding, not an error)
"""
import argparse
import datetime
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
from common import HERE, REPO, SRC  # noqa: E402

SELF = common.self_rel(__file__)
CACHE = HERE / 'footprints.json'

EXIT_OK, EXIT_CANNOT_RUN, EXIT_REFUTED = 0, 1, 2

# Declarations Lean generates from a `structure`/`inductive`/`def` rather than ones a human wrote.
# A prose universal ("all ZP-K theorems") never ranges over these, so they are recorded but tagged.
#
# ⚠ A SUFFIX TUPLE WAS NOT ENOUGH, and the first run proved it: `TriHalted.eq_1`, `carry.eq_1` and
# `EventuallyLeaf.below.step` were all reported as counterexamples to a claim about theorems. They
# are equation lemmas and recursor scaffolding -- true footprints attached to objects no sentence
# was ever about. Numbered families (`.eq_1`, `.match_3`) and INFIXES (`.below.step`) both need a
# pattern, so this is a regex on the whole name rather than a list of endings.
_FROM_INDUCTIVE = (
    'mk', 'rec', 'recOn', 'casesOn', 'below', 'brecOn', 'ibelow', 'binductionOn',
    'noConfusion', 'noConfusionType', 'ctorIdx', 'toCtorIdx', 'sizeOf_spec', 'injEq',
    'inj', 'induct', 'elim',
)
# Generated by a DEFINITION (equation lemmas, match arms, extracted proofs).
_FROM_DEFINITION = (r'eq_\d+', r'match_\d+', r'proof_\d+', 'eq_def', 'fun_cases',
                    '_sunfold', '_unfold', 'ofNat')

AUTO_PATTERN = re.compile(
    r'(?:^|\.)(' + '|'.join(_FROM_INDUCTIVE + _FROM_DEFINITION) + r')(?:\.|$)')
_INDUCTIVE_SEGMENTS = frozenset(_FROM_INDUCTIVE)


def _is_auto(name: str, rows: dict, parent_kind: str) -> bool:
    """Is this name one Lean generated, rather than one a human wrote?

    ⚠ THE NAME ALONE IS NOT ENOUGH, and shipping it that way ate two real definitions:
    `ZeroParadox.mk` (`ZeroParadox/Algebra/WheelFrac.lean:48`) and `NatOrdinal.rec`
    (`ZeroParadox/Vendored/NaturalOps.lean:166`). The regex matched whole dot-delimited
    segments, and `ZeroParadox` is a NAMESPACE while `NatOrdinal` is a `def` -- neither has a
    parent that could have generated it.

    ⚠⚠ AND THE FIRST FIX FOR THAT RESOLVED THE PARENT AGAINST THIS TABLE, which holds only
    `ZeroParadox.*`. So a generated name whose parent lives in MATHLIB was tagged NOT-auto and
    re-entered every violation set: `/rely` round 2 measured 4 spurious reclassifications
    (`ContinuousMap.comp.eq_1`, `CategoryTheory.Limits.constCocone.eq_1`, `NONote.repr.eq_1`,
    `Partrec2.eq_1`), and on one set `ContinuousMap.comp.eq_1` became the SOLE counterexample to
    two universals. A filter that silently drops real declarations and one that silently adds
    fake ones are the same defect wearing opposite signs.

    So the parent is resolved BY LEAN, against the whole environment including Mathlib
    (`parent_kind`, the harvest's fifth column), for the common case where the generated segment
    is the LAST one. Where it is an INFIX (`X.below.step`) Lean's prefix is not the parent we
    want, and that case still resolves against `rows` -- i.e. within `ZeroParadox.*` only. Stated
    rather than hidden: that residue is a known, bounded gap, not a verified absence.
    """
    m = AUTO_PATTERN.search(name)
    if not m:
        return False
    parent = name[:m.start()]
    if not parent:
        return False
    is_last_segment = name[m.end():] == ''
    if is_last_segment:
        if parent_kind == '-':
            return False           # Lean says no such parent exists anywhere. A human wrote it.
        if m.group(1) in _INDUCTIVE_SEGMENTS:
            return parent_kind in ('induct', 'ctor')
        return True
    prow = rows.get(parent)
    if prow is None:
        return False
    if m.group(1) in _INDUCTIVE_SEGMENTS:
        return prow['kind'] in ('induct', 'ctor')
    return True


HARVEST_TEMPLATE = '''{imports}

open Lean Elab Command

run_cmd do
  let env <- getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  for h : i in [0:mods.size] do
    let m := mods[i]!
    if (`ZeroParadox).isPrefixOf m || m == `ZeroParadox then
      let mut cnt := 0
      for n in data[i]!.constNames do
        if !n.isInternal then
          let ax <- collectAxioms n
          let kind := match env.find? n with
            | some (.thmInfo _)   => "thm"
            | some (.axiomInfo _) => "axiom"
            | some (.defnInfo _)  => "def"
            | some (.inductInfo _) => "induct"
            | some (.ctorInfo _)  => "ctor"
            | some (.opaqueInfo _) => "opaque"
            | some (.quotInfo _)  => "quot"
            | some (.recInfo _)   => "rec"
            | none                => "?"
          -- The parent resolved against the WHOLE environment, Mathlib included. Python cannot
          -- do this: its table holds only `ZeroParadox.*`, so a Mathlib parent reads as absent.
          let pkind := match env.find? n.getPrefix with
            | some (.inductInfo _) => "induct"
            | some (.ctorInfo _)   => "ctor"
            | some _               => "other"
            | none                 => "-"
          IO.println s!"FP\\t{{n}}\\t{{m}}\\t{{kind}}\\t{{String.intercalate "," (ax.toList.map toString)}}\\t{{pkind}}"
          cnt := cnt + 1
      -- ⛔ PRINTED *AFTER* THE LOOP, AND CARRYING THE COUNT. Both halves were defects.
      -- `/rely` round 2: the marker used to be printed BEFORE the loop, so it proved a module was
      -- ENTERED, never that its declarations were EMITTED -- truncating stdout after the last
      -- marker still wrote a table at "221 of 221 modules" with no complaint. And the blind spot
      -- is OCCUPIED: 8 of 221 modules genuinely emit zero rows (`AxiomProfile`,
      -- `DiagonalFixedPoint`, and all five `*CannotBe.lean` indexes, which are `#check`-only and
      -- declare nothing). So "correctly empty" and "truncated" returned the same value.
      -- That is `R-ZERONULL` exactly. The COUNT is what separates them: the driver checks that
      -- the per-module counts SUM to the rows it actually parsed.
      IO.println s!"MOD\\t{{m}}\\t{{cnt}}"
'''


def modules() -> list[str]:
    """Every module under ZeroParadox/, as a Lean module name.

    NOT the umbrella's import closure: `ZeroParadox.lean` imports one module and `lakefile.toml`
    picks the rest up through `globs = ["ZeroParadox.+"]`. Measured 2026-09-19: 1 import, 221
    files. Reading the umbrella would have measured under half a percent of the corpus and
    reported a clean table.
    """
    out = []
    for p in sorted(SRC.rglob('*.lean')):
        rel = p.relative_to(REPO).with_suffix('')
        out.append('.'.join(rel.parts))
    return out


def build(verbose: bool = True) -> dict:
    mods = modules()
    if not mods:
        # R-ZERONULL: an empty module list is NOT an empty corpus, it is a broken derivation.
        # Returning `{}` here would be indistinguishable from a corpus with no axioms anywhere.
        raise SystemExit(f'{SELF}: FAIL -- no modules found under {SRC}. Refusing to write an '
                         f'empty table that would read as "measured, nothing found".')
    if verbose:
        print(f'{SELF}: importing {len(mods)} modules; running collectAxioms on every constant.')
    src = HARVEST_TEMPLATE.format(imports='\n'.join(f'import {m}' for m in mods))
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / 'AxiomHarvest.lean'
        f.write_text(src, encoding='utf-8')
        proc = subprocess.run(['lake', 'env', 'lean', str(f)],
                              cwd=REPO, capture_output=True, text=True, encoding='utf-8',
                              errors='replace')
    if proc.returncode != 0:
        print(proc.stdout[-4000:])
        print(proc.stderr[-4000:], file=sys.stderr)
        raise SystemExit(f'{SELF}: FAIL -- the harvest did not elaborate (exit {proc.returncode}).')

    rows, declared, emitted, dupes = {}, {}, {}, []
    malformed = 0
    for ln in proc.stdout.splitlines():
        if ln.startswith('MOD\t'):
            p = ln.split('\t')
            if len(p) != 3 or not p[2].isdigit():
                malformed += 1
                continue
            declared[p[1]] = int(p[2])
            continue
        if not ln.startswith('FP\t'):
            continue
        parts = ln.split('\t')
        if len(parts) != 6:
            # ⚠ COUNTED, NOT SKIPPED. `continue` alone discarded 3000 malformed rows in silence
            # during the /rely trial and the table still wrote, still passed selftest, still
            # exited 0. A dropped row is missing evidence; a dropped row nobody counted is
            # missing evidence that reports as complete.
            malformed += 1
            continue
        _, name, mod, kind, ax, pkind = parts
        # EMISSIONS, counted before the dict can hide one. `rows` is keyed by NAME, so a repeated
        # name silently collapses to a single entry -- which is how the per-module count first
        # fired: four modules "emitted fewer rows than they counted" when in fact every row
        # arrived and some shared a key. Comparing Lean's count against UNIQUE NAMES asked a
        # different question than "did the stream survive", and only one of those is truncation.
        emitted[mod] = emitted.get(mod, 0) + 1
        if name in rows:
            dupes.append(name)
        rows[name] = {
            'module': mod,
            'kind': kind,
            'axioms': [a for a in ax.split(',') if a],
            '_pkind': pkind,
        }
    if not rows:
        raise SystemExit(f'{SELF}: FAIL -- the harvest elaborated but emitted no rows. That is a '
                         f'broken probe, not a corpus without declarations.')
    if malformed:
        raise SystemExit(f'{SELF}: FAIL -- {malformed} malformed harvest row(s). The output format '
                         f'moved under this parser; every dropped row is a declaration NOT '
                         f'measured, and a partial table reads exactly like a complete one.')

    # ⛔ COVERAGE, IN BOTH DIRECTIONS AND BY COUNT.
    expected, walked = set(mods), set(declared)
    missing, extra = sorted(expected - walked), sorted(walked - expected)
    if missing:
        raise SystemExit(
            f'{SELF}: FAIL -- {len(missing)} of {len(expected)} modules never reported: '
            + ', '.join(missing[:5]) + (f' ... and {len(missing) - 5} more'
                                        if len(missing) > 5 else ''))
    if extra:
        # `/rely` round 2 (O4): `walked - expected` was unchecked, so a harvest could report 222
        # modules beside a module_count of 221 and write silently. A module the corpus does not
        # contain means the two sides are measuring different things.
        raise SystemExit(f'{SELF}: FAIL -- the harvest reported {len(extra)} module(s) not on '
                         f'disk: {", ".join(extra[:5])}')
    # THE TRUNCATION CHECK: every row Lean printed must have reached this parser. Compared against
    # EMISSIONS, not unique names -- see the note where `emitted` is incremented.
    mismatched = sorted(m for m in declared if declared[m] != emitted.get(m, 0))
    if mismatched:
        raise SystemExit(
            f'{SELF}: FAIL -- {len(mismatched)} module(s) emitted fewer rows than they counted, '
            f'so the stream was cut mid-module: '
            + ', '.join(f'{m} said {declared[m]} got {emitted.get(m, 0)}'
                        for m in mismatched[:4]))

    # SECOND PASS: `_is_auto` needs the whole table for the infix case.
    for name, row in rows.items():
        row['auto'] = _is_auto(name, rows, row.pop('_pkind'))

    table = {
        'declarations': rows,
        # PROVENANCE, so `load()` can tell a complete table from a truncated one WITHOUT trusting
        # a count the table wrote about itself. `row_count` is cross-checked against the actual
        # number of entries, and `modules` against the corpus on disk.
        'row_count': len(rows),
        'emitted': sum(emitted.values()),
        # Names Lean printed more than once. Recorded rather than silently collapsed: the dict
        # keeps the LAST, so a duplicate means one measurement was discarded and the table holds
        # fewer rows than the corpus emitted. Surfaced by the per-module count on its first run.
        'duplicate_names': sorted(set(dupes)),
        'modules': sorted(expected),
        'built': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
    }
    CACHE.write_text(json.dumps(table, indent=1, sort_keys=True), encoding='utf-8')
    if verbose:
        print(f'{SELF}: wrote {len(rows)} declarations across {len(expected)} modules '
              f'to {common.self_rel(CACHE)}')
        if dupes:
            print(f'{SELF}: {sum(emitted.values())} rows emitted, {len(set(dupes))} name(s) '
                  f'emitted more than once: {", ".join(sorted(set(dupes))[:4])}'
                  + (' ...' if len(set(dupes)) > 4 else ''))
    return table


def load() -> dict:
    """Read the table, and REFUSE one that cannot account for itself.

    ⛔ THIS CHECK IS THE POINT, AND ITS ABSENCE WAS A FAIL-OPEN. `/rely` round 2: the coverage
    check ran only inside `build()`, while every path a human actually invokes -- `--selftest`,
    `--universal`, `--decl` -- came through here and read whatever JSON was on disk. A table of
    8 rows out of 3053 passed the controls and then reported a universal unrefuted that the full
    table refutes with 45 counterexamples. The field was written and never read.

    ⚠ WHAT THIS CATCHES, AND WHAT IT DOES NOT -- mutation-tested 2026-09-19, four mutations:
      RED   a truncated table (rows fewer than `row_count`)
      RED   a STALE table (its `modules` no longer match the corpus on disk)
      RED   a table with no provenance fields at all (written by an older build)
      GREEN a table forged SELF-CONSISTENTLY -- 8 rows, `row_count` 8, `modules` intact
    The last is not closed and is stated rather than hidden. It is not reachable by accident:
    truncation, a crashed harvest and a moved corpus each trip one of the first three, and the
    build-side per-module emission counts catch a cut stream before the file is ever written.
    Producing it means hand-editing the JSON into a consistent lie. The mitigation is that
    `--universal` prints the table's size and the matched set's size on every run, so a forged
    table announces itself as "1 declarations over ..." -- which is also why the scope line is
    not decoration and must not be trimmed.
    """
    if not CACHE.exists():
        raise SystemExit(f'{SELF}: no measurement on disk. Run `{SELF} --build` first. '
                         f'(An absent table is not an empty one.)')
    try:
        t = json.loads(CACHE.read_text(encoding='utf-8'))
    except json.JSONDecodeError as e:
        raise SystemExit(f'{SELF}: FAIL -- the table is not readable JSON ({e}). Re-run --build.')
    for key in ('declarations', 'row_count', 'modules', 'built'):
        if key not in t:
            raise SystemExit(f'{SELF}: FAIL -- the table has no `{key}`. It predates the '
                             f'provenance fields, or was written by something else. Re-run '
                             f'--build; do not read a table that cannot say what it covers.')
    if len(t['declarations']) != t['row_count']:
        raise SystemExit(f'{SELF}: FAIL -- the table holds {len(t["declarations"])} rows and '
                         f'claims {t["row_count"]}. It was truncated after it was written.')
    on_disk = set(modules())
    recorded = set(t['modules'])
    if on_disk != recorded:
        raise SystemExit(
            f'{SELF}: FAIL -- the table covers {len(recorded)} modules and the corpus now has '
            f'{len(on_disk)}. It is STALE: {len(on_disk - recorded)} module(s) added, '
            f'{len(recorded - on_disk)} removed since it was built at {t["built"]}. Re-run '
            f'--build. A table that predates a module cannot refute anything about it.')
    return t


def _select(table: dict, pat: str, include_auto: bool, kind: str | None = None) -> dict:
    """The set a quantifier ranges over.

    ⚠ `kind` is LOAD-BEARING, not a convenience. A prose universal says "all ZP-K THEOREMS", and a
    structure field, a class, an equation lemma or a `.below.step` recursor is not a theorem. Left
    unfiltered, this function refutes such a sentence with objects the sentence never quantified
    over -- a true measurement about the WRONG OBJECT, which is the defect class this whole tool
    exists to remove. Name the kind the sentence means.
    """
    rx = re.compile(pat)
    return {n: r for n, r in table['declarations'].items()
            if rx.search(r['module'])
            and (include_auto or not r['auto'])
            and (kind is None or r['kind'] == kind)}


def report_module(pat: str, include_auto: bool, kind: str | None) -> int:
    sel = _select(load(), pat, include_auto, kind)
    if not sel:
        print(f'{SELF}: no declarations matched module pattern /{pat}/. '
              f'That is a fact about the PATTERN, not about the corpus.')
        return EXIT_CANNOT_RUN
    buckets = {}
    for n, r in sel.items():
        buckets.setdefault(tuple(sorted(r['axioms'])), []).append(n)
    print(f'{SELF}: {len(sel)} declarations over /{pat}/ '
          f'({"including" if include_auto else "excluding"} auto-generated)')
    for ax, names in sorted(buckets.items(), key=lambda kv: -len(kv[1])):
        label = ', '.join(ax) if ax else '(no axioms)'
        print(f'  {len(names):5d}  {label}')
        for n in sorted(names)[:6]:
            print(f'           {n}')
        if len(names) > 6:
            print(f'           ... and {len(names) - 6} more')
    return EXIT_OK


def report_universal(pat: str, include_auto: bool, kind: str | None) -> int:
    """Try to REFUTE the universals prose keeps asserting. Never confirm one.

    A refutation is a named declaration, measured. Failing to find one is reported as what it is
    -- a search that came back empty, with its scope stated -- and never as the sentence being
    true. See the module docstring: the confirming verdict was REMOVED, deliberately.
    """
    table = load()
    sel = _select(table, pat, include_auto, kind)
    if not sel:
        print(f'{SELF}: no declarations matched /{pat}/ -- nothing measured, nothing concluded.')
        return EXIT_CANNOT_RUN
    scope = (f'{len(sel)} declarations over modules /{pat}/'
             + (f', kind={kind}' if kind else ', ALL KINDS (structures and projections included)')
             + ('' if include_auto else ', excluding auto-generated'))
    print(f'{SELF}: {scope}')
    print(f'{SELF}: table = {table["row_count"]} declarations across {len(table["modules"])} '
          f'modules, built {table["built"]}')
    print()

    # ⛔ THE VIOLATION SET OF A UNIVERSAL IS ITS NEGATION, NOT THE NEAREST SET TO HAND. The first
    # version used `clean` -- axioms EMPTY -- for two of the three claims, and both were wrong in
    # the fail-open direction. A theorem carrying `[propext]` does not carry the standard triple
    # and does not carry choice, so it refutes BOTH, and `clean` cannot see it. Measured by /rely
    # round 1: on a set where every member carries `[propext]`, this printed
    # `carry Classical.choice : 0` and then, three lines later, "not refuted" for "choice is
    # required at each" -- self-contradictory inside twenty lines of its own output.
    TRIPLE = {'propext', 'Classical.choice', 'Quot.sound'}
    claims = (
        ('"all ... carry the standard foundational axioms"',
         sorted(n for n, r in sel.items() if not TRIPLE.issubset(set(r['axioms'])))),
        ('"... is choice-free" / "no ... carries choice"',
         sorted(n for n, r in sel.items() if 'Classical.choice' in r['axioms'])),
        ('"Classical.choice is required at each ..."',
         sorted(n for n, r in sel.items() if 'Classical.choice' not in r['axioms'])),
    )
    refuted = 0
    for claim, viol in claims:
        if viol:
            refuted += 1
            print(f'  REFUTED  {claim}')
            for n in viol[:8]:
                print(f'             counterexample: {n}')
            if len(viol) > 8:
                print(f'             ... and {len(viol) - 8} more')
        else:
            # `R-NOTINLIB`: "not located as of <date>, searched as follows" -- never "absent".
            print(f'  NO COUNTEREXAMPLE LOCATED  {claim}')
            print(f'             searched: {scope}')
            print(f'             table built {table["built"]}')
        print()

    # ⛔⛔ THIS BLOCK STAYS ASCII-ONLY, AND THAT IS A CORRECTNESS REQUIREMENT RATHER THAN A STYLE
    # PREFERENCE. Measured 2026-09-21 (/rely): these were the ONLY two printed lines in this file
    # carrying non-ASCII (a `⚠` here and a `§` below), so under a cp1252 stdout they were the only
    # output that could fail — and the thing that died was THE SAFETY FENCE ITSELF. The claim rows
    # above, some reading `NO COUNTEREXAMPLE LOCATED`, had already printed; this disclaimer then
    # raised `UnicodeEncodeError: 'charmap' codec can't encode character '⚠'` and the reader was
    # left with an unqualified absence result. `R-TRUNC` makes that the DEFAULT way to run this tool
    # (redirect to a file and read it), and redirection is exactly when stdout stops being a
    # UTF-8 console. `DC-45`: two distinguishable states rendered identically and the safe one was
    # assumed. ⚠ IT WAS MASKED IN THE MEASURING SESSION by `PYTHONIOENCODING=utf-8:surrogateescape`
    # while `locale.getpreferredencoding()` was cp1252 — so whether the fence survives depended on
    # an environment variable nobody declares. Do not reintroduce a glyph on any PRINTED line here.
    print('  /!\\ NO COUNTEREXAMPLE LOCATED IS NOT A VERIFICATION, AND THIS TOOL WILL NOT SAY IT IS.')
    print('    Three reasons it can come back empty while the sentence is still false:')
    print('    1. Anonymous `example`s declare no constant and are INVISIBLE here (97 in the')
    print('       corpus, measured 2026-09-19). `R-TOLEAN` actively prefers that form.')
    print('    2. The set above is what the PATTERN matched, which may not be the set the')
    print('       sentence quantifies over. Read the scope line and check it yourself.')
    print('    3. A footprint follows the STATEMENT as well as the proof, so it never shows a')
    print('       theorem NEEDS an axiom. Necessity takes a reduction to a taboo, not a')
    print('       measurement -- `ZeroParadox/Category/ChoiceCannotBe.lean` section IV.')
    return EXIT_REFUTED if refuted else EXIT_OK


# CONTROLS. Footprints this corpus records INDEPENDENTLY of this tool, in prose written before it
# existed. They are the control on the MEASUREMENT: if `collectAxioms` is being called on the wrong
# environment, these stop matching.
#
# ⛔ THEY DO NOT PROVE COVERAGE, AND AN EARLIER VERSION OF THIS COMMENT CLAIMED THEY DID.
# They live in 6 modules of 221, so a table containing only them passes every one. Coverage is
# `build()`'s per-module counts and `load()`'s provenance check -- a different property, proved a
# different way. `/rely` round 1 demonstrated the confusion by exploiting it.
#
# Sources, each read at the file:
#   ZeroParadox/AxiomProfile.lean  ss 0, I        -- lines 67, 71, 94, 96
#   ZeroParadox/Category/ChoiceCannotBe.lean  s I -- t_snap_derived, "no axioms at all"
#   ZeroParadox/Ordinal/SyntacticCollapse.lean    -- "[propext] or cleaner on every theorem"
CONTROLS = {
    'ZeroParadox.da1_closed_concrete':          ['Classical.choice', 'Quot.sound', 'propext'],
    'ZeroParadox.bot_is_quine_atom':            [],
    'ZeroParadox.t_snap_derived':               [],
    'ZeroParadox.AFAStructure.bot_self_mem':    [],
    'ZeroParadox.t_exec':                       [],
    'ZeroParadox.wem_of_fixedPointFree':        ['Quot.sound', 'propext'],
    'ZeroParadox.fixedPointFree_of_nontrivial': ['Classical.choice', 'Quot.sound', 'propext'],
    'ZeroParadox.synCollapse_epsN':             ['propext'],
}
CONTROL_FLOOR = 8   # `/rely` round 2 (O5): `CONTROLS = {}` printed `PASS -- 0/0` and returned 0.


def selftest() -> int:
    if len(CONTROLS) < CONTROL_FLOOR:
        raise SystemExit(f'{SELF}: FAIL -- {len(CONTROLS)} controls, floor is {CONTROL_FLOOR}. '
                         f'An empty or thinned control set passes vacuously; that is the shape '
                         f'that got a neutered push gate to print 13/13 ok.')
    table = load()['declarations']
    bad = []
    for name, expect in CONTROLS.items():
        row = table.get(name)
        if row is None:
            bad.append(f'{name}: MISSING from the table entirely')
        elif sorted(row['axioms']) != sorted(expect):
            bad.append(f'{name}: measured {sorted(row["axioms"])}, corpus records {sorted(expect)}')
    print(f'{SELF}: {len(CONTROLS)} controls, each an axiom footprint this corpus recorded in '
          f'prose before this tool existed. They check the MEASUREMENT, never the coverage.')
    for line in bad:
        print(f'  FAIL  {line}')
    if bad:
        print(f'{SELF}: FAIL -- {len(bad)}/{len(CONTROLS)}. Either the harvest is measuring the '
              f'wrong thing, or a footprint genuinely MOVED. Both need a human; neither is a '
              f'reason to edit this list.')
        return EXIT_CANNOT_RUN
    print(f'{SELF}: PASS -- {len(CONTROLS)}/{len(CONTROLS)} match.')
    return EXIT_OK


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--build', action='store_true', help='re-measure the whole corpus')
    ap.add_argument('--selftest', action='store_true',
                    help='check the table against independently recorded footprints')
    ap.add_argument('--module', metavar='REGEX', help='footprint distribution over matching modules')
    ap.add_argument('--decl', metavar='NAME', help='one declaration')
    ap.add_argument('--universal', metavar='REGEX',
                    help='try to REFUTE the standard universals over a module set')
    ap.add_argument('--auto', action='store_true', help='include auto-generated declarations')
    ap.add_argument('--kind', choices=['thm', 'def', 'axiom', 'induct', 'ctor', 'opaque', 'rec'],
                    help='restrict to one declaration kind -- use `thm` for a claim about THEOREMS')
    a = ap.parse_args()

    if a.build:
        build()
        return selftest()
    if a.selftest:
        return selftest()
    if a.decl:
        r = load()['declarations'].get(a.decl)
        if r is None:
            print(f'{SELF}: `{a.decl}` is not in the measured table. Either it does not exist, or '
                  f'the table predates it -- re-run --build before concluding absence.')
            return EXIT_CANNOT_RUN
        ax = ', '.join(r['axioms']) if r['axioms'] else '(no axioms)'
        print(f'{a.decl}\n  module: {r["module"]}\n  kind:   {r["kind"]}\n  axioms: {ax}')
        return EXIT_OK
    if a.module:
        return report_module(a.module, a.auto, a.kind)
    if a.universal:
        return report_universal(a.universal, a.auto, a.kind)
    ap.print_help()
    return EXIT_OK


if __name__ == '__main__':
    sys.exit(main())
