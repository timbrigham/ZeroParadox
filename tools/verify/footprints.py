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
`ZeroParadox.*` module and writes the table. A universal claim is then settled by a query against
that table, not by a seventh redraft. (`R-DEFECTCLASS`: prefer a detector whose verb is RUN.)

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

  Measured, and it is the counterexample that killed the "the cost rides on the TYPE" redraft:
  two proofs of the identical statement `IsQuineAtom (bot : MachinePhase)` differ. The pair is at
  `ZeroParadox/Computability/Kleene.lean:410-415` --
      theorem da1_closed_concrete : IsQuineAtom (bot : MachinePhase) := da1_computational
      example                     : IsQuineAtom (bot : MachinePhase) :=
        @bot_is_quine_atom MachinePhase _ machinePhaseAFA
  The THEOREM carries the full triple; the EXAMPLE, at the same type, carries none.
  THE COST RIDES ON THE PROOF.

  ⛔ THE SECOND MEMBER IS THE `example`, NOT `bot_is_quine_atom`, AND THE FIRST VERSION OF THIS
  COMMENT NAMED THE THEOREM. Elaborated 2026-09-19, they are not the same statement:
      da1_closed_concrete :              IsQuineAtom ZPSemilattice.bot
      bot_is_quine_atom   : forall {L} [ZPSemilattice L] [AFAStructure L], IsQuineAtom ...bot
  One is the GENERAL lemma, the other its INSTANTIATION -- and the difference between them is
  exactly the instance arguments, which is the "cost rides on the TYPE" reading the pair was cited
  to refute. Citing them as one statement argued the opposite of the intended point. The corpus
  had it right and the `example` on the line below the theorem is the whole reason it is there.

  ⚠⚠ AND THAT WITNESS IS STRUCTURALLY INVISIBLE TO THIS TOOL. The harvest walks
  `ModuleData.constNames`, and an anonymous `example` declares no constant, so it is never
  measured here. `R-TOLEAN` PREFERS that form ("it declares nothing, so it owes no `#print
  axioms` entry, no `ssot.json` row and no SJV sync"), and ~98 `example` lines in the corpus are
  outside this table for exactly that reason. **So a universal this tool reports as not refuted
  may still be refuted by an `example` it cannot see.** Check the `example`s by hand, or say the
  scope out loud (`R-NOTINLIB`: name the set you searched).

Usage:
    footprints.py --build            # re-measure; writes footprints.json  (SLOW: full import)
    footprints.py --module <pat>     # footprint distribution over matching modules
    footprints.py --decl <name>      # one declaration's footprint
    footprints.py --universal <pat>  # the three standard universals, tested over a module set
"""
import argparse
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

# Declarations Lean generates from a `structure`/`inductive`/`def` rather than ones a human wrote.
# A prose universal ("all ZP-K theorems") never ranges over these, so they are recorded but tagged.
#
# ⚠ A SUFFIX TUPLE WAS NOT ENOUGH, and the first run proved it: `TriHalted.eq_1`, `carry.eq_1` and
# `EventuallyLeaf.below.step` were all reported as counterexamples to a claim about theorems. They
# are equation lemmas and recursor scaffolding -- true footprints attached to objects no sentence
# was ever about. Numbered families (`.eq_1`, `.match_3`, `.proof_2`) and INFIXES (`.below.step`)
# both need a pattern, so this is a regex on the whole name rather than a list of endings.
# Generated BY AN INDUCTIVE OR STRUCTURE. Lean emits these only when the parent is one.
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


def _is_auto(name: str, rows: dict) -> bool:
    """Is this name one Lean generated, rather than one a human wrote?

    ⚠ THE NAME ALONE IS NOT ENOUGH, and shipping it that way ate two real definitions:
    `ZeroParadox.mk` (`ZeroParadox/Algebra/WheelFrac.lean:48`) and `NatOrdinal.rec`
    (`ZeroParadox/Vendored/NaturalOps.lean:166`) were both tagged auto-generated by a pure
    regex, because it matched whole dot-delimited segments and `ZeroParadox` is a NAMESPACE
    while `NatOrdinal` is a `def`. Neither has a parent that could have generated it.

    So ask the environment instead of the spelling: a generated name has a PARENT DECLARATION
    that generates it, and for the inductive family that parent must actually be an inductive.
    Found by /rely 2026-09-19.
    """
    m = AUTO_PATTERN.search(name)
    if not m:
        return False
    parent = name[:m.start()]
    if not parent:
        return False
    prow = rows.get(parent)
    if prow is None:
        # No parent declaration exists, so nothing generated this. A human wrote it.
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
      -- One marker per module WALKED, so the driver compares what the harvest actually covered
      -- against the module list it asked for. Without this the table's only coverage figure is
      -- `len(mods)` off the filesystem, computed BEFORE lake runs -- a number about the caller's
      -- intent, never about the measurement.
      IO.println s!"MOD\\t{{m}}"
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
          IO.println s!"FP\\t{{n}}\\t{{m}}\\t{{kind}}\\t{{String.intercalate "," (ax.toList.map toString)}}"
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

    rows = {}
    walked = set()
    malformed = 0
    for ln in proc.stdout.splitlines():
        if ln.startswith('MOD\t'):
            walked.add(ln.split('\t', 1)[1])
            continue
        if not ln.startswith('FP\t'):
            continue
        parts = ln.split('\t')
        if len(parts) != 5:
            # ⚠ COUNTED, NOT SKIPPED. `continue` alone discarded 3000 malformed rows in silence
            # during the /rely trial and the table still wrote, still passed selftest, still
            # exited 0. A dropped row is missing evidence; a dropped row nobody counted is
            # missing evidence that reports as complete.
            malformed += 1
            continue
        _, name, mod, kind, ax = parts
        rows[name] = {
            'module': mod,
            'kind': kind,
            'axioms': [a for a in ax.split(',') if a],
        }
    if not rows:
        raise SystemExit(f'{SELF}: FAIL -- the harvest elaborated but emitted no rows. That is a '
                         f'broken probe, not a corpus without declarations.')
    # SECOND PASS: `_is_auto` needs the whole table, because it asks whether a PARENT declaration
    # exists and what kind it is. It cannot be decided while the rows are still being read.
    for name, row in rows.items():
        row['auto'] = _is_auto(name, rows)
    if malformed:
        raise SystemExit(f'{SELF}: FAIL -- {malformed} malformed harvest row(s). The output format '
                         f'moved under this parser; every dropped row is a declaration NOT '
                         f'measured, and a partial table reads exactly like a complete one.')

    # ⛔ THE COVERAGE CHECK. This is what makes a PARTIAL harvest fail closed. Measured by /rely
    # 2026-09-19: the eight CONTROLS live in 6 modules of 213, so a table holding 8 rows out of
    # 3053 printed `PASS -- 8/8 match.` and exited 0 -- the exact failure the controls' own
    # comment claimed they caught. Controls prove the measurement is RIGHT where it ran. Only
    # this proves it RAN EVERYWHERE. They are different properties and neither implies the other.
    expected = set(mods)
    missing = sorted(expected - walked)
    if missing:
        raise SystemExit(
            f'{SELF}: FAIL -- the harvest walked {len(walked)} of {len(expected)} modules. '
            f'{len(missing)} never reported: {", ".join(missing[:5])}'
            + (f' ... and {len(missing) - 5} more' if len(missing) > 5 else ''))
    table = {'declarations': rows, 'module_count': len(mods), 'modules_walked': len(walked)}
    CACHE.write_text(json.dumps(table, indent=1, sort_keys=True), encoding='utf-8')
    if verbose:
        print(f'{SELF}: wrote {len(rows)} declarations to {common.self_rel(CACHE)}')
    return table


def load() -> dict:
    if not CACHE.exists():
        raise SystemExit(f'{SELF}: no measurement on disk. Run `{SELF} --build` first. '
                         f'(An absent table is not an empty one.)')
    return json.loads(CACHE.read_text(encoding='utf-8'))


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
        return 1
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
    return 0


def report_universal(pat: str, include_auto: bool, kind: str | None) -> int:
    """Test the three universals prose keeps asserting, against the measured set.

    Each is reported with its COUNTEREXAMPLE, named. A universal with a named counterexample is
    not a wording problem and must not be redrafted into a weaker one (`R-REVALIDATE`).
    """
    sel = _select(load(), pat, include_auto, kind)
    if not sel:
        print(f'{SELF}: no declarations matched /{pat}/ -- nothing measured, nothing concluded.')
        return 1
    print(f'{SELF}: set = modules /{pat}/'
          + (f', kind={kind}' if kind else ', ALL KINDS (structures and projections included)'))
    clean = sorted(n for n, r in sel.items() if not r['axioms'])
    choice = sorted(n for n, r in sel.items() if 'Classical.choice' in r['axioms'])
    # ⛔ THE VIOLATION SET OF A UNIVERSAL IS ITS NEGATION, NOT THE NEAREST SET TO HAND. The first
    # version of this function used `clean` -- axioms EMPTY -- for two of the three claims, and
    # both were wrong in the fail-open direction. A theorem carrying `[propext]` does not carry
    # the standard triple and does not carry choice, so it refutes BOTH of those universals, and
    # `clean` cannot see it. Measured by /rely 2026-09-19: on the set where every member carries
    # `[propext]`, this printed `carry Classical.choice : 0` and then, three lines later, "not
    # refuted" for "choice is required at each" -- self-contradictory inside twenty lines of its
    # own output, in the one direction that lets a false universal through.
    #
    # Negate the claim, then collect. Each list below is literally "the members that make the
    # sentence false".
    TRIPLE = {'propext', 'Classical.choice', 'Quot.sound'}
    not_triple = sorted(n for n, r in sel.items() if not TRIPLE.issubset(set(r['axioms'])))
    no_choice = sorted(n for n, r in sel.items() if 'Classical.choice' not in r['axioms'])
    print(f'{SELF}: {len(sel)} declarations over /{pat}/')
    print(f'  carry NO axioms at all       : {len(clean)}')
    print(f'  carry Classical.choice       : {len(choice)}')
    print(f'  do NOT carry the full triple : {len(not_triple)}')
    print(f'  do NOT carry Classical.choice: {len(no_choice)}')
    print()
    for claim, viol in (
            ('"all ... carry the standard foundational axioms"', not_triple),
            ('"... is choice-free" / "no ... carries choice"', choice),
            ('"Classical.choice is required at each ..."', no_choice),
    ):
        if viol:
            print(f'  REFUTED  {claim}')
            for n in viol[:8]:
                print(f'             counterexample: {n}')
            if len(viol) > 8:
                print(f'             ... and {len(viol) - 8} more')
        else:
            print(f'  not refuted over this set  {claim}')
    print()
    print('  A universal not refuted over THIS set is not thereby true over the set the prose')
    print('  names. Check that the pattern above is the set the sentence quantifies over.')
    return 0


# CONTROLS. Eight footprints this corpus records INDEPENDENTLY of this tool, in prose written
# before it existed. They are the control on the harvest: if `collectAxioms` is being called on the
# wrong environment, or the module walk is silently measuring a fraction of the corpus, these stop
# matching. Two of them are the pair that killed the "the cost rides on the statement's TYPE"
# redraft -- `da1_closed_concrete` and `bot_is_quine_atom` prove the IDENTICAL statement
# `IsQuineAtom (bot : MachinePhase)` and have OPPOSITE footprints. Sources, each read at the file:
#   ZeroParadox/AxiomProfile.lean  ss 0, I           -- lines 67, 71, 94, 96
#   ZeroParadox/Category/ChoiceCannotBe.lean  s I    -- t_snap_derived, "no axioms at all"
#   ZeroParadox/Ordinal/SyntacticCollapse.lean       -- "[propext] or cleaner on every theorem"
#   .claude-local/DEFECTS.md  ZPK-BED-1, ZPK-BED-2   -- bot_is_quine_atom, AFAStructure.bot_self_mem
CONTROLS = {
    'ZeroParadox.da1_closed_concrete':        ['Classical.choice', 'Quot.sound', 'propext'],
    'ZeroParadox.bot_is_quine_atom':          [],
    'ZeroParadox.t_snap_derived':             [],
    'ZeroParadox.AFAStructure.bot_self_mem':  [],
    'ZeroParadox.t_exec':                     [],
    'ZeroParadox.wem_of_fixedPointFree':      ['Quot.sound', 'propext'],
    'ZeroParadox.fixedPointFree_of_nontrivial': ['Classical.choice', 'Quot.sound', 'propext'],
    'ZeroParadox.synCollapse_epsN':           ['propext'],
}


def selftest() -> int:
    table = load()['declarations']
    bad = []
    for name, expect in CONTROLS.items():
        row = table.get(name)
        if row is None:
            bad.append(f'{name}: MISSING from the table entirely')
        elif sorted(row['axioms']) != sorted(expect):
            bad.append(f'{name}: measured {sorted(row["axioms"])}, corpus records {sorted(expect)}')
    print(f'{SELF}: {len(CONTROLS)} controls, each an axiom footprint this corpus recorded in prose')
    print(f'{SELF}: before this tool existed.')
    for line in bad:
        print(f'  FAIL  {line}')
    if bad:
        print(f'{SELF}: FAIL -- {len(bad)}/{len(CONTROLS)}. Either the harvest is measuring the '
              f'wrong thing, or a footprint genuinely MOVED. Both need a human; neither is a '
              f'reason to edit this list.')
        return 1
    print(f'{SELF}: PASS -- {len(CONTROLS)}/{len(CONTROLS)} match.')
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--build', action='store_true', help='re-measure the whole corpus')
    ap.add_argument('--selftest', action='store_true',
                    help='check the table against eight independently recorded footprints')
    ap.add_argument('--module', metavar='REGEX', help='footprint distribution over matching modules')
    ap.add_argument('--decl', metavar='NAME', help='one declaration')
    ap.add_argument('--universal', metavar='REGEX', help='test the standard universals over a set')
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
            return 1
        ax = ', '.join(r['axioms']) if r['axioms'] else '(no axioms)'
        print(f'{a.decl}\n  module: {r["module"]}\n  kind:   {r["kind"]}\n  axioms: {ax}')
        return 0
    if a.module:
        return report_module(a.module, a.auto, a.kind)
    if a.universal:
        return report_universal(a.universal, a.auto, a.kind)
    ap.print_help()
    return 0


if __name__ == '__main__':
    sys.exit(main())
