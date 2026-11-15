#!/usr/bin/env python3
"""Corpus-wide verification report, for the public CI run summary.

Reads a `lake build` log plus THE BUILD'S OWN EXIT CODE, and emits Markdown saying
what the machine actually checked: whether the build succeeded, and the axiom
footprint of every declaration that records one. Nothing is written to the
repository - the log is CI's and regenerates from source on every run.

Generalizes scripts/minimal_core_report.py, which does this for one file.

DESIGN NOTE - three detectors, none of them sufficient alone, all measured.

1. EXIT STATUS, for "did it elaborate". An earlier version searched the log text for
   "error:" instead. That fails OPEN: Lean tags some diagnostics `error(lean.xxx):`
   which contains no `error:`; a build killed by the OOM killer writes none at all;
   an empty log trivially contains none. Each published "verified" and exited 0.

2. TEXT, for "is anything unproved" - and here the exit status is NO help at all:
   `lake env lean` on a file containing `sorry` **exits 0**. So for that property the
   scan is the only detector there is. An earlier draft of this note claimed the exit
   status was "the authority" and text merely "supporting evidence"; that is false in
   the one dimension a proof corpus cares about most.

3. PRESENCE OF EVIDENCE. A log with no footprints satisfies both of the above and
   proves nothing, so it fails closed rather than printing a credential over a blank
   table.

4. A FLOOR ON THE COUNT. CI restores a Lake build cache, and an up-to-date module
   contributes its footprints only by Lake REPLAYING its stored log. If replay ever
   dropped them, detector 3 would still pass on whatever was left. So the caller may
   pass a floor - the distinct-name count a cold build produced - and a count below it
   fails the report. The floor is a number someone lowers deliberately when
   declarations are removed; it is never derived from the run it judges.

5. A COLD CHECK. The floor is only as good as the build it was read from, so a run that
   is meant to be cold says so with `--require-cold <module-count>`, and then the report
   fails if any `ZeroParadox` or `ZeroParadox.*` module is `Replayed`, or if the number of
   distinct `ZeroParadox.*` submodules the log shows as `Built` differs from the count the
   caller passes (the `.lean` files under `ZeroParadox/`). "Cold" is measured from the log,
   not assumed from the workflow's cache settings. The root module `ZeroParadox` is left
   out of the `Built` count: in Complete Project job 131631685723 (a cold build of
   47666d37) all 259 submodules printed a `Built` line and the root module printed none.

Exits 0 if the build verified, 1 otherwise, so the report doubles as a gate -
but only because the caller passes the real exit code in. Wire it as:

    lake build 2>&1 | tee build.log
    BUILD_RC=${PIPESTATUS[0]}
    set -o pipefail
    python3 scripts/corpus_verification_report.py build.log "$BUILD_RC" "$FLOOR" \
      | tee -a "$GITHUB_STEP_SUMMARY"

Usage: corpus_verification_report.py <lake-build-log> <build-exit-code> [<footprint-floor>
       [--require-cold <module-count>]]
"""
import sys
import re
from collections import Counter

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

if len(sys.argv) < 3:
    sys.stderr.write(
        "usage: corpus_verification_report.py <lake-build-log> <build-exit-code>\n"
        "the exit code is REQUIRED - deciding success from log text fails open\n")
    sys.exit(2)

path, rc_arg = sys.argv[1], sys.argv[2]
try:
    build_rc = int(rc_arg)
except ValueError:
    sys.stderr.write(f"build-exit-code must be an integer, got {rc_arg!r}\n")
    sys.exit(2)
# None, not 0, when no floor is passed: "no floor given" and "a floor of zero" are
# different answers, and the report says which one it ran with.
floor = None
if len(sys.argv) > 3:
    try:
        floor = int(sys.argv[3])
    except ValueError:
        sys.stderr.write(f"footprint-floor must be an integer, got {sys.argv[3]!r}\n")
        sys.exit(2)
# The only accepted arguments after the floor are `--require-cold <module-count>`. Anything
# else is refused rather than ignored, so a misspelled flag cannot turn the cold check off
# unnoticed, and the count is required, so the cold check cannot run without it.
require_cold = False
expected_modules = None
if len(sys.argv) > 4:
    if sys.argv[4] != "--require-cold" or len(sys.argv) != 6:
        sys.stderr.write(f"expected `--require-cold <module-count>` after the floor, "
                         f"got {sys.argv[4:]!r}\n")
        sys.exit(2)
    try:
        expected_modules = int(sys.argv[5])
    except ValueError:
        sys.stderr.write(f"module-count must be an integer, got {sys.argv[5]!r}\n")
        sys.exit(2)
    # Zero is refused, not compared: an empty checkout would count 0 files, and a log
    # with 0 `Built` lines would then agree with it.
    if expected_modules < 1:
        sys.stderr.write(f"module-count must be at least 1, got {expected_modules}\n")
        sys.exit(2)
    require_cold = True

print(f"[report] reading {path}, build exit code {build_rc}", file=sys.stderr)
log = open(path, encoding="utf-8", errors="replace").read()
print(f"[report] {len(log)} chars, {log.count(chr(10))} lines", file=sys.stderr)

# --- axiom footprints ----------------------------------------------------
# Emitted by the `#print axioms` calls the corpus already carries. A warm cache does
# NOT suppress these: Lake REPLAYS cached module logs and re-emits them verbatim
# (measured 2026-08-08 - a fully warm build still produced 1270 footprint lines across
# 216 modules marked `Replayed`). So an empty table means something went wrong, never
# that the cache was warm.
# ⚠ `.+` NOT `[^']+`. A Lean name may END IN A PRIME, and `[^']+` cannot span it, so
# `floor_not_wellFounded_via_descent'` and friends were silently dropped - and since a
# dropped line is a dropped footprint, a dropped `sorryAx` went with it. `.+` is greedy
# and line-bounded, anchored by the trailing literal; measured, it captures 1270 of
# 1270 occurrences with zero over-capture.
#
# DEDUPLICATE BY NAME so the headline, the table and the <details> list share one unit.
# Occurrence-counting the total while name-counting the choice-free set made the report
# contradict its own arithmetic four lines apart.
axfree = sorted(set(re.findall(r"'(.+)' does not depend on any axioms", log)))
axdep = sorted({n: ", ".join(a.strip() for a in ax.split(","))
                for n, ax in
                re.findall(r"'(.+)' depends on axioms: \[([^\]]*)\]", log)}.items())
total = len(axfree) + len(axdep)
no_evidence = total == 0

# `sorryAx` in a footprint is the AUTHORITATIVE unproven-signal: it is what the
# kernel records, and unlike the `declaration uses `sorry`` warning it survives
# log reformatting. Check both - the warning catches a sorry in a declaration
# that has no `#print axioms` beside it.
sorried = sorted({n for n, ax in axdep if "sorryAx" in ax})
SORRY_WARNING = "declaration uses `sorry`"          # backticks, measured against the pin
# The raw-substring belt matters independently of the parse: if a footprint line is ever
# missed for any reason, this still catches the `sorryAx` in it. `sorryAx` never occurs
# in ordinary log furniture, unlike the bare word "sorry" (`nanoda-allow-sorry`).
has_sorry_warning = (SORRY_WARNING in log) or ("sorryAx" in log)

# How much of this build came from the cache. Lake prints one progress line per module,
# `Built X` when it elaborated X in this run and `Replayed X` when X was up to date and
# its stored log was re-emitted.
built = len(re.findall(r"\] Built ", log))
replayed = len(re.findall(r"\] Replayed ", log))
below_floor = floor is not None and total < floor
# The root module `ZeroParadox` and every `ZeroParadox.*` submodule, and nothing else
# (`ZeroParadoxFoo` does not match). A module line is `[i/n] Replayed X` or
# `[i/n] Built X (1.2s)`, so the name ends at whitespace or at the end of the line.
CORPUS_MODULE = r"ZeroParadox(?:\.\S+)?(?=\s|$)"
replayed_corpus = len(re.findall(r"\] Replayed " + CORPUS_MODULE, log, re.MULTILINE))
built_submodules = len(set(re.findall(r"\] Built (ZeroParadox\.\S+)(?=\s|$)", log,
                                      re.MULTILINE)))
replayed_cold = require_cold and replayed_corpus > 0
built_short = require_cold and built_submodules != expected_modules
not_cold = replayed_cold or built_short

ok = ((build_rc == 0) and not sorried and not has_sorry_warning and not no_evidence
      and not below_floor and not not_cold)
print(f"[report] rc={build_rc} sorried={len(sorried)} warn={has_sorry_warning} "
      f"evidence={not no_evidence} total={total} floor={floor} built={built} "
      f"replayed={replayed} replayed_corpus={replayed_corpus} "
      f"built_submodules={built_submodules} expected_modules={expected_modules} "
      f"require_cold={require_cold} -> ok={ok}", file=sys.stderr)
print(f"[report] {len(axfree)} axiom-free, {len(axdep)} with a footprint", file=sys.stderr)

by_footprint = Counter(ax for _n, ax in axdep)
# A `sorryAx` declaration is UNPROVED, not choice-free. Filtering on the absence of
# `Classical.choice` alone would publish unproved statements inside a purity inventory,
# which is the one property this table exists to certify.
choice_free = sorted(set(axfree) | {n for n, ax in axdep
                                    if "Classical.choice" not in ax and "sorryAx" not in ax})

# --- the report ----------------------------------------------------------
out = []
out.append("## The corpus — checked by machine, not by us ✓" if ok
           else "## The corpus — VERIFICATION FAILED ✗")
out.append("")

if not ok:
    if build_rc != 0:
        out.append(f"**The build did not succeed** (exit status {build_rc}). "
                   "The raw output is in the run log above.")
    if sorried:
        shown = ", ".join(f"`{n}`" for n in sorried[:20])
        more = " …" if len(sorried) > 20 else ""
        out.append(f"**{len(sorried)} declaration(s) depend on `sorryAx`** — they are "
                   f"stated, not proved: {shown}{more}")
    elif has_sorry_warning:
        out.append("**A declaration was left unproved** (Lean reported a `sorry`).")
    if no_evidence and build_rc == 0:
        out.append("**The build reported success and the log records no axiom footprints "
                   "at all** — so nothing was verified here. A warm cache still replays "
                   "them, so this means the log is truncated or the build did not run. "
                   "An absence of evidence is not a check.")
    if below_floor:
        out.append(f"**The log records {total} declarations with an axiom footprint, below "
                   f"the floor of {floor} set from a cold build.** Footprints went missing: "
                   "either the cache replay dropped them or declarations were removed. If "
                   "they were removed on purpose, lower the floor in "
                   "`.github/workflows/lean_action_ci.yml` in the same change.")
    if replayed_cold:
        out.append(f"**This run was meant to be a cold build, and the log shows "
                   f"{replayed_corpus} corpus module(s) `Replayed` from a build cache.** "
                   "Its count cannot be used to set or check the floor.")
    if built_short:
        out.append(f"**This run was meant to be a cold build, and the log shows "
                   f"{built_submodules} distinct `ZeroParadox.*` module(s) `Built`, "
                   f"against {expected_modules} `.lean` files under `ZeroParadox/`.** "
                   "Every corpus module must be elaborated in this run for its count to "
                   "set or check the floor.")
else:
    out.append(
        "Don't take our word for it. Lake exited 0, no declaration depends on `sorryAx`, "
        "and the table below is generated from this run's own output rather than "
        "maintained by hand.")
out.append("")

if no_evidence:
    sys.stdout.write("\n".join(out) + "\n")
    print("[report] no footprints - failing closed", file=sys.stderr)
    sys.exit(0 if ok else 1)

if not ok:
    out.append("⚠ The inventory below is from an **incomplete or failed run** and is "
               "partial. It is published for diagnosis, not as a credential.")
    out.append("")
out.append(f"**Declarations recording an axiom footprint in this build:** {total}, "
           f"of which **{len(choice_free)} do not use `Classical.choice`**. Counted by "
           "distinct name, and including library declarations the corpus checks "
           "alongside its own.")
out.append("")
floor_text = (f"floor **{floor}**, from a cold build" if floor is not None
              else "**no floor given**")
out.append(f"**Count check:** {total} against {floor_text}. Modules in this log: "
           f"{built} elaborated in this run, {replayed} replayed from the build cache.")
out.append("")
out.append("| footprint | count | means |")
out.append("|---|---:|---|")
def gloss(footprint: str) -> str:
    """Derive the gloss from the atoms present.

    Deliberately NOT a lookup table. A table over combinations is hand-maintained data
    that silently degrades to "see the run log" on the combination nobody listed - and
    measured 2026-08-08, the CI log and a full local build do not even contain the same
    set (`Classical.choice, Quot.sound` occurs locally and not in CI). Deriving it means
    a new combination is described correctly the first time it appears.
    """
    atoms = {a.strip() for a in footprint.split(",") if a.strip()}
    if not atoms:
        return "no axiom recorded"
    if "sorryAx" in atoms:
        return "⚠ NOT PROVED — `sorry` stands in for the proof"
    parts = []
    if "propext" in atoms:
        parts.append("propositional extensionality")
    if "Quot.sound" in atoms:
        parts.append("quotient soundness")
    if "Classical.choice" in atoms:
        parts.append("classical choice")
    extra = sorted(atoms - {"propext", "Quot.sound", "Classical.choice"})
    parts.extend(f"`{a}`" for a in extra)
    tail = "" if "Classical.choice" in atoms else "; choice-free"
    return (", ".join(parts) if parts else "none") + tail


if axfree:
    out.append(f"| *(none)* | {len(axfree)} | no axiom at all; choice-free |")
for fp, n in by_footprint.most_common():
    out.append(f"| `{fp}` | {n} | {gloss(fp)} |")
out.append("")

out.append(f"<details><summary>The {len(choice_free)} declarations that avoid "
           "<code>Classical.choice</code></summary>")
out.append("")
for name in sorted(choice_free):
    out.append(f"- `{name}`")
out.append("")
out.append("</details>")
out.append("")

out.append(
    "**Scope.** An axiom footprint records which axioms a proof reaches for — ordinarily "
    "`propext`, `Classical.choice` and `Quot.sound`, and `sorryAx` when a proof is missing "
    "altogether. It is not a claim that a theorem is interesting, correctly named, or "
    "states what its docstring says — and a declaration with an empty footprint may still "
    "rest on hypotheses or typeclass assumptions, which are not axioms.")

sys.stdout.write("\n".join(out) + "\n")
print(f"[report] wrote {len(out)} lines, exiting {0 if ok else 1}", file=sys.stderr)
sys.exit(0 if ok else 1)
