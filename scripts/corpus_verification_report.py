#!/usr/bin/env python3
"""Corpus-wide verification report, for the public CI run summary.

Reads a `lake build` log plus THE BUILD'S OWN EXIT CODE, and emits Markdown saying
what the machine actually checked: whether the build succeeded, and the axiom
footprint of every declaration that records one. Nothing is written to the
repository - the log is CI's and regenerates from source on every run.

Generalizes scripts/minimal_core_report.py, which does this for one file.

DESIGN NOTE, and it is the whole point of the second argument. An earlier version
decided success by searching the log text for "error:". That fails OPEN in at
least three ways, all measured: Lean tags some diagnostics `error(lean.xxx):`
which does not contain `error:`; a build killed by the OOM killer writes no
`error:` at all; and an empty log trivially contains none. Each published
"verified, nothing left unproven" and exited 0. **The build's exit status is the
authority. Text is only ever supporting evidence.**

Exits 0 if the build verified, 1 otherwise, so the report doubles as a gate -
but only because the caller passes the real exit code in. Wire it as:

    lake build 2>&1 | tee build.log
    BUILD_RC=${PIPESTATUS[0]}
    set -o pipefail
    python3 scripts/corpus_verification_report.py build.log "$BUILD_RC" \
      | tee -a "$GITHUB_STEP_SUMMARY"

Usage: corpus_verification_report.py <lake-build-log> <build-exit-code>
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

print(f"[report] reading {path}, build exit code {build_rc}", file=sys.stderr)
log = open(path, encoding="utf-8", errors="replace").read()
print(f"[report] {len(log)} chars, {log.count(chr(10))} lines", file=sys.stderr)

# --- axiom footprints ----------------------------------------------------
# Emitted by the ~1250 `#print axioms` calls the corpus already carries. A warm
# cache does NOT suppress these: Lake REPLAYS cached logs and re-emits them
# verbatim (measured 2026-08-08 - a fully warm build still produced all 1270
# footprint lines, tagged `Replayed`). So an empty table means something went
# wrong, never that the cache was warm.
axfree = re.findall(r"'([^']+)' does not depend on any axioms", log)
axdep = [(n, ", ".join(a.strip() for a in ax.split(",")))
         for n, ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)]
total = len(axfree) + len(axdep)

# `sorryAx` in a footprint is the AUTHORITATIVE unproven-signal: it is what the
# kernel records, and unlike the `declaration uses `sorry`` warning it survives
# log reformatting. Check both - the warning catches a sorry in a declaration
# that has no `#print axioms` beside it.
sorried = sorted({n for n, ax in axdep if "sorryAx" in ax})
SORRY_WARNING = "declaration uses `sorry`"          # backticks, measured against the pin
has_sorry_warning = SORRY_WARNING in log

ok = (build_rc == 0) and not sorried and not has_sorry_warning
print(f"[report] rc={build_rc} sorried={len(sorried)} warn={has_sorry_warning} -> ok={ok}",
      file=sys.stderr)
print(f"[report] {len(axfree)} axiom-free, {len(axdep)} with a footprint", file=sys.stderr)

by_footprint = Counter(ax for _n, ax in axdep)
choice_free = [n for n in axfree] + [n for n, ax in axdep if "Classical.choice" not in ax]

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
        out.append(f"**{len(sorried)} declaration(s) depend on `sorryAx`** — they are "
                   "stated, not proved: " + ", ".join(f"`{n}`" for n in sorried[:20]))
    elif has_sorry_warning:
        out.append("**A declaration was left unproven** (Lean reported a `sorry`).")
elif total:
    out.append(
        "Don't take our word for it. Lake exited 0 and no declaration depends on `sorryAx`. "
        "The table below is generated from this run's own output, not maintained by hand.")
else:
    out.append("Lake exited 0 and no declaration depends on `sorryAx`.")
out.append("")

if total == 0:
    out.append("⚠ **This log records no axiom footprints at all.** The corpus carries over a "
               "thousand `#print axioms` calls and a warm cache still replays them, so an "
               "empty table means the log is truncated or the build did not run — not that "
               "there was nothing to check.")
    sys.stdout.write("\n".join(out) + "\n")
    sys.exit(0 if ok else 1)

out.append(f"**Declarations recording an axiom footprint:** {total}, "
           f"of which **{len(choice_free)} do not use `Classical.choice`**.")
out.append("")
out.append("| footprint | count | means |")
out.append("|---|---:|---|")
GLOSS = {
    "propext": "propositional extensionality only; choice-free",
    "Quot.sound": "quotient soundness only; choice-free",
    "propext, Quot.sound": "extensionality and quotients; choice-free",
    "propext, Classical.choice, Quot.sound": "the ordinary Mathlib footprint, including choice",
    "Classical.choice": "classical choice alone",
}
if axfree:
    out.append(f"| *(none)* | {len(axfree)} | depends on no axiom beyond Lean's core logic |")
for fp, n in by_footprint.most_common():
    out.append(f"| `{fp}` | {n} | {GLOSS.get(fp, 'see the run log above')} |")
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
    "**Scope.** An axiom footprint records which of Lean's three kernel axioms a proof "
    "reaches for. It is not a claim that a theorem is interesting, correctly named, or "
    "states what its docstring says — and a declaration with no footprint may still rest "
    "on hypotheses or typeclass assumptions, which are not axioms.")

sys.stdout.write("\n".join(out) + "\n")
print(f"[report] wrote {len(out)} lines, exiting {0 if ok else 1}", file=sys.stderr)
sys.exit(0 if ok else 1)
