#!/usr/bin/env python3
"""Generator for ZeroParadox/MANIFEST.md — the Lean-sources manifest.

Ground truth is the tree itself: every `ZeroParadox/**/*.lean` file is classified
**core** vs **experimental** by whether it carries the in-file `-- EXPERIMENTAL`
header (the same header the manifest documents), grouped by its domain folder, and
titled from its `# ...` module-docstring header. The editorial preamble (the
central-claim framing) is a fixed string, carried verbatim from the hand-written
original with only the reorg-dead filenames corrected.

So the manifest can no longer drift on a file move/rename/add — rerun it.

Run:  python .claude-local/build_manifest.py   (mirror to scripts/ per the scripts/ sync rule)
Out:  ZeroParadox/MANIFEST.md
"""
import os, re, sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(REPO, "ZeroParadox")
OUT = os.path.join(SRC, "MANIFEST.md")

PREAMBLE = """# ZeroParadox Lean sources - manifest

This folder holds the Lean 4 formalization for the Zero Paradox framework. It contains two kinds of file,
and this manifest says which is which so a reader knows what to read. Files in the **experimental** class
also carry a one-line `-- EXPERIMENTAL (branch scaffolding)` header at the top.

This material grew out of a broader exploratory arc that is kept privately; only the rigorous, review-cleared
Lean is surfaced here. The speculative interpretation behind it is deliberately not part of this repository.

The single best entry point is **`BottomCannotBe.lean`**: a machine-checked (`#check`-only) index that
gathers the established results about the framework's bottom element across every layer and organizes them
by a classification schema. Within this repository the shorthand for it is "Bottom-Meta". It declares
nothing of its own and only `#check`s already-proved results, so building it recompiles every result it
cites; it is a curated map of what is established, not a source of new claims.

**On the central claim (read this first).** The organizing thesis is that the bottom element recurs in the
same structural role across several domains. What is **proved** is the *membership* and the *recurrence of
the slot structure*. What is **not** proved, and is stated only as a conjecture/program, is that the various
bottoms are *one object*: they are provably distinct as structures (the "walls" results in the campaign).
The index above is where the precise line between proved and conjectural is kept.
"""

TITLE_RE = re.compile(r"^#\s+(.+?)\s*$")

def scan():
    """Return {folder: [(relpath, title, experimental_bool)]}."""
    out = {}
    for dp, _, files in os.walk(SRC):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dp, fn)
            rel = os.path.relpath(full, REPO).replace(os.sep, "/")
            parts = rel.split("/")
            folder = parts[1] if len(parts) >= 3 else "(root)"
            with open(full, encoding="utf-8") as f:
                lines = [ln.rstrip("\n") for ln in f]   # whole file: Meta files put the docstring after a ~140-line import block
            exp = any(ln.startswith("-- EXPERIMENTAL") for ln in lines[:3])
            title = None
            for ln in lines:                       # 1st choice: a markdown `# Title` (the common `/-! # ...` style)
                m = TITLE_RE.match(ln)
                if m:
                    title = m.group(1); break
            if title is None:                      # fallback: first prose line inside the leading /- or /-! block
                started = False
                for ln in lines:
                    s = ln.strip()
                    if not started:
                        if s.startswith("/-"):
                            started = True
                            after = s[3:].strip() if s.startswith("/-!") else s[2:].strip()
                            if after:
                                title = after.lstrip("# ").strip(); break
                        continue
                    if s and not s.startswith(("-", "#")):
                        title = s.lstrip("# ").strip(); break
            out.setdefault(folder, []).append((rel, title or fn, exp))
    return out

# folder -> human domain label
DOMAIN = {
    "Order": "Order / lattice (ZP-A, ZP-E)", "Valuation": "Valuation / number theory (ZP-B, ZP-F)",
    "Information": "Information (ZP-C)", "State": "State / Hilbert (ZP-D)",
    "Reals": "Reals (counterexamples)", "Category": "Category theory (ZP-G, ZP-H)",
    "Multihomed": "Multi-homed bridges (ZP-H)", "Settheory": "Set theory / AFA (ZP-J)",
    "Computability": "Computability (ZP-K, ZP-J)", "Ordinal": "Ordinals / proof theory (ZP-L, ZP-M, ZP-N)",
    "Algebra": "Algebra / wheel (ZP-J)", "Meta": "Meta / tooling (not framework content)",
    "Vendored": "Vendored external code (Mathlib / CGT)", "(root)": "Root",
}
ORDER = ["Order","Valuation","Information","State","Reals","Category","Multihomed","Settheory",
         "Computability","Ordinal","Algebra","(root)","Meta","Vendored"]

def section(data, want_exp):
    lines = []
    for folder in ORDER + [f for f in sorted(data) if f not in ORDER]:
        items = [t for t in data.get(folder, []) if t[2] == want_exp]
        if not items:
            continue
        lines.append(f"\n### {DOMAIN.get(folder, folder)}\n")
        for rel, title, _ in sorted(items):
            lines.append(f"- `{rel}` - {title}")
    return "\n".join(lines)

def main():
    data = scan()
    core = section(data, False)
    exp = section(data, True)
    ncore = sum(1 for v in data.values() for t in v if not t[2])
    nexp = sum(1 for v in data.values() for t in v if t[2])
    page = (PREAMBLE
            + f"\n## Core (finalized results - read these)\n"
            + "\nThe framework's reviewed, load-bearing Lean, organized by domain folder. "
            + "The formal layers ZP-A through ZP-P live here; `BottomCannotBe.lean` (Bottom-Meta) is the curated index over them.\n"
            + core
            + f"\n\n## Experimental (branch scaffolding - the lab notebook)\n"
            + "\nThese carry the `-- EXPERIMENTAL` header: the exploratory work the core results were distilled from, "
            + "kept for transparency. The load-bearing results among them are cited by `BottomCannotBe.lean`; "
            + "the rest are probes, dead ends, and honest negatives.\n"
            + exp
            + f"\n\n---\n\n*Generated by `build_manifest.py` from the Lean tree + each file's `-- EXPERIMENTAL` header. "
            + f"Rerun after adding, moving, or renaming a file. ({ncore} core, {nexp} experimental.)*\n")
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {OUT}  ({ncore} core, {nexp} experimental, {ncore+nexp} files)")

if __name__ == "__main__":
    main()
