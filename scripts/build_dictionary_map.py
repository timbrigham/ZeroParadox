#!/usr/bin/env python3
"""Generator for "The Bottom Element (⊥) — Dictionary and Map".

SSOT: MAP data from `build_bottom_matrix.py` (CELLS/SLOTS); apophatic entries + glosses below. Witness
theorem names are RESOLVED against the actual Lean source (`ZeroParadox/**/*.lean`) at generation time:
each resolvable name becomes a relative link `ZeroParadox/File.lean`; names that do not resolve are printed
as a warning. So the page cannot link a witness the Lean does not contain.

Assumes the output .md lives at the REPO ROOT (relative links point into `ZeroParadox/`).

MAP data (CELLS/SLOTS) is imported from build_bottom_matrix.py, an internal companion generator kept in
the private working folder and not mirrored to scripts/; this file is the one that emits the public page.

Run:  python .claude-local/build_dictionary_map.py   (active copy; also mirrored read-only to scripts/)
Out:  BOTTOMELEMENT.md at the repo root   (Mermaid + relative links render on GitHub)
"""
import sys, os, re
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
sys.path.insert(0, os.path.dirname(__file__))
from build_bottom_matrix import CELLS, SLOTS

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO_ROOT, "BOTTOMELEMENT.md")  # front-door reference at repo root (relative links resolve from here)

# --- Resolver: name -> "ZeroParadox/rel/path.lean" by scanning the actual Lean source ---
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z0-9_']+)")

def scan_declarations():
    index = {}
    for dp, _, files in os.walk(os.path.join(REPO_ROOT, "ZeroParadox")):
        for fn in files:
            if fn.endswith(".lean"):
                full = os.path.join(dp, fn)
                rel = os.path.relpath(full, REPO_ROOT).replace(os.sep, "/")
                try:
                    with open(full, encoding="utf-8") as f:
                        for line in f:
                            m = _DECL.match(line)
                            if m:
                                index.setdefault(m.group(1), rel)
                except Exception:
                    pass
    return index

INDEX = scan_declarations()
UNRESOLVED = []
OVERRIDDEN = []

# Manual overrides for witnesses that are NOT top-level declarations (so the scanner cannot
# find them) but DO live in a known local file — e.g. class fields. Kept explicit and reported
# so a hand-resolved link is never silently indistinguishable from a scanned one.
FIELD_OVERRIDE = {
    "unique_fp": "ZeroParadox/ZPJ_SelfApp.lean",  # class field AbstractSelfApp.unique_fp (SelfApp:69)
}

def link_witness(name):
    path = INDEX.get(name)
    if path:
        return f"[`{name}`]({path})"
    path = FIELD_OVERRIDE.get(name)
    if path:
        OVERRIDDEN.append(name)
        return f"[`{name}`]({path})"
    UNRESOLVED.append(name)
    return f"`{name}`"  # not a local declaration (Mathlib, a class field, etc.) — shown, not linked

def render_witnesses(names):
    return ", ".join(link_witness(n) for n in names) if names else "*meta (no Lean witness)*"

# --- Reading key 1: slot codes ---
SLOT_GLOSS = {
    "CANT":  "**cannot-have** - what ⊥ provably is NOT (its exclusions)",
    "NARR":  "**narrow** - ⊥ is a single, unique point",
    "MEAS":  "**measure** - some quantity becomes infinite exactly at ⊥",
    "REACH": "**reach** - ⊥ is what nearby points converge to (an attractor)",
    "INV":   "**inversion** - the map z↦1/z swaps ⊥ (which is 0) with infinity (the two poles of a Riemann sphere)",
    "CONC":  "**concurrency** - applying ⊥'s own operation returns ⊥ unchanged (a fixed point: operation and result coincide)",
    "SELF":  "**self-reference** - ⊥ is defined by referring to itself (a self-reproducing / self-containing object)",
    "GEN":   "**generation** - ⊥ generates the structure built above it (for example, the ordinal ε₀ generated from 0)",
    "DYN":   "**dynamics** - how ⊥ is approached over time and departed from irreversibly",
}

# --- Reading key 2: constructions (map rows) ---
CONSTRUCTION_GLOSS = {
    "Lat ⊥ (ZPA/ZPE)": "the abstract order bottom: ⊥ as the least element of the framework's lattice",
    "p-adic (ℚ₂/ℤ₂)": "the number 0 in the 2-adic numbers (the floor of the 2-adic distance)",
    "Info (ZPC)": "the information-theoretic bottom, where surprisal / information grows without bound",
    "#4 Kleisli (Fin 0)": "the empty type, as the initial object of a probability (Kleisli) category",
    "#5 Hilbert (zero obj/seam)": "the zero vector space, as the zero object of a linear category (the 'seam')",
    "#3 TopCat ({0} limit)": "the one-point space {0}, obtained as a topological limit of shrinking balls",
    "#2 Markov (attractor)": "the stationary distribution a random walk settles into",
    "Kleene (quine, ZPK)": "the self-reproducing program (Kleene fixed point) of computability",
    "ε₀ (ordinal, ZPL/M)": "the ordinal ε₀, generated from 0 by iterating omega-to-the-power",
    "selfApp (abstract ⊥)": "the abstract self-application ⊥: the unique fixed point of a self-map",
}

# --- Reading key 3: recurring terms ---
TERMS = [
    ("apophatic", "characterizing something by what it is NOT (definition by exclusion)"),
    ("μ / ν", "least fixed point (μ, built up from the floor) vs greatest fixed point (ν, closed down)"),
    ("Quine atom / Kleene quine", "a self-containing set (x = {x}) / a program that prints itself"),
    ("the snap", "the framework's discrete jump off ⊥ into the first structured state"),
    ("ε₀", "the ordinal reached by iterating omega-to-the-power from 0 (a proof-theoretic ceiling)"),
    ("v₂ → ∞", "the 2-adic valuation going to infinity at 0 (0 is infinitely divisible by 2)"),
]

# --- Dictionary: negative entries.  (id, description, [witness theorem names]) ---
APOPHATIC = [
    ("A1", "a Lean term or otherwise finitely written down (⊥ is descriptionless, so any written form is already a description of it)", []),
    ("A2", "anything that keeps time, space, description, measure or structure (that would be an *interpretation* of ⊥, not ⊥)", []),
    ("A3", "finite: ⊥ is by definition the point where every finite measure diverges to infinity", []),
    ("B1", "the same object as both the proof-theory floor and the attractor floor (one is well-founded, the other is not)",
     ["no_strictMono_real_to_ordinal", "simplex_antichain"]),
    ("B2", "the same object as a categorical initial bottom, if it is a topological limit bottom (their universal properties point opposite ways)",
     ["padic_bottom_not_initial", "split_kleisli_vs_hilbert"]),
    ("B4", "reached by a comparison that preserves the 'closed-down' (ν) structure - you can only get to ⊥ by forgetting that structure",
     ["faithful_iff_descending"]),
    ("B5", "unified with its self-referential face in a structure-preserving way - the two coincide only as a bare point",
     ["faces_iso_unique"]),
    ("C1", "forced to a single point as a Markov bottom (#2): a reducible chain settles into a whole family of distributions, not one",
     ["markov_node_no_universal_property"]),
    ("C3", "an *initial* object of the category of spaces (the p-adic floor behaves like a limit / terminal object, the opposite)",
     ["padic_bottom_not_initial"]),
    ("D1", "a *zero object* (both initial and terminal) of the Kleisli or p-adic categories",
     ["kleisli_bottom_not_zero", "padic_bottom_not_zero"]),
    ("D2", "a *greatest* element (it is the floor, not the top)", ["zpa_bot_not_greatest"]),
    ("D4", "an inhabited least-fixed-point for the identity functor: that least fixed point is provably empty",
     ["strict_fix_isEmpty", "fix_isEmpty_constructive"]),
    ("D5", "recovered by mapping the least fixed point onto the greatest: the comparison map is not onto",
     ["fixToCofix_not_surjective"]),
    ("D6", "reached by a non-contracting orbit: unit-norm and swap orbits provably do not converge to ⊥",
     ["unit_orbit_not_tendsto_zero", "swap_orbit_not_convergent"]),
]

# --- Dictionary: positive handles.  (slot, aspect, characterization, [witness names]) ---
POSITIVE = [
    ("narrow", "noun", "the single, unique pinned point", ["q2_unique_fp", "fB_bottom_is_limit"]),
    ("measure", "noun", "a quantity that becomes infinite exactly at ⊥", ["t2_diverges", "addVal_bot"]),
    ("reach", "verb", "an attractor: *contracting* orbits converge to ⊥ (not all orbits - see D6)",
     ["contraction_orbit_tendsto_zero"]),
    ("inversion", "verb", "the 0 = ∞ pole: the map z↦1/z swaps 0 and infinity",
     ["rInv_swaps", "inversion_reverses_filtration"]),
    ("concurrency", "hinge", "the fixed point where least and greatest coincide (operation = result)",
     ["unique_fp", "selfApp_bot_is_both_extremal"]),
    ("self-reference", "hinge", "the self-reproducing / self-containing fixed point (Quine / Kleene)",
     ["kleene_quine_is_bot", "quine_period_is_goedel"]),
    ("generation", "verb", "the floor generates the ceiling (ε₀ = the closure of 0 under omega-to-the-power)",
     ["epsilonZero_eq_nfp"]),
    ("dynamics", "verb", "approached as orbits reach it, and departed irreversibly (the snap)",
     ["t_snap_derived", "fC_no_return", "fullMix_not_injective"]),
]

def cell_mark(w):
    if not w:
        return ""
    if w.strip().endswith("*"):
        return "✓*"
    return "✓"

def render_table(rows, headers):
    out = ["| " + " | ".join(headers) + " |", "|" + "---|" * len(headers)]
    for r in rows:
        out.append("| " + " | ".join(r) + " |")
    return "\n".join(out)

def render_slot_gloss():
    return render_table([[k, SLOT_GLOSS[k]] for k, _ in SLOTS], ["code", "what it means"])

def render_construction_gloss():
    return render_table([[c, g] for c, g in CONSTRUCTION_GLOSS.items()], ["construction (map row)", "what it means"])

def render_terms():
    return render_table([[t, g] for t, g in TERMS], ["term", "plain meaning"])

def render_map():
    keys = [k for k, _ in SLOTS]
    rows = ["| construction | " + " | ".join(keys) + " |", "|---|" + ":--:|" * len(keys)]
    for c, d in CELLS.items():
        rows.append("| " + c + " | " + " | ".join(cell_mark(d.get(k)) for k in keys) + " |")
    return "\n".join(rows)

PAGE = """# The Bottom Element (⊥) - Dictionary and Map

*A dictionary and map of the framework's bottom element ⊥ - what it is, what it is not, and where each characterization is established, most with a machine-checked Lean witness linked to the source.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For the formal framework index and Lean verification, see [README](README.md). For plain-language introductions, companions, and reading paths, see [GUIDE](GUIDE.md). For the claim-by-claim status of every result, see the [Claims Ledger](CLAIMS.md).

---

## What this is

This is a **reference** for the framework's bottom element ⊥: a **dictionary** (what ⊥ is and is not) and a
**map** (where each characterization is established). It is a **beginning, not a resolution.** What is
*proved* is that each construction's bottom belongs to the family and that the slot structure recurs; that
the various bottoms are *one object* stays a conjecture - they are provably distinct as structures (the
"walls"). It closes a standing gap: a framework built on ⊥ that had not yet characterized ⊥ itself.

---

## Reading key (for a reader with no prior context)

**Slot codes** (the map columns, and the positive dictionary entries):

{slot_gloss}

**Constructions** (the map rows; the `#` numbers are node labels from the framework's bottom-diagram
comparison):

{construction_gloss}

**A few recurring terms:**

{terms}

---

## Dictionary

### ⊥ cannot be (characterization by exclusion)

{apophatic}

### ⊥ is (positive handles - the slots)

The handles sort by **aspect**: what ⊥ *is* (**noun**), what ⊥ *does* (**verb**), or **both at once**
(**hinge**). The hinge is ⊥'s signature: at the floor the two collapse - the fixed point that *is* a thing
and *acts on itself* in one step (operation = result). *This noun-and-verb reading, and the claim that they
collapse at ⊥, is the framework's interpretation; the slot witnesses below are proved, the lens over them is
not.*

{positive}

---

## Map - slot × construction

Where each characterization is established. `✓` = established, `✓*` = conditional/bridge, blank = **open
probe**. (The witnessing theorem - and whether it is proved here or cited from a library - is in the
dictionary above, with links to the Lean source.)

{map}

The blanks are the honest part: they are open probes, and two columns (**inversion**, **generation**) sit in
one construction each - structural facts (inversion is the p-adic / Riemann phenomenon; generation is the
build-up-from-the-floor side), not gaps to paper over.

---

## Structure diagrams

> **Sizing** (Mermaid auto-lays-out; the risk is sprawl, not overflow). Target: at most about 8 nodes, short
> labels, fits one screen. Flow/tree stays shallow; a hub/fan is 1 hub with up to about 6 short spokes.

### The μ / ν fork - ⊥ as the seam
*3 nodes, width 2, depth 2.*

```mermaid
flowchart TB
  mu["least fixed point (μ)<br/>built UP from ⊥ (initial, ε₀)"]
  nu["greatest fixed point (ν)<br/>closed DOWN to ⊥ (limit, attractor)"]
  seam(["⊥ = the seam<br/>(least and greatest coincide)"])
  mu --> seam
  nu --> seam
```

### Where ⊥ appears - the constructions
*7 nodes, hub-and-fan, depth 2. (That these are all one referent is the open conjecture, not shown as fact.)*

```mermaid
flowchart TB
  bot((("⊥")))
  bot --- p["p-adic floor<br/>0 in ℚ₂"]
  bot --- k["Kleisli initial<br/>empty type"]
  bot --- h["Hilbert zero object<br/>zero space"]
  bot --- e["ordinal generation<br/>ε₀ from 0"]
  bot --- q["Kleene quine<br/>self-reference"]
  bot --- m["Markov attractor<br/>stationary"]
```

---

*Generated from `bottom_cannot_be.md` and the matrix data by `build_dictionary_map.py`. Witness names are
resolved against the Lean source at generation time and link to the file that declares them; the `meta`
entries (marked as such) have no Lean witness. To update: edit a source and rerun. Mermaid and the links
render natively on GitHub.*
"""

def main():
    page = PAGE.format(
        slot_gloss=render_slot_gloss(),
        construction_gloss=render_construction_gloss(),
        terms=render_terms(),
        apophatic=render_table([[i, c, render_witnesses(ws)] for (i, c, ws) in APOPHATIC],
                               ["#", "⊥ cannot be...", "witness (links to Lean source)"]),
        positive=render_table([[s, a, c, render_witnesses(ws)] for (s, a, c, ws) in POSITIVE],
                              ["slot", "aspect", "characterization of ⊥", "witness (links to Lean source)"]),
        map=render_map(),
    )
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {OUT}")
    print(f"{len(INDEX)} declarations indexed · {len(APOPHATIC)} apophatic · {len(POSITIVE)} positive · "
          f"{len(CONSTRUCTION_GLOSS)} constructions · {len(CELLS)}x{len(SLOTS)} map")
    if OVERRIDDEN:
        print("OVERRIDDEN witnesses (linked via FIELD_OVERRIDE, not top-level decls): " + ", ".join(sorted(set(OVERRIDDEN))))
    if UNRESOLVED:
        print("UNRESOLVED witnesses (shown un-linked - check external/field/typo): " + ", ".join(sorted(set(UNRESOLVED))))
    else:
        print("all witnesses resolved (scanned or overridden)")

if __name__ == "__main__":
    main()
