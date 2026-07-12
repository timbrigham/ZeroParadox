#!/usr/bin/env python3
"""Generator for "The Binary Snap (⊥ → ε₀) - Dictionary and Map".

Companion to build_dictionary_map.py (BOTTOMELEMENT.md). That file maps the *object* ⊥ (the noun);
this file maps the *transition* off it - the snap (the verb). Same discipline: the is / is-not /
proved-vs-open catalogue is hand-curated flat data below, and every witness theorem name is RESOLVED
against the actual Lean source (`ZeroParadox/**/*.lean`) at generation time - each resolvable name becomes
a relative link `ZeroParadox/File.lean`; names that do not resolve are printed as a warning. So the page
cannot link a witness the Lean does not contain, and a renamed/moved/deleted witness fails LOUD.

SSOT note: unlike BOTTOMELEMENT (whose map matrix comes from build_bottom_matrix.py), the snap catalogue is
inline flat data here. The Lean corpus is the single source of truth for witness existence. A future revision
may drive the catalogue from the ssot.json snap ontology tags once that tagging matures (Option B); this is
Option A - the proven flat-data + corpus-resolution pattern.

Assumes the output .md lives at the REPO ROOT (relative links point into `ZeroParadox/`).

Run:  python .claude-local/build_snap_map.py   (active copy; also mirrored read-only to scripts/)
Out:  SNAP.md at the repo root   (Mermaid + relative links render on GitHub)
"""
import sys, os, re
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO_ROOT, "SNAP.md")  # front-door reference at repo root (relative links resolve from here)

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

def link_witness(name):
    path = INDEX.get(name)
    if path:
        return f"[`{name}`]({path})"
    UNRESOLVED.append(name)
    return f"`{name}`"  # not a local declaration (Mathlib, a class field, etc.) - shown, not linked

def render_witnesses(names):
    return ", ".join(link_witness(n) for n in names) if names else "*meta (no Lean witness)*"

def render_table(rows, headers):
    out = ["| " + " | ".join(headers) + " |", "|" + "---|" * len(headers)]
    for r in rows:
        out.append("| " + " | ".join(r) + " |")
    return "\n".join(out)

# --- Auto-linker for witness names embedded in prose (the rosetta) ---
# NB: do NOT wrap a decl name in manual backticks in the prose below - the linker adds its own, and a
# pre-backticked token yields broken nested markdown. Write decl names bare; the linker handles them.
_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
def _decl_shaped(name):
    return "_" in name or re.search(r"[A-Z]", name[1:]) is not None
def link_in_text(text):
    def repl(m):
        name = m.group(0)
        if _decl_shaped(name) and name in INDEX:
            return link_witness(name)
        return name
    return _TOKEN.sub(repl, text or "")

# --- Dictionary: positive faces.  (aspect, characterization, [witness names]) ---
# The snap is fundamentally a VERB - the action off the floor - so most faces are verbs; the endpoints
# (what departs, what is reached) are the nouns.
IS_FACES = [
    ("theorem", "the *forced* transition off ⊥ into the minimum non-⊥ state: the join c₀ ∨ c₁ = c₁ is a valid transition, and c₀, c₁ are provably distinct in both directions. AX-1 (the Binary Snap) is no longer an axiom, it is derived",
     ["t_snap_derived"]),
    ("verb", "*one-way*: the departure from ⊥ does not reverse. No join can return to a strictly lower state (algebraic form), and the 2-adic and Kleisli faces prove the same irreversibility topologically and categorically",
     ["t_snap_irreversible", "c3_irreversible", "fC_no_return"]),
    ("verb", "a *change of frame*, valuation face (probe): the same ω-tower descends to the 2-adic floor 0 (ε₀ realized as ⊥) and, through the Riemann-sphere inversion that swaps 0 ↔ ∞, rises to ∞ (ε₀ realized as the ceiling). The inversion is the passage between the two charts",
     ["snap_is_frameflip", "snap_frameflip_tower_tendsto_infty"]),
    ("verb", "a *change of frame*, category face (probe): the categorical seam realizes the same frame-flip via the zero object of the linear functor",
     ["catseam_is_frameflip"]),
    ("verb", "a *change of frame*, order-theoretic universal (choice-free): order-duality swaps the fork's two closures (least fixed point ↔ greatest fixed point), and the fork collapses to the diagonal fixed point exactly when the map has a unique fixed point. This is the standard lfp/gfp duality, bundled - the domain-independent shape the valuation and category faces realize concretely",
     ["fork_is_frameflip", "fork_collapse_iff"]),
    ("verb", "*generation*: the floor generates the ceiling - ε₀ is the closure of 0 under omega-to-the-power (the least fixed point of α ↦ ω^α)",
     ["epsilonZero_eq_nfp"]),
    ("verb", "*constructive, from below, choice-free*: on ordinal notations, each tower term strictly exceeds the last, ω^x has no fixed point, and the tower is strictly monotone - all `propext`-only, free even of `Quot.sound`",
     ["exp_lt_term", "omegaPow_no_fixedpoint", "tower_strictMono"]),
    ("noun", "the ceiling reached, *co-witnessed*: ε₀ stands with the 2-adic limit and the machine snap in one triangle",
     ["zpm_triangle"]),
    ("noun", "*what departs*: the floor the snap leaves - the three-name identity (Quine atom = order-bottom ⊥ = join-identity, axiom-free), extended to the Kleene self-reproducing fixed point",
     ["t_exec", "t_comp", "kleene_quine_is_bot"]),
]

# --- Dictionary: negative entries.  (description, [witness names or empty=meta/open]) ---
IS_NOT = [
    ("*one mechanism across categories*. The per-domain frame-flips share a shape, not a single categorical map. In Set no nontrivial total type carries a Lawvere fixed-point witness (Cantor), so the lattice and 2-adic faces are provably not Set-level Lawvere instances - their ⊥ is a posited fixed point sharing the diagonal shape. The computability face is instead a genuine recursion fixed point, but in the effective category, where the diagonal is not computable. Heterogeneous categories, heterogeneous verdicts: what unifies the faces is the diagonal shape, not one mechanism - order-theoretic, not categorical. A proved obstruction, not a gap",
     ["nontrivial_lattice_no_witness", "q2_no_witness", "computability_face_fixedPoint"]),
    ("*numerically one transition across its carriers*. That the valuation, categorical, order, and computability snaps are the same object is a modeling commitment (MC-1), a type boundary - `x = y` across distinct categories is not a well-formed proposition. The faces share the diagonal-fixed-point shape; that they are literally one object is offered, not proved",
     []),
    ("*a physical, temporal, or causal event*. The framework is silent on physics. The snap is an order and derivation transition, not a process unfolding in time; which specific state emerges first is outside its scope",
     []),
    ("*dependent on a snap-specific axiom*. T-SNAP is derived from the bottom axiom A4 (the join identity ∀ x, ⊥ ∨ x = x) and the framework's computational commitments. No snap axiom appears anywhere in the development",
     ["t_snap_derived"]),
    ("*proved to be a choice-free minimal ceiling*. The from-below snap on ordinal notations is choice-free, but ε₀ as the least fixed point via the syntax-to-semantics bridge (`tower_NF`) inherits `Classical.choice`. Whether the minimality is choice-free at the notation level is open",
     []),
]

def render_rosetta():
    body = """## The short version: the snap, tiered by confidence

The snap is the framework's one theorem - the forced, one-way departure from ⊥ into the first structured state ε₀ - and its central *action*. Everything provable is checkable: clone the repo and run `#print axioms <name>`.

**Proved - the snap is forced, and adds no axiom.** T-SNAP (t_snap_derived): the transition ⊥ → ε₀ (the minimum non-⊥ state) is a derived consequence of the bottom axiom A4 and the framework's computational commitments, not an assumption. The Binary Snap that earlier layers posited as AX-1 is a theorem; no snap-specific axiom appears anywhere.

**Proved - the snap is one-way.** It does not reverse: no join returns to a strictly lower state (t_snap_irreversible, algebraic), and the same irreversibility is proved topologically in the 2-adics (c3_irreversible) and categorically in the probability functor (fC_no_return). ⊥ is a source, not a round trip.

**Proved - a frame-change in each domain, and an order-theoretic universal.** Over any complete lattice the order-duality frame-change swaps the fork's two closures and the fork collapses at the diagonal fixed point (fork_is_frameflip); this is the standard lfp/gfp duality, choice-free, claimed as no novelty. It is realized concretely in the valuation face (snap_is_frameflip: one ω-tower is ε₀-as-⊥ in the encoding chart and ε₀-as-ceiling through the 0 ↔ ∞ inversion) and the category face (catseam_is_frameflip). (The abstract cross-domain reading - that these are one and the same frame-change - stays a conjecture; see below.)

**Proved - the ceiling, reached by a choice-free snap from below.** ε₀ is the closure of 0 under omega-to-the-power (epsilonZero_eq_nfp); on ordinal notations the snap climbs from below with no choice (exp_lt_term, omegaPow_no_fixedpoint, tower_strictMono, all `propext`-only), and the ceiling is co-witnessed with the 2-adic limit and the machine snap (zpm_triangle). (That ε₀ *is* the least fixed point - epsilonZero_eq_nfp - uses classical logic; whether that is avoidable at the notation level is the open item below.)

**Proved - a wall: the snap is not one mechanism across categories.** The per-domain frame-flips share a shape, not a single categorical map. In Set (all endofunctions) no nontrivial total type carries a Lawvere fixed-point witness - Cantor forbids it - so the lattice and 2-adic faces are provably not Set-level Lawvere instances (nontrivial_lattice_no_witness, q2_no_witness); their ⊥ is a posited fixed point sharing the diagonal shape. The computability face, by contrast, IS a genuine recursion fixed point (computability_face_fixedPoint, Kleene / Rogers) - but it lives in the effective category, where the fixed-point-free diagonal is not computable. Heterogeneous categories, heterogeneous verdicts: what unifies them is the diagonal shape, not one mechanism. The universality that holds is order-theoretic (the fork), not categorical - a proved obstruction.

**Committed / open - the identity, and minimality.** That the domain snaps are *numerically one* transition is a modeling commitment (MC-1), a type boundary, not a theorem. And whether ε₀-as-least-fixed-point is choice-free at the notation level is open: the syntax-to-semantics bridge tower_NF inherits `Classical.choice`.

**A note on the frame-change faces.** snap_is_frameflip, catseam_is_frameflip, and fork_is_frameflip are experimental probes in the bottom-diagram mapping campaign, not a finalized layer. The theorems build and are checkable, and they compose known results (no novelty is claimed); the abstract cross-domain statement "the snap ⊥ → ε₀ IS the change of point of view" remains a conjecture. The formal write-up is [ZP-Q The Frame-Change](ZP-Q_The_Frame_Change.pdf)."""
    return link_in_text(body)

PAGE = """# The Binary Snap (⊥ → ε₀) - Dictionary and Map

*A dictionary and map of the framework's central transition, the snap - what it is, what it is not, and where each characterization is established, most with a machine-checked Lean witness linked to the source.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For the framework's *object*, the bottom element ⊥, see its companion reference [The Bottom Element](BOTTOMELEMENT.md). For the formal framework index and Lean verification, see [README](README.md). For plain-language introductions and reading paths, see [GUIDE](GUIDE.md). For the claim-by-claim status of every result, see the [Claims Ledger](CLAIMS.md).

---

## What this is

This is a **reference** for the framework's central transition, the **snap** - the forced move off the bottom element ⊥ into the first structured state, ε₀. It is the companion to [The Bottom Element](BOTTOMELEMENT.md): that page maps the *object* ⊥ (the noun); this page maps the *transition* off it (the verb). Where the bottom dictionary is mostly nouns, this one is mostly verbs - the snap is an action.

It is a **beginning, not a resolution.** What is *proved* is that the snap is forced, one-way, generates its ceiling from below, and realizes a frame-change in each domain; what is *committed* is that the domain snaps are one object (MC-1); and what stays *open* is the choice-freeness of the ceiling's minimality. The frame-change faces are experimental probes; the abstract "the snap IS the change of frame" is a conjecture, written up in [ZP-Q](ZP-Q_The_Frame_Change.pdf).

---

{rosetta}

---

## Dictionary

### The snap is (positive handles, with witnesses)

The handles sort by **aspect**: what the snap *is* (**noun** - the endpoints it joins) or what the snap *does* (**verb** - the action itself). Most are verbs; that is the point. *The frame-change rows marked "(probe)" and the order-theoretic universal are experimental - the theorems are checkable, the abstract cross-domain reading is a conjecture.*

{is_faces}

### The snap is not (characterization by exclusion)

Each exclusion is either a **proved obstruction** (a Lean-checked wall), a **modeling commitment** (offered, not proved), or an **open** question. The value is here as much as in the positive handles: the walls are what keep the synthesis honest.

{is_not}

---

## Map - the snap arc

*6 nodes, one arc with faces fanning off. The dotted arc is the frame-change reading (the destination ε₀ is the floor ⊥ seen from the inverted frame); the wall node is a proved obstruction, not a gap.*

```mermaid
flowchart LR
  bot((("⊥"))) -- "snap: forced, one-way<br/>t_snap_derived" --> eps["ε₀<br/>minimum non-⊥"]
  bot -. "inverted frame (0 ↔ ∞)<br/>snap_is_frameflip" .-> eps
  eps --- gen["generation<br/>ε₀ = closure of 0"]
  eps --- con["constructive from below<br/>notations, choice-free"]
  bot --- wall["no universal mechanism<br/>Lawvere wall (Cantor)"]
```

---

*Generated by `build_snap_map.py`. Witness names are resolved against the Lean source at generation time and link to the file that declares them; a name that does not resolve fails loud as a warning, and the `meta` / `open` entries (marked as such) have no Lean witness. To update: edit the catalogue and rerun. Mermaid and the links render natively on GitHub.*
"""

def main():
    page = PAGE.format(
        rosetta=render_rosetta(),
        is_faces=render_table([[a, c, render_witnesses(ws)] for (a, c, ws) in IS_FACES],
                              ["aspect", "characterization of the snap", "witness (links to Lean source)"]),
        is_not=render_table([[d, render_witnesses(ws)] for (d, ws) in IS_NOT],
                            ["the snap is not...", "witness (or meta / open)"]),
    )
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {OUT}")
    print(f"{len(INDEX)} declarations indexed - {len(IS_FACES)} positive faces - {len(IS_NOT)} exclusions")
    if UNRESOLVED:
        print("UNRESOLVED witnesses (shown un-linked - check external/field/typo): " + ", ".join(sorted(set(UNRESOLVED))))
    else:
        print("all witnesses resolved")

if __name__ == "__main__":
    main()
