#!/usr/bin/env python3
"""Generator for the metalevel-⊥ slot x construction test matrix.

Single source of truth = the CELLS dict below. Edit a cell (add a witness theorem
or set it to None for an open probe) and re-run to regenerate the matrix markdown.
This is the claim-graph SSOT pattern, scoped to the ⊥ object: the rendered table can
never show a witness the data doesn't sanction, and empty cells are auto-flagged as probes.

Run:  python scripts/build_bottom_matrix.py
Out:  .claude-local/notes/bottom_object_matrix_2026-06-30.md
"""
import sys, os
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")  # μ / ⊥ chars on Windows cp1252

# ⚠ THE OUTPUT NOTE STAYS PRIVATE; THE METHOD OF GENERATION DOES NOT.
# This module moved from `.claude-local/` to `scripts/` on 2026-08-29. Its `CELLS` dict is the data
# `BOTTOMELEMENT.md` renders from, and while it lived in the gitignored folder the public generator
# could only fail with an explanation -- a published page whose source nobody outside this machine
# could run. Tim: "I just want the method of generation to be standardized so that if we ever have
# someone else help with this project they'll be able to use it."
#
# ⚠ AND IT IS THE SHAPE R-SCRIPTS ALREADY RETIRED ONCE. The script mirror was removed because the
# PUBLISHED copy sat outside the integrity check while `register.md` fingerprinted the private one,
# and it drifted three months unnoticed. Published artifact, private source, no check: same shape.
# R-SCRIPTS licenses a private-only script on the test "emits no tracked artifact" -- this one passed
# that test on a technicality, because it does not EMIT `BOTTOMELEMENT.md`, it SUPPLIES its content.
#
# The note below is working material and is deliberately still private. It degrades to this folder
# when `.claude-local/` is absent, so a public clone can run the script rather than crash on a
# directory it does not have.
_NOTES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                      ".claude-local", "notes")
OUT = os.path.join(_NOTES if os.path.isdir(_NOTES) else os.path.dirname(os.path.abspath(__file__)),
                   "bottom_object_matrix_2026-06-30.md")

# slot key -> (header label, one-line meaning)
SLOTS = [
    ("CANT",  "cannot-have"),
    ("NARR",  "narrow / uniqueness"),
    ("MEAS",  "infinite measure"),
    ("INV",   "inversion / 0=∞"),
    ("CONC",  "concurrency / fixed-point"),
    ("SELF",  "self-reference / diagonal"),
    ("GEN",   "generation (floor→ceiling)"),
    ("DYN",   "dynamics · ↓in ↑out ↕seam"),
]

# --- Cell status vocabulary (5-state).  A relationship is not a checkbox: a cell is a CLAIM
# with a status, encoded by a light prefix/suffix on the CELLS value ---
#   "witness"     -> go    (established; sorry-free witness)                       glyph ✓
#   "witness*"    -> cond  (conditional / established via a bridge / inherited)   glyph ✓*
#
# ⭐ A `go` WITNESS NEED NOT BE A THEOREM — a DEFINITION is the top mark, not a weaker one.
# Where a property is what the structure is DEFINED BY, no theorem of it exists or could, so `go`
# records the strongest available form. The live case is `selfApp (abstract ⊥)` / CONC ->
# `unique_fp`, a FIELD of `AbstractSelfApp` (ZeroParadox/Computability/SelfApp.lean:75), cited the
# same way at notes/bottom_by_class_of_math_matrix_2026-07-11.md:17 beside `mc1_correspondence`
# and `t_comp`.  ⚠ DO NOT "correct" it to `cond`. `cond` means a stronger form is PENDING; at the
# invariant tier there is none, and demoting it would assert a gap that does not exist.
# The tier rule is that note's ★ FACE / + ENRICH split: FACE rows are translation-invariant and
# SATURATED — "re-stating it in a new language yields another face, not new understanding" (:59).
# ⚠ DO NOT record how many non-theorem witnesses there are here. An earlier version of this
# comment said "this is the ONE" and was wrong by a factor of ten on the day it was written — the
# audit behind it counted `def` and `class` as acceptable, which is the very assumption the legend
# was making. `build_dictionary_map.py` DERIVES the kind and prints the live list on every run;
# read that, never a figure recorded here.
# ⚠ Nor is `unique_fp` special. It is the one CLASS FIELD; there are also `def` and `class`
# witnesses, and two are external (Mathlib), which the generator resolves by scanning the pin.
#   "!witness"    -> nogo  (REFUTED; the witness is the OBSTRUCTION theorem)      glyph ✗
#   "na: reason"  -> na    (not-applicable by STRUCTURE; a category error,        glyph ∅
#                           e.g. asking a ν-object for a μ-property - NOT a gap)
#   None / absent -> open  (open probe - genuinely unknown, investigable)         glyph ?
# The point (Tim, 2026-07-06): "blank" used to conflate open / structural-N-A / refuted, and "✓"
# conflated established / conditional. This splits them so a question, a settled structural fact,
# and news (a proved obstruction) never render the same.
GLYPH = {"go": "✓", "cond": "✓*", "nogo": "✗", "na": "∅", "open": "?"}
STATUS_LABEL = {"go": "established", "cond": "conditional/bridge", "nogo": "refuted (no-go)",
                "na": "n/a - structural", "open": "open probe"}

def classify(v):
    """(status, text) for a CELLS value; text = witness or reason ('' when open)."""
    if not v:
        return ("open", "")
    s = str(v).strip()
    if s.startswith("na:"):
        return ("na", s[3:].strip())
    if s.startswith("!"):
        return ("nogo", s[1:].strip())
    if s.endswith("*"):
        return ("cond", s[:-1].strip())
    return ("go", s)

# --- The DYN column is special: dynamics is DIRECTIONAL (Tim, 2026-07-06).  Its value starts with
# in / out / both (+ optional * for conditional/bridge/inherited), then the witnesses.  Confirmed
# result (notes/dynamics_directionality_2026-07-06.md): ⊥'s dynamics is single-directional, set by
# whether ⊥ is a sink (ν → ↓ inbound) or a source (μ → ↑ outbound); ↕ both only at a SEAM (μ=ν). ---
DYN_GLYPH = {"in": "↓", "out": "↑", "both": "↕"}

def dyn_glyph(v):
    if not v:
        return "?"
    head = str(v).strip().split(" ", 1)[0]
    star = "*" if head.endswith("*") else ""
    return DYN_GLYPH.get(head.rstrip("*"), "?") + star

# construction -> { slot_key: cell-value }.  See the status vocabulary above (DYN: see dyn_glyph).
# This dict is the single source of truth.
CELLS = {
    "Lat ⊥ (ZPA/ZPE)": {
        "CANT": "zpa_bot_not_greatest", "NARR": "da2_bottom_characterization",
        "MEAS": "na: bare ZPSemilattice has no metric/valuation scalar to diverge",
        "INV": "na: ZPSemilattice states no INVOLUTION and no ∞-counterpart, so there is nothing for z↦1/z to swap ⊥ WITH. ⚠ NOT that no member has a top: `trivialZPSemilattice : ZPSemilattice Unit` has ⊥=⊤ - the earlier reason said so and was refuted 2026-08-29 by the corpus's own standing control. ⚠ An earlier draft of THIS text also cited Bool, which is not a `ZPSemilattice` member at all",
        "CONC": "selfApp_bot_is_both_extremal*", "SELF": "derived_bot_self_mem*",
        "GEN": "na: ZPSemilattice STATES no infinite joins, so ⊔ₙfⁿ(⊥) is not expressible from the class alone; ε₀-generation lives in the ordinal row. ⚠ NOT that no member has them: `CompleteLattice Unit` exists and `trivialZPSemilattice` is a member - the class/member slip corrected in the INV cell above, swept here 2026-08-29",
        "DYN": "out t_snap_derived (⊥=c₀ departs to c₁ - source/μ)",
    },
    "p-adic (ℚ₂/ℤ₂)": {
        "CANT": "padic_bottom_not_initial", "NARR": "fB_bottom_is_limit", "MEAS": "addVal_bot",
        "INV": "rInv_swaps (Riemann sphere 0↔∞)",
        "CONC": "q2_zero_is_fixed", "SELF": "valuation_bot_is_quine*",
        "GEN": "na: ν-limit (inverse limit of balls) - carries inbound dynamics, not GEN (μ/ν fork)",
        "DYN": "in contraction_orbit_tendsto_zero (converge) + c3_irreversible (arrival is a jump) - sink/ν",
    },
    "Info (ZPC)": {"MEAS": "t2_diverges",
        "CANT": "description_instantiation_gap_closed*",
        "NARR": "na: the info bottom is the n→∞ surprisal limit, not a pinned carrier point",
        "INV": "na: −log prob↔info is a coordinate change, not a ⊥↔∞ involution",
        "CONC": "na: no self-application operation on surprisal / distributions",
        "SELF": "da1_closed_concrete*", "GEN": "na: unbounded ascent, with no distinct level above it constructed - GEN asks the floor to generate the tower over it, and nothing here builds one",
        "DYN": "out* t_snap_derived (snap off the machine null c₀; ZP-E bridge)"},
    "#4 Kleisli (Fin 0)": {
        "CANT": "kleisli_bottom_not_zero", "NARR": "fC_zero_isInitial",
        "MEAS": "na: the empty type carries no distribution at all, so no scalar exists to diverge. ⚠ `IsEmpty (PMF (Fin 0))` elaborates, so the stronger mark - a proved obstruction (✗) rather than a category error - is AVAILABLE and unbuilt as of 2026-08-29. Upgrading it costs one theorem; the mark stays ∅ until that theorem exists, because a cell may not cite a witness the corpus does not contain",
        "INV": "IsInitial.op (Mathlib)",
        "CONC": "na: DEGENERATE on an empty carrier - there are no points, so every endomorphism fixes every "
            "point vacuously and CONC carries no content here. ⚠ This cell previously cited "
            "`kleisli_bottom_not_zero` as a refutation; that theorem proves the Kleisli bottom is "
            "not a ZERO OBJECT (not terminal), which is a mu/nu DIRECTION fact and belongs to DYN. "
            "It addresses neither of CONC's two propositions",
        "SELF": "na: DEGENERATE, and that is the finding. `Fin 0` is EMPTY, so the Kleisli endomorphism "
            "`Fin 0 -> PMF (Fin 0)` is the unique empty map and every diagonal/self-application "
            "statement about it holds VACUOUSLY, carrying no content about this bottom. "
            "⚠ Not that no self-map exists - the same correction the TopCat cells took "
            "2026-08-29. No ZP witness is cited because none is owed for a degeneracy",
        "GEN": "node4_generates_nat",
        "DYN": "out fC_no_return (initial source; nothing returns to ⊥ - μ)",
    },
    "#5 Hilbert (zero obj/seam)": {
        "CANT": "seam_not_mu_colimit_apex",
        "NARR": "hilbert_bottom_isZero",
        "MEAS": "na: the zero space has finrank 0 - every attached scalar is 0/finite",
        "INV": "hasZeroObject_op (Mathlib)",
        "CONC": "seam_is_mu_nu_coincidence_SeamCoincidence", "SELF": "biprod_diagonal_only_zero (self-similarity)",
        "GEN": "na: μ=ν self-coincident (seam⊔seam≅seam) - it generates no level distinct from itself",
        "DYN": "both seam_has_Pin (terminal: maps in) ; hilbert_bottom_isZero.isInitial (maps out) - the SEAM (μ=ν)",
    },
    "#3 TopCat ({0} limit)": {"CANT": "padic_bottom_not_initial", "NARR": "floorConeIsLimit",
        "MEAS": "na: TopCat forgets the scalar; divergence-at-⊥ is the p-adic/info sibling",
        "INV": "na: TopCat forgets field mult; z↦1/z is the ℚ₂ Riemann sibling",
        "CONC": "na: DEGENERATE, and that is the finding. The cone apex is a SUBSINGLETON, so `ContinuousMap.id` is an intrinsic self-map and EVERY self-map fixes every point - CONC holds VACUOUSLY, carrying no content about this bottom. ⚠ The earlier reason claimed no self-map exists; that was refuted by compilation 2026-08-29. No ZP witness is cited because none is owed for a degeneracy",
        "SELF": "na: SELF asks for a DIAGONAL (a self-application whose fixed point is the object), which the limit object does not carry. ⚠ Not that it has no self-map at all - the apex is a subsingleton and `ContinuousMap.id` is one; that degeneracy is recorded under CONC",
        "GEN": "na: ν-limit ({0} as a topological limit) - carries inbound dynamics, not GEN (μ/ν fork)",
        "DYN": "in* c3_irreversible (topological no-return; stated on ambient Q₂) - sink/ν"},
    "#2 Markov (attractor)": {
        "CANT": "markov_node_no_universal_property", "NARR": "markov_node_irreducible_rescue*",
        "MEAS": "na: a probability distribution - no finite value diverges at it",
        "INV": "na: the simplex carries no 0↔∞ POLE for an inversion to swap, which is what INV asks. ⚠ NOT that no involution exists: `PMF.map (Equiv.swap 0 1)` on `PMF (Fin 2)` is one, exchanging the vertices - compiled 2026-08-29, refuting the earlier wording",
        "CONC": "exists_stationary",
        "SELF": "na: no self-application; its fixed point is CONC, no self-similarity",
        "GEN": "na: ν-attractor - carries inbound dynamics, not GEN (μ/ν fork)",
        "DYN": "in doubly_stochastic_mean_ergodic (converge) + fullMix_not_injective (mixing is lossy) - sink/ν",
    },
    "Kleene (quine, ZPK)": {
        "CANT": "self_halting_undecidable", "NARR": "kleene_quine_is_bot",
        "MEAS": "infinite_quine_family",
        "INV": "na: programs carry no ∞-counterpart for an inversion to swap the bottom WITH. ⚠ NOT that no involution exists - `Equiv.swap` on two distinct codes is one, compiled 2026-08-29. Narrowed to the half that stands, matching the Markov INV correction",
        "CONC": "computational_quine_exists", "SELF": "quine_period_is_goedel",
        "GEN": "na: self-coincident fixed point (⊥ = the quine itself) - carries SELF, not floor-generates-tower",
        "DYN": "in quine_encodings_approach_bot (encodings approach ⊥; a static point)",
    },
    "ε₀ (ordinal, ZPL/M)": {
        "CANT": "kruskal_is_wqo_not_descent*",
        "NARR": "epsilonZero_le_fixedPoint", "MEAS": "cnfToZp2_valuation_unbounded",
        "INV": "na: a well-order has a floor but no ∞-pole / order-reversing z↦1/z",
        "CONC": "epsilonZero_fixedPoint",
        "SELF": "both_fixed_points_exist*", "GEN": "epsilonZero_eq_nfp",
        "DYN": "both tower_converges_to_zero (floor 0) ; snap_exactly_at_epsilon_zero (the level above, ε₀) - the snap-ARC",
    },
    "selfApp (abstract ⊥)": {
        "CANT": "scale_ne_fixed", "NARR": "selfApp_fp_set_eq_singleton",
        "MEAS": "na: AbstractSelfApp abstracts away valuation (ℚ₂ deliberately not an instance)",
        "INV": "na: no ∞-pole; qua μ=ν seam the point is the inversion-FIXED centre",
        "CONC": "unique_fp", "SELF": "derived_bot_self_mem",
        "GEN": "na: self-coincident (μ=ν seam, ⊥ = the least fixed point) - carries SELF/CONC, not GEN",
        "DYN": "out* t_snap_derived (inherited; the static seam-point does not itself move)",
    },
}

def cell(v, key=None):
    if key == "DYN":                          # directional dynamics column
        g = dyn_glyph(v)
        parts = str(v).strip().split(" ", 1) if v else []
        txt = parts[1] if len(parts) > 1 else ""
        return f"{g} {txt}" if txt else g
    st, txt = classify(v)
    g = GLYPH[st]
    return g if (st == "open" or not txt) else f"{g} {txt}"

def status_tally():
    from collections import Counter
    c = Counter(classify(d.get(k))[0] for d in CELLS.values() for k, _ in SLOTS if k != "DYN")
    order = ["go", "cond", "nogo", "na", "open"]
    five = " · ".join(f"{GLYPH[s]} {STATUS_LABEL[s]}: {c.get(s,0)}" for s in order)
    dc = Counter(dyn_glyph(d.get("DYN")).rstrip("*") for d in CELLS.values())
    dyn = " · ".join(f"{g}:{dc.get(g,0)}" for g in ("↓", "↑", "↕", "?"))
    return five + f".\n**Dynamics direction** (↓ sink/ν · ↑ source/μ · ↕ seam): {dyn}"

def render():
    keys = [k for k, _ in SLOTS]
    head = "| Construction | " + " | ".join(keys) + " |"
    sep  = "|" + "---|" * (len(keys) + 1)
    rows = [head, sep]
    for c, d in CELLS.items():
        rows.append("| **" + c + "** | " + " | ".join(cell(d.get(k), k) for k in keys) + " |")
    return "\n".join(rows)

def empties():
    out = []
    for c, d in CELLS.items():
        miss = [k for k, _ in SLOTS if not d.get(k)]
        if miss:
            out.append(f"- **{c}**: {', '.join(miss)}")
    # per-slot coverage
    cov = []
    for k, lbl in SLOTS:
        # ESTABLISHED, never merely present: a cell with an `na:`/`?`/`!` entry is filled and
        # says the property does NOT hold there. Counting presence rendered 10/10 for every
        # slot, including the two this file calls near-empty.
        st = [classify(d[k])[0] for d in CELLS.values() if d.get(k)]
        n = sum(1 for s in st if s in ("go", "cond"))
        rest = ", ".join(f"{GLYPH[s]}{st.count(s)}" for s in ("nogo", "na", "open")
                         if st.count(s))
        cov.append(f"- **{k}** ({lbl}): {n}/{len(CELLS)} established"
                   + (f" ({rest})" if rest else ""))
    return "\n".join(out), "\n".join(cov)

READOUT = """\
## What the matrix tests - the empty-cell readout

**Two near-empty slots = the two newest. The strongest finding.** Counts live in the computed per-slot coverage above, never here - a hand-maintained count is exactly what the first bullet below records going wrong.
- **INV is sparse, and the live cells are marked in the column** - do not count it in prose. ⚠ The
  earlier text here said INV was empty everywhere except p-adic and drew a conclusion from it: that
  the categorical INV cell was the unbuilt `Cᵒᵖ` keystone, a structural hole. Both categorical INV
  cells are FILLED, by exactly the opposite-category results named as missing (`IsInitial.op`,
  `hasZeroObject_op`). Measured 2026-08-29 by recomputing from CELLS; the hole was an artifact of a
  hand-maintained count.
- **GEN is μ-only, and its live cells are marked in the column - the μ/ν FORK, not a gap.** GEN ↔ μ (generate UP
  from ⊥ = least fixed point; abstraction is Mathlib's Kleene `lfp = ⨆ₙ fⁿ(⊥)`). Its DUAL is inbound dynamics
  ↔ ν (flow DOWN to ⊥ = attractor/limit). So the ν-bottoms (p-adic inverse limit, Markov attractor) carry
  inbound dynamics (↓), not GEN - asking them for GEN is asking a ν-object for a μ-property. (Categorical μ-GEN
  = Adámek's initial-algebra-colimit, not cheaply in Mathlib - open. See gen_probe_2026-06-30.md.)

- **DYNAMICS is single-directional (confirmed 2026-07-06, `dynamics_directionality_2026-07-06.md`).** The old
  REACH + DYN columns were the two SUB-SENSES of one dynamics axis - inbound (↓, converge TO ⊥) and outbound
  (↑, depart FROM ⊥ irreversibly) - now merged into one directional column. ⊥'s dynamics is single-
  directional, set by its μ/ν polarity: **source (μ/initial) → ↑ outbound; sink (ν/limit/attractor) → ↓
  inbound; seam (μ=ν zero object) → ↕ both.** The apparent "both" of p-adic and Markov was a MIS-FILING:
  `c3_irreversible` (no continuous path TO 0 - the *arrival* is a jump) and `fullMix_not_injective` (mixing
  *toward* the stationary state is lossy) are inbound-irreversibility, not departures - re-sorted to ↓. So ↕
  is a SEAM diagnostic; the only genuine ↕ is Hilbert (ε₀ shows ↕ because its row IS the snap-arc 0→ε₀).

**SELF has two sub-senses (#5-Hilbert probe 2026-06-30).** self-APPLICATION (Kleene-quine: a code acts on
its own index - Kleene/selfApp/ε₀ bottoms; a computability phenomenon) vs self-SIMILARITY / diagonal-
uniqueness (⊥ is the unique fixed point of a self-construction). The Hilbert bottom carries the latter:
`biprod_diagonal_only_zero` (`X ≅ X⊞X → IsZero X`, finite-dim) - the genuine version TC37 faked. Read SELF
as these two sub-senses; the structural bottoms get self-similarity at most, not self-application.

**Instrument validation (reproduces known structure):** #2 Markov's column is sparse, and the SHAPE of
that sparsity is its signature (probe 2026-06-30, `markov_probe_2026-06-30.md`). ⚠ Do not rank the
columns here: which is sparsest or richest is visible in the rendered table and a count in prose goes
stale against it (R-ADJACENT). It lives in the analytic mode -
CONC (stationary fixed point) + ↓ inbound dynamics (mean-ergodic attractor ‖T₂‖≤1, and lossy mixing) + CANT
(no universal property) + conditional NARR - and every other cell is empty for a NAMED structural reason:
GEN empty by the μ/ν fork (it is a ν-attractor, carries inbound dynamics not GEN); INV not applicable
because the simplex carries no 0↔∞ POLE for an inversion to swap ⚠ (NOT because no involution exists:
`PMF.map (Equiv.swap 0 1)` is one, compiled 2026-08-29 -- see the INV cell above, which this line
contradicted until round 3 caught it);
MEAS not applicable (a probability distribution, no value diverges at it); SELF absent (no self-application;
its fixed point is CONC, no self-similarity characterization). Its inbound-dynamics (↓) irreversibility is
the SPECTRAL GAP (2026-06-30, cold-audit SOLID): `fullMix_not_injective` - a mixing chain's relaxation
operator is non-injective (loses the mean-zero mode), the genuine irreversibility *into* the attractor, with
`fullMix_mode_decays` from the general `tendsto_norm_iterate_zero`. FENCED: mixing-only - permutation/cyclic
chains have no gap, are injective, do not mix (TC39). So #2 = CONC + ↓inbound-dynamics + CANT + condNARR;
still MEAS/INV/SELF/GEN empty by structure. This agrees with "the telling exception" seen in the campaign and in the Direction-A archimedean
place. ⚠ It was previously called the THIRD INDEPENDENT confirmation, resting partly on the INV
premise corrected above; independence is not established once a shared premise is wrong, so the
claim is now agreement rather than a count. Categorical bottoms (#4/#5/#3) are structural-only.
Info is a pure-MEAS witness. ε₀ and Kleene carry the diagonal-fixed-point's two deepest faces.

**Goodhart guard (standing):** the value is empty cells (questions) and no-fits (news), NOT the filled
count. Do not optimize "fill more cells." Track which empties become proved witnesses vs proved
obstructions - that history is the real record.

**Provenance:** generated by `scripts/build_bottom_matrix.py` from its CELLS dict (the SSOT). Full
witness lists per cell: `bottom_object_harvest_catalog_2026-06-30.md`. Edit CELLS + re-run to update.
"""

def main():
    miss, cov = empties()
    doc = f"""# Metalevel ⊥ object - slot × construction test matrix (generated)

Rows = bottom-CONSTRUCTIONS; columns = SLOTS (kinds of ⊥-fact). A cell is a **claim with a status**,
not a checkbox - 5 states so a question, a settled structural fact, and news never render the same:

**Cell status:** {status_tally()}.

**Slot key:** {' · '.join(f'{k} = {lbl}' for k, lbl in SLOTS)}.

{render()}

(`✓` established · `✓*` conditional/bridge · `✗` refuted (obstruction witness) · `∅` n/a by structure
(a category error, e.g. asking a ν-object for a μ-property - not a gap) · `?` open probe. Cited-from-Mathlib
entries are marked `(Mathlib)`, NOT ZP-proved. Every cell above is generated from `scripts/build_bottom_matrix.py`; read that for the full entries.)

## Open probes (auto-flagged empty cells - each a GO/NO-GO target)
{miss}

## Per-slot coverage
{cov}

---

{READOUT}"""
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(doc)
    print(f"wrote {OUT}")
    print(f"{len(CELLS)} constructions x {len(SLOTS)} slots; "
          f"{sum(len([k for k,_ in SLOTS if not d.get(k)]) for d in CELLS.values())} empty cells")

if __name__ == "__main__":
    main()
