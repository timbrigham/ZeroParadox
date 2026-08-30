"""
Build ZP-I Illustrated Companion
Version 1.31 | August 2026
v1.31: THE CLAIM IS DELETED, NOT REDRAFTED (companion sync with ZP-I v1.22; adversary FAIL-BEDROCK). Three findings landed in this file, one of them the worst kind. (1) The step table's SOURCE cell for step 1 read "R1 + ZP-B completeness ... (t_iz_cauchy)". t_iz_cauchy binds the chain and the norm bound and NO LATTICE AT ALL; it is pure p-adic analysis. Restated to what it consumes. (2) The Lean status box gave t_iz_r1_t3_geometric_bound the binders of its NEIGHBOUR h_strict_from_r1_t3 - IsDepthChain and IsStrictStateSequence, listed correctly one entry above - and dropped the nonvanishing hypothesis the named lemma actually requires. A status box stating a theorem that is not the theorem. (3) Door 1 still credited R1 with leaving the chain somewhere to go, one paragraph from the text reserving R1 for no-subtraction; deleted, see the formal document's v1.22 entry for the counter-model that settles it. Also: "T3 drives ascent" at :294 and :599 - T3 is monotonicity, and the corpus's own compiled gauge shows it permits stalling in any ZPSemilattice - and the dead file name ZPI.lean in the header, which has been ZeroParadox/Valuation/SemilatticeInstance.lean since the reorg. ROUND 3 (adversary FAIL-BEDROCK): the cycle diagram's fourth node was labelled 'eps_(omega-1)' with the sublabel 'last state'. That ordinal DOES NOT EXIST - omega is a limit and has no predecessor - and the paired formal document denies the sublabel four pages earlier at Remark R-I.1, "a countable sequence with NO last element in L". Together they made the limit read as a successor step, the exact misreading this document exists to block. Second Drawing-borne defect in three rounds, after 'T3 (R1 drives)' at comp v1.29: a String inside a Drawing is invisible to every prose checker in this repository, so the only detector is a reviewer reading the drawing code. Also: the arrow labels gave the climb to T3 alone, and T3 is monotonicity, which the corpus's own gauge shows permits stalling; and the step-1 source cell, repaired earlier this round, still led with ZP-B completeness, which t_iz_cauchy does not consume. ROUND 4 (editorial FAIL-BEDROCK, ordinary here): the summary still read "T-IZ is derived from ZP-A through ZP-E and ZP-K" - the five-document range attribution the formal document deleted at v1.22. A range of documents is not a derivation. ROUND 3, SECOND GATE (editorial FAIL-BEDROCK): the section III-C status box made the same "pure ZP-A lattice conditions" claim TWICE in one entry and dropped the nonvanishing hypothesis again - the exact omission the v1.31 entry above records as fixed one entry earlier at the geometric-bound lemma. Third half-applied fix in this arc. Corrected to the three hypotheses the signature actually binds, with only IsStrictStateSequence named as a lattice condition.
v1.30: ATTRIBUTION CORRECTED (companion sync with ZP-I v1.21; claim-review FAIL-BEDROCK). The comp v1.29 name fix left the false attribution in place. HasNoTop appears in no binder of any declaration in SemilatticeInstance.lean; what h_strict_from_r1_t3 consumes is IsDepthChain and IsStrictStateSequence. Two LEAN STATUS BOXES carried "from R1 + T3" - a status box is the surface a general reader treats as the verified summary, which makes it the worst place for a premise nothing binds.
v1.29: NAME COLLISION RESOLVED, AND THE OUTSIDE-L CLAIM RETRACTED (companion sync with ZP-I v1.20). R1 named two propositions - ZP-A's is NO-SUBTRACTION, and the order property is HasNoTop in ZeroParadox/Order/Lattice.lean. This companion used both, one paragraph apart from Door 1 which correctly reads "R1 (No subtraction)". Per Tim, the order property is now named HasNoTop and "ZP-A R1" is reserved for no-subtraction. Retracted with it, and introduced by the v1.28 fix: that no-top "puts the limit OUTSIDE L so the succession has somewhere to go" - refuted by a compiled counterexample in the ordinals under max, whose ascending chain has its least upper bound inside the carrier. Also swept: the diagram arrow label 'T3 (R1 drives)', which sits inside a Drawing and is invisible to every prose checker in this repository - found only because a reviewer read the drawing code.
v1.28: R1 ATTRIBUTION CORRECTED (companion sync with ZP-I v1.19; DC-32, enabling credited as forcing). Seven sites, worse than the formal document's ten because one was a SECTION TITLE ("The No-Top Property Is the Engine") and another a remember-box, which is what a general reader takes away. The claim: R1 (no top) is "the engine that drives T-IZ", "the driving force", and "the chain cannot stop". Measured at the signature - h_strict_from_r1_t3 binds S, depths, IsDepthChain and IsStrictStateSequence, and HasNoTop is not among them. No-top says every element has a strictly greater one, so no chain HAS to stop (the further claim that the limit falls outside L is RETRACTED at comp v1.29); that a particular chain keeps stepping is IsStrictStateSequence. One site listed "no top element, monotonicity, and IsDepthChain" as together forcing strict depth growth - three conditions, omitting the one that actually does it. NOTE the document already carried an "Occurrence fence" for T-SNAP two paragraphs from an uncorrected R1 site: the same possibility/occurrence distinction was applied to one axiom and not the adjacent one. Backed by a new mutation-verified NO-GO gauge at SemilatticeInstance.lean §Ib. Do not read this as retracting R1; deleting it from the account is the opposite error (DC-30).
v1.27: JOIN-IDENTITY OVERCLAIM RETRACTED (bedrock, adversary round 4; companion sync with ZP-I v1.18). The other conjunct of the sentence comp v1.26 half-corrected. The document asserted "The Cauchy limit 0 in Q2 satisfies the join-identity condition" as a proved step, and that property is t_iz_limit_is_new_null's HYPOTHESIS, not its conclusion. Measured at the signature: t_iz_complete takes the 2-adic sequence and, separately, a terminal in an arbitrary semilattice with h_role handed in, and never identifies the two - a conjunction of independent results, not a chain. Q2 carries no join at all, so the condition is not statable of the limit. The "four steps, all formally proved, no step is outside Lean scope" framing rested on that unstated premise and now says what the theorem joins and what it does not. CLAIMS.md's T-IZ row had it right throughout. SWEEP COMPLETED (round 5, both gates FAIL-BEDROCK on the half-applied first pass): the first pass fixed step-table row 2 and left row 4 of the SAME table asserting "the limit fills the ⊥ role ... proved in Lean ✓" - the exact inverse of the comp v1.26 defect, which fixed row 4 and left row 2. Third instance of half-application in this arc. Root cause fixed first, in the Lean: SemilatticeInstance.lean:261 still carried the retracted claim verbatim, and R-COREOBJ sends every agent there first, so every round drafted from a source asserting what it was retracting. Framing moves from two tiers to three - convergence PROVED, role-recognition PROVED as an implication, occupancy a COMMITMENT (not statable in Q2), novelty a further COMMITMENT. Also corrected: "closes the chain without any ungrounded hypothesis ✓", where t_iz_complete_from_axioms carries h_role explicitly.
v1.26: NOVELTY OVERCLAIM RETRACTED - THE v1.25 SWEEP WAS HALF-APPLIED (bedrock). v1.25 retitled the step-table row that said bottom-prime "is born" and left three sites standing in the same document, which is worse than the original error: a half-applied fix to a self-consistent claim manufactures a self-contradiction. Step-table row 2 asserted "The limit is bottom-prime" with the evidence cell "proved in Lean (t_iz_limit_is_new_null, axiom-free)" while row 4 of the SAME table already carried the correct annotation "(the role, not the novelty)". SnapCannotBe.lean:43 forbids that citation verbatim: the theorem proves the ROLE half only, one direction, into the bottom ALREADY PRESENT in that lattice - it identifies an occupant, it does not construct anything. The "closed system" note ran the derivation chain "from T-SNAP through T-IZ to bottom-prime"; the chain reaches the bottom ROLE. The traceability block listed "bottom-prime-identification" among what t_iz_complete proves "All formal". Novelty is C-DA2, a commitment: snap_arc_z2_loop has the 2-adic arc returning to the SAME 0. Third occurrence of this defect in ZP-I - struck from the formal document at v1.16 and v1.17, and this companion was the sweep that missed it.
v1.25: NOVELTY OVERCLAIM RETRACTED (companion sync with ZP-I v1.16). The step table carried a row titled "T-SNAP fires, bottom-prime is born" with a Lean checkmark beside it; the checkmark was honest about bot_join, the row title was not. Also "the chain generates its own successor by forward motion alone" and "Emergence and return are both derived, not assumed". What is proved is the ROLE half: anything acting as the join's additive identity IS the bottom, the same one. That the branch ends at a FRESH bottom is a commitment - in the 2-adic picture the arc returns to the same 0. v1.24 fenced occurrence; novelty is a separate commitment and was left unfenced.
v1.24: FORCING OVERCLAIM RETRACTED (companion sync with ZP-I v1.15). "T-SNAP (bottom -> eps0, necessarily)" asserted occurrence; T-SNAP fixes the transition's shape and does not establish that it is taken (Order/Snap.lean's tsnap_holds_but_nothing_moves holds in a model where nothing moves). Occurrence is a framework commitment.
v1.23: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v1.21: "(no sorryAx)" applied to step 1 source; ZP-internal labels removed from step table; "No new axioms" clarified to scope; "the framework" scoped to ZP-I (ER/AR fixes).
v1.20: Conditions scoped in prose ("every" → conditional); "(axiom-free)" corrected to "(no sorryAx)" for theorems using propext/Classical.choice (ER/AR fixes).
v1.19: Norm bound includes S(0) factor; IsDepthChain/IsStrictStateSequence added to key result box; ZP-internal framing replaced with standard math (AR fixes).
v1.18: IsDepthChain hypothesis added to strict growth claim (AR fix).
v1.17: Blanket purity claim replaced with per-theorem scoping (AR fix).
v1.16: Norm claim corrected to inequality ("at most 2^{-n}" — matches proved bound).
v1.15: Em-dashes removed; "closed system" language scoped to derivation chain (AR/ER fixes).
v1.11: "Zero Paradox" expanded in disclaimer (AR fix).
v1.10: T-IZ step table updated to 4 steps all proved via t_iz_complete (AFA/Kleene path);
       disclaimer rewritten as self-contained; KleeneStructure condition added to key result box.
v1.9: Cover title retitled "Going Forward Brings You Back to Zero" (AR fix).
v1.8: Well diagram state labels  - black outline for visibility; DA-2 label centered.
v1.7: Depth diagram legibility  - font sizes, Unicode math notation, norm labels below circles.
v1.6: Vocab fix: null state → ⊥.
v1.5: Strip version number from companion footer.
v1.4: Strip Lean file version numbers from Lean 4 Verification section.
v1.3: Disclaimer and opening paragraph updated.
v1.2: (prior)
v1.1: R-IZ-A closure explained; engine section and Step 1 source updated.
v1.0: Initial release.

Standalone companion for ZP-I: Inside Zero.
Accessibility target: 2 years of college math.
Lean status reflected: ZeroParadox/Valuation/SemilatticeInstance.lean (current)  - all proofs filled, no sorryAx.
"""

import os, math
from zp_utils import *

from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF

def lean_status_box(rows):
    data = [[Paragraph('Lean 4 Verification Status (SemilatticeInstance.lean  - all proofs filled, no sorry)',
                        CS['kr_hdr'])]]
    for r in rows:
        data.append([Paragraph(fix(r), CS['kr_body'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  INDIGO),
        ('BACKGROUND',    (0,1), (-1,-1), INDIGO_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, INDIGO),
        ('TOPPADDING',    (0,0), (-1,-1), 6),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t


# ── DIAGRAM 1: Inside Approach (2-adic depth) ─────────────────────────────────
def depth_diagram():
    """Shows chain descending in 2-adic depth toward zero at the limit.

    All elements are strictly within [0, dh] and [0, dw] to avoid the ReportLab
    Drawing overflow bug (elements outside bounds render over surrounding page text).
    Uses 4 states with safe fixed y-coordinates, and a right-pointing limit indicator
    instead of a zero circle placed below the chain.
    """
    dw, dh = TW, 2.8 * inch  # 2.8 * 72 = 201.6 pts
    d = Drawing(dw, dh)

    # Safe margins: keep all content within y=[14, dh-14] = [14, 187.6]
    TOP_Y  = dh - 14   # 187.6
    BOT_Y  = 14        # 14

    # Gradient bands (shallow at top, deep at bottom)
    band_colors = [
        colors.HexColor('#EEF4FA'), colors.HexColor('#DDEAF7'),
        colors.HexColor('#CCE0F5'), colors.HexColor('#BBD6F2'),
        colors.HexColor('#AACCEF'),
    ]
    band_h = (TOP_Y - BOT_Y) / len(band_colors)
    for i, bc in enumerate(band_colors):
        y = BOT_Y + i * band_h
        d.add(Rect(30, y, dw - 60, band_h, fillColor=bc, strokeColor=None))

    # Vertical axis (left edge): arrow points downward = deeper
    ax = 28
    d.add(Line(ax, TOP_Y, ax, BOT_Y + 6, strokeColor=COMP_SLATE, strokeWidth=1.5))
    d.add(Polygon([ax, BOT_Y, ax - 4, BOT_Y + 8, ax + 4, BOT_Y + 8],
                  fillColor=COMP_SLATE, strokeColor=COMP_SLATE, strokeWidth=0))
    d.add(String(2, TOP_Y - 8, 'shallow', fontSize=7.5, fontName='DV-I', fillColor=COMP_SLATE))
    d.add(String(2, BOT_Y + 2, 'deep',    fontSize=7.5, fontName='DV-I', fillColor=COMP_SLATE))
    d.add(String(0, dh / 2 + 6,  '2-adic', fontSize=7.5, fontName='DV-I', fillColor=COMP_SLATE))
    d.add(String(0, dh / 2 - 5,  'depth',  fontSize=7.5, fontName='DV-I', fillColor=COMP_SLATE))

    # 4 states at fixed, safe y-coordinates: 165, 128, 91, 54 (all within [14, 187])
    # x-coordinates step left-to-right so the chain goes upper-left → lower-right
    cx_base = dw * 0.20    # ≈ 93.6
    cx_step = dw * 0.155   # ≈ 72.5
    state_ys = [165, 128, 91, 54]
    state_xs = [cx_base + i * cx_step for i in range(4)]
    # S0: (93.6, 165)  S1: (166.1, 128)  S2: (238.6, 91)  S3: (311.1, 54)
    # Circle radius 8: all circles stay in y=[46, 173] ⊂ [14, 188] ✓
    # Rightmost x = 311.1 + 8 = 319.1 ≪ dw = 468 ✓

    state_lbls = ['S₀', 'S₁', 'S₂', 'S₃']
    state_subs = ['= ⊥', '',   '',   ''  ]

    # Connecting lines between consecutive states
    for i in range(3):
        d.add(Line(state_xs[i] + 9, state_ys[i] - 7,
                   state_xs[i+1] - 9, state_ys[i+1] + 7,
                   strokeColor=COMP_BLUE, strokeWidth=1.5))

    # State circles
    for i in range(4):
        sx, sy = state_xs[i], state_ys[i]
        d.add(Circle(sx, sy, 8, fillColor=COMP_BLUE, strokeColor=WHITE, strokeWidth=1.5))
        d.add(String(sx - 10, sy - 4, state_lbls[i], fontSize=8, fontName='DVS',
                     fillColor=WHITE, strokeColor=colors.black, strokeWidth=0.4))
        if state_subs[i]:
            d.add(String(sx + 12, sy - 3, state_subs[i], fontSize=8, fontName='DVS',
                         fillColor=COMP_SLATE))

    # Norm labels: placed BELOW each circle (sy - 8 radius - 3 gap - text baseline).
    # This avoids collision with the "= ⊥" sub-label which sits to the right of the circle.
    # S2 omitted (S3 norm nearby). S3 placed above-left (limit indicator owns the right).
    norms_below = [(0, '‖S₀‖ = 1'), (1, '‖S₁‖ ≤ 2⁻¹')]
    for i_s, ns in norms_below:
        sx, sy = state_xs[i_s], state_ys[i_s]
        d.add(String(sx - len(ns) * 2.4, sy - 22, ns, fontSize=8, fontName='DV-I',
                     fillColor=colors.HexColor('#555555')))
    # S3: above-left so it doesn't collide with the limit-indicator arrow
    sx3, sy3 = state_xs[3], state_ys[3]
    d.add(String(sx3 - 72, sy3 + 14, '‖S₃‖ ≤ 2⁻³', fontSize=8, fontName='DV-I',
                 fillColor=colors.HexColor('#555555')))

    # Limit indicator: dotted line + arrow pointing right from S3, then "→ 0"
    # Arrow: from S3.x+10 to S3.x+10+40, at S3.y level
    arr_x1 = sx3 + 10
    arr_x2 = sx3 + 55      # ≈ 366
    arr_y  = sy3            # 54
    # Three dots along the arrow
    for k in range(3):
        d.add(Circle(arr_x1 + 10 + k * 10, arr_y, 2, fillColor=COMP_BLUE, strokeColor=None))
    # Arrow shaft + head
    d.add(Line(arr_x1 + 42, arr_y, arr_x2 - 6, arr_y,
               strokeColor=COMP_AMBER, strokeWidth=2))
    d.add(Polygon([arr_x2, arr_y, arr_x2 - 7, arr_y + 4, arr_x2 - 7, arr_y - 4],
                  fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    # "0 (limit)" label
    # arr_x2 ≈ 366, text at ≈ 370; '0 (limit)' ~9 chars × 5pt = 45pt → ends at 415 ≪ 468 ✓
    d.add(String(arr_x2 + 5, arr_y + 3, '0',
                 fontSize=11, fontName='DVS-B', fillColor=COMP_AMBER))
    d.add(String(arr_x2 + 18, arr_y + 3, '(depth → ∞)',
                 fontSize=8, fontName='DVS-I', fillColor=COMP_SLATE))
    # Annotation at arr_y + 3 = 57. Arrow elements: y in [46, 62]. Within [14, 187] ✓

    # Bottom caption (within drawing, at y=4; text occupies y=[4, 12]  - below all circles)
    d.add(String(30, 4,
                 'States descend in 2-adic depth by going forward  - the limit is 0, reached from inside',
                 fontSize=7.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    # Caption at y=4 (top ≈ 12). BOT_Y = 14 means the band background starts at y=14. ✓
    # Nothing below y=4 in this diagram. ✓

    return d


# ── DIAGRAM 2: Three Closed Doors + Fourth Passage ────────────────────────────
def three_doors_diagram():
    """Three blocked paths (R1, C3, AX-G2) and one open passage (Cauchy)."""
    dw, dh = TW, 2.4 * inch
    d = Drawing(dw, dh)

    target_x = dw - 52
    target_y = dh / 2

    # Target: zero
    d.add(Circle(target_x, target_y, 14, fillColor=COMP_AMBER,
                 strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(target_x - 5, target_y - 5, '0', fontSize=11, fontName='DV-B', fillColor=WHITE))
    d.add(String(target_x - 10, target_y - 22, '⊥′',
                 fontSize=8, fontName='DVS', fillColor=COMP_SLATE))

    RED = colors.HexColor('#C0392B')

    # Three blocked attempts  - spaced vertically above center
    blocked = [
        (dw * 0.18, dh * 0.80, 'Subtraction', '(R1 blocks)'),
        (dw * 0.38, dh * 0.80, 'Continuous path', '(C3 blocks)'),
        (dw * 0.58, dh * 0.80, 'Morphism in C', '(AX-G2 blocks)'),
    ]
    for (bx, by, lbl1, lbl2) in blocked:
        # Line toward target, stopped midway
        mid_x = (bx + target_x - 14) / 2
        mid_y = (by + target_y) / 2
        d.add(Line(bx, by - 16, mid_x - 4, mid_y + 2,
                   strokeColor=RED, strokeWidth=1.5))
        # X at midpoint
        sz = 6
        d.add(Line(mid_x - sz, mid_y - sz, mid_x + sz, mid_y + sz,
                   strokeColor=RED, strokeWidth=2.5))
        d.add(Line(mid_x + sz, mid_y - sz, mid_x - sz, mid_y + sz,
                   strokeColor=RED, strokeWidth=2.5))
        # Box label
        bw, bh = 82, 30
        d.add(Rect(bx - bw / 2, by - bh / 2, bw, bh,
                   fillColor=colors.HexColor('#FDECEA'), strokeColor=RED, strokeWidth=1.2))
        d.add(String(bx - 36, by + 4, lbl1, fontSize=8, fontName='DV-I', fillColor=RED))
        d.add(String(bx - 34, by - 8, lbl2, fontSize=7.5, fontName='DV-I', fillColor=RED))

    # Fourth passage: Cauchy sequence (below)
    cau_x = dw * 0.26
    cau_y = dh * 0.24

    # Dashed green arrow
    dx_total = target_x - 14 - cau_x
    dy_total = target_y - cau_y
    dist = math.sqrt(dx_total**2 + dy_total**2)
    n_segs = int(dist / 14)
    for i in range(n_segs):
        t0 = i / n_segs
        t1 = (i + 0.5) / n_segs
        x0 = cau_x + dx_total * t0
        y0 = cau_y + dy_total * t0
        x1 = cau_x + dx_total * t1
        y1 = cau_y + dy_total * t1
        d.add(Line(x0, y0, x1, y1, strokeColor=COMP_GREEN, strokeWidth=2.5))
    # Arrowhead
    aex = target_x - 16
    aey = target_y - 1
    d.add(Polygon([aex + 7, aey + 1, aex - 2, aey + 6, aex - 2, aey - 4],
                  fillColor=COMP_GREEN, strokeColor=COMP_GREEN, strokeWidth=0))

    # Cauchy box
    bw, bh = 106, 30
    d.add(Rect(cau_x - bw / 2, cau_y - bh / 2, bw, bh,
               fillColor=GREEN_LITE, strokeColor=COMP_GREEN, strokeWidth=1.8))
    d.add(String(cau_x - 48, cau_y + 5, 'Cauchy sequence',
                 fontSize=8.5, fontName='DV-B', fillColor=GREEN_DARK))
    d.add(String(cau_x - 48, cau_y - 8, 'T-IZ  - open passage',
                 fontSize=7.5, fontName='DV-I', fillColor=GREEN_DARK))

    d.add(String(40, 6,
                 'Three structures block return to zero. Cauchy convergence is the passage none of them govern.',
                 fontSize=8, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d


# ── DIAGRAM 3: Complete Cycle ─────────────────────────────────────────────────
def cycle_diagram():
    """T-SNAP -> ascending chain -> T-IZ -> T-SNAP' -> next branch."""
    dw, dh = TW, 1.9 * inch
    d = Drawing(dw, dh)

    cy = dh / 2
    margin = 38

    xs = [margin, dw * 0.27, dw * 0.50, dw * 0.73, dw - margin]
    # ⚠ NOT 'eps_(omega-1)' / 'last state'. Omega is a limit ordinal and has no predecessor, so
    # that ordinal does not exist; and R-I.1 of the formal document says the chain has NO last
    # element. Both errors also made the limit read as a successor step, which is the misreading
    # this document exists to block. A Drawing is invisible to every prose checker here.
    node_labels   = ['⊥', 'ε₀', '...', 'Sₙ', '⊥′']
    node_sublabels= ['null', 'first state', 'ascending', 'no last state', 'next null']
    node_colors   = [COMP_AMBER, COMP_BLUE, COMP_SLATE, COMP_BLUE, COMP_AMBER]
    arrow_labels  = ['T-SNAP', 'T3 (monotone)', 'strict ascent', 'T-IZ + T-SNAP']
    arrow_colors  = [COMP_GREEN, COMP_BLUE, COMP_BLUE, COMP_GREEN]

    for i in range(len(xs) - 1):
        x1, x2 = xs[i] + 14, xs[i + 1] - 14
        d.add(Line(x1, cy, x2 - 6, cy,
                   strokeColor=arrow_colors[i], strokeWidth=2))
        d.add(Polygon([x2, cy, x2 - 7, cy + 4, x2 - 7, cy - 4],
                      fillColor=arrow_colors[i], strokeColor=arrow_colors[i], strokeWidth=0))
        mx = (x1 + x2) / 2
        d.add(String(mx - len(arrow_labels[i]) * 2.8, cy + 17, arrow_labels[i],
                     fontSize=7, fontName='DV-I', fillColor=arrow_colors[i]))

    for i, (nx, lbl, sub, col) in enumerate(zip(xs, node_labels, node_sublabels, node_colors)):
        d.add(Circle(nx, cy, 13, fillColor=col, strokeColor=WHITE, strokeWidth=1.5))
        offset = -len(lbl) * 3.2
        d.add(String(nx + offset, cy - 5, lbl,
                     fontSize=9 if len(lbl) == 1 else 8, fontName='DVS', fillColor=WHITE))
        d.add(String(nx - len(sub) * 2.8, cy - 26, sub,
                     fontSize=6.5, fontName='DV-I', fillColor=COMP_SLATE))

    # Centered below the arrow-label row (cy+17) so it doesn't overflow the right edge
    d.add(String(dw / 2 - 52, cy + 28, 'DA-2: cycle repeats',
                 fontSize=7, fontName='DV-I', fillColor=COMP_GREEN))

    # No internal summary string: the caption below this drawing already carries the cycle in
    # words, and R-DIAGRAM says a caption duplicate comes out. It also sat at y=4, under the
    # min_y > 5 floor, so the bounds warning goes with it.
    return d


VERSION = '1.31'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-I_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-I Companion  |  Inside Zero  |  ' + version_date())
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-I Illustrated Companion',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header banner ──────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-I Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Going Forward Brings You Back to Zero', CS['title']),
        Paragraph('Inside Zero', CS['subtitle']),
        Paragraph('ZP Companion | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
        Paragraph(
            'This companion explains in plain language how an ascending chain of p-adic '
            'states converges, in the 2-adic metric, to zero  - and why the framework READS that '
            'limit as filling the bottom role again. Both that reading and whether the result is a '
            'NEW bottom or the one it started from are commitments of the framework, not things the '
            'chain proves. This is one result in the '
            'Zero Paradox project (ZP-I), '
            'a formal framework built on lattice algebra and 2-adic topology. '
            'Diagrams and real-world examples are included throughout. '
            'It is self-contained: ZP-A through ZP-E results used here are '
            'briefly introduced on first appearance. Every claim restates a result already '
            'proved in the corresponding technical document  - consult that document for the '
            'authoritative mathematics. (The ZP-E Illustrated Companion covers the upstream '
            'results in more depth if needed.)',
            CS['disc']),
    ]

    # ── What ZP-I Is Doing ─────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-I Doing?', CS['h1']))
    E.append(cbody(
        'ZP-E proved that the transition from ⊥ to the minimum nonzero state (ε₀) '
        'has its SHAPE fixed by the lattice axioms  - derived, not assumed; that the transition is taken is a further commitment. But '
        'ZP-E left a question open: what happens '
        'after the Snap? The chain of states ascends  - but does it ascend forever? And if '
        'not, what comes next?'))
    E.append(cbody(
        'ZP-I answers both questions with a single theorem: <b>T-IZ (Inside Zero)</b>. '
        'Every maximal ascending chain satisfying the IsDepthChain and IsStrictStateSequence conditions converges  - in the '
        '2-adic metric  - to zero, which the framework reads as the bottom role and then as a successor null. '
        'The chain does not go on forever; it reaches its limit at the ordinal limit, and on those '
        'readings the cycle begins again. The '
        'framework is not just a description of emergence. The derivation chain from T-SNAP through T-IZ is self-contained within the framework\'s axioms, and the two readings that carry it to a successor null are commitments stated alongside it.'))
    E.append(cbody(
        'The name "Inside Zero" refers to the geometry of the approach. The chain does '
        'not reach ⊥′ by turning around and going backward. It reaches ⊥′ by going '
        '<i>deeper</i>  - descending into the 2-adic structure until the depth of zero '
        'is reached from the inside. Forward motion is the mechanism of return.'))
    E.append(sp(4))

    # ── The Engine ─────────────────────────────────────────────────────────────
    E.append(Paragraph('What the No-Top Property Does', CS['h1']))
    E.append(cbody(
        'The state space (L, ∨, ⊥) has no top element: there is no maximum state. Stated on its own '
        'this looks like a limitation  - the algebra does not close. ZP-I reveals it is the opposite: '
        'it is what gives T-IZ room to run. ⚠ Two cautions. It is NOT ZP-A&#8217;s Remark R1, which is '
        'the no-subtraction restriction (Door 1 below); the order property is HasNoTop, in '
        'ZeroParadox/Order/Lattice.lean. And it does NOT put the limit outside L  - whether a limit '
        'escapes its carrier depends on the lattice, and the ordinals under max have no top while the '
        'chain n to n has least upper bound omega inside them.'))
    E.append(cbody(
        'Here is the logic. Each state in the ascending chain has a 2-adic valuation '
        'depth  - a measure of how many times 2 divides the state. As the chain ascends '
        '(ZP-A T3: every step is a join, every state is at least as large as the last), '
        'the depth increases. Because L has no top element, the chain never HAS to stop  - there is '
        'always a strictly greater element. Given that it keeps stepping, the depth grows without bound.'))
    E.append(cbody(
        'More than that: each step is a genuine advance. The depth does not merely grow '
        'eventually  - given the IsDepthChain condition, it increases by at least 1 at every transition. This is not an '
        'assumption about the chain. It follows from the ZP-A lattice axioms together with '
        'the IsDepthChain condition (which requires the chain\'s 2-adic depth to strictly '
        'track position): monotonicity, IsDepthChain, and IsStrictStateSequence  - the assumption that every '
        'step is a PROPER ascent  - together give strict depth growth at every step. No-top supplies the room '
        'for that ascent and is not itself a hypothesis of the theorem: <tt>h_strict_from_r1_t3</tt> binds '
        'IsDepthChain and IsStrictStateSequence, and HasNoTop appears nowhere in it '
        '(SemilatticeInstance.lean §Ib, with a NO-GO gauge exhibiting a no-top lattice whose chain never moves).'))
    E.append(cbody(
        'In the 2-adic metric, norms decrease geometrically: ‖S(n)‖ ≤ ‖S(0)‖ · 2<sup>−n</sup>. '
        'As n → ∞, the norm → 0. The chain converges to 0 in the 2-adic sense: '
        'the point with 2-adic valuation +∞. Reading that structural limit as filling the bottom role is the first commitment - the role condition is not statable in Q₂ - and calling the occupant ⊥′, a successor null, is the second; in this very chart the arc returns to the same 0.'))

    E.append(example_box('Real-world analogy  - The deepest point in the well', [
        'Imagine a well that has no bottom  - every level opens onto a deeper one. '
        'You descend, level by level, and each step takes you to a place more '
        '"inside" the well than the last. You never hit a floor within the well. '
        'But from the outside, there is a limit to all that descent  - the point '
        'that all those levels approach. That limit is the bottom the well '
        'itself generates by going deeper. In ZP-I, the 2-adic null is that bottom.',
    ]))
    E.append(sp(4))

    E.append(depth_diagram())
    E.append(ccaption(
        'The ascending chain S₀, S₁, S₂, ... descends in 2-adic depth as it ascends '
        'in the lattice. As depth → ∞, the 2-adic norm → 0. The chain converges '
        'to zero from inside, not by reversing direction.'))
    E.append(sp(4))

    E.append(remember_box(
        'The no-top property is not a limitation. It is what guarantees the road never ends: there is '
        'always somewhere further to go, so no chain halts for want of room. What makes a particular '
        'chain travel it is the assumption that every step is a proper ascent. No-top buys the '
        'POSSIBILITY; the strict-ascent condition is the OCCURRENCE. Where the road ENDS UP  - inside '
        'the lattice or outside it  - is a separate question no-top does not settle.'))
    E.append(sp(6))

    # ── The Geometry of Inside ─────────────────────────────────────────────────
    E.append(Paragraph('The Geometry of Going Inside', CS['h1']))
    E.append(cbody(
        'The 2-adic metric is unusual. In the ordinary real number line, "close to zero" '
        'means "small absolute value." In the 2-adic metric, "close to zero" means '
        '"divisible by a very high power of 2." These are different geometries, '
        'and in the 2-adic geometry, the natural motion of the ascending chain is '
        '<i>toward</i> zero, not away from it.'))
    E.append(cbody(
        'Think of it this way: each state in the chain is divisible by 2<sup>n</sup> for '
        'some n. As the chain ascends  - each state "larger" in the lattice sense  - '
        'it becomes divisible by higher and higher powers of 2. In 2-adic terms, this '
        'means it is getting closer to 0. The chain approaches zero by becoming '
        'more and more structured, not by becoming smaller.'))
    E.append(cbody(
        'The formal statement uses the geometric norm bound: '
        '&#8214;S(n)&#8214;₂ ≤ &#8214;S(0)&#8214;₂ ⋅ 2<sup>−n</sup>. '
        'This bound is derived in Lean 4 as theorem '
        '<tt>t_iz_r1_t3_geometric_bound</tt>  - using the p-adic norm formula and '
        'monotonicity of the valuation (T3 plus strict ascent). It means the norm is squeezed toward 0 '
        'by a geometric sequence, forcing convergence.'))
    E.append(sp(6))

    # ── T-IZ in Plain Language ─────────────────────────────────────────────────
    E.append(Paragraph('T-IZ in Plain Language', CS['h1']))
    E.append(cbody(
        'The theorem has four steps, and <tt>t_iz_complete</tt> '
        '(ZeroParadox/Valuation/SemilatticeInstance.lean §III-B) carries all four in Lean 4. '
        'Read what it joins and what it does not: step 1 is about 0 in Q₂, while steps 2 to 4 are '
        'about a terminal in a separate semilattice, and the theorem takes the bottom-role property '
        'as a hypothesis rather than deriving it for the limit. The two objects are never '
        'identified, so this is a conjunction of results, not a single chain:'))

    step_rows = [
        ['1. Cauchy convergence',
         'The chain has 2-adic norm ≤ 2⁻ⁿ at step n. Both the norm and the chain '
         'converge to 0. This is the topological core.',
         'The geometric norm bound  - proved (no sorryAx) (t_iz_cauchy, which binds the chain and '
         'the bound and no lattice at all; completeness of Q₂ is not consumed, because the limit is '
         'exhibited as 0 rather than obtained from a Cauchy criterion). '
         'Strict per-step growth follows from h_strict_from_r1_t3 + IsDepthChain  - verified as a derived condition. ✓'],
        ['2. ⊥-role identification',
         'Anything satisfying the join-identity condition IS that lattice\'s bottom. '
         'That the Cauchy limit 0 ∈ Q₂ satisfies it is the theorem\'s HYPOTHESIS, not '
         'its conclusion, and Q₂ carries no join, so the condition is not statable '
         'there — the two are distinct members of the bottom family, not one object (MC-1). Reading the occupant as a NEW null ⊥′ is a further commitment (C-DA2).',
         'ZP-E DA-2  - proved in Lean (t_iz_limit_is_new_null, axiom-free). '
         '✓ (the role only, given the hypothesis; not the novelty)'],
        ['3. DA-1 fires',
         'The successor semilattice carries a KleeneStructure (ZP-K). '
         'DA-1 applies at ⊥′ via the computational fixed-point argument.',
         'ZP-K KleeneStructure  - proved in Lean (da1_computational). ✓'],
        ['4. T-SNAP fires, on the reading that the limit fills the ⊥ role',
         'On that reading, at the computational fixed point T-SNAP fires: '
         'join ⊥ ε₀′ = ε₀′. Reading the 2-adic limit as the occupant is one commitment; '
         'calling that occupant a NEW null ⊥′ rather than the same ⊥ is a second.',
         'ZP-A bot_join  - proved in Lean. ✓ (the algebra, given the reading; '
         'neither the occupancy nor the novelty)'],
    ]

    col_widths = [TW * 0.21, TW * 0.49, TW * 0.30]
    hdr_row = [Paragraph(fix(h), CS['kr_hdr']) for h in ['Step', 'What it says', 'Source']]
    data_rows = [[Paragraph(fix(c), CS['kr_body']) for c in row] for row in step_rows]
    table_data = [hdr_row] + data_rows
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  COMP_BLUE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [colors.white, SLATE_LITE]),
        ('BOX',           (0,0), (-1,-1), 0.5, COMP_BLUE),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 7),
        ('RIGHTPADDING',  (0,0), (-1,-1), 7),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(table_data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    E.append(t)
    E.append(sp(8))

    E.append(key_result_box('Theorem T-IZ  - Inside Zero',
        'Every maximal ascending chain (S₀, S₁, S₂, ...) starting at ⊥, '
        'ascending monotonically by ZP-A T3, in a lattice with no top, and satisfying '
        'the IsDepthChain and IsStrictStateSequence conditions  - '
        'converges to zero in the 2-adic metric. Reading that limit as filling the bottom '
        'role is a commitment, and reading the occupant as ⊥′ a further one. '
        'On the first reading: DA-1 fires (the successor semilattice carries a '
        'KleeneStructure, per ZP-K) and T-SNAP fires. '
        'No axioms beyond those already proved in ZP-A through ZP-K are needed for the '
        'CONVERGENCE; the two readings are commitments rather than consequences of it. '
        'That the chain generates a genuinely NEW bottom, rather than arriving back at the '
        'one it started from, is the framework\'s commitment and not something the chain proves - '
        'in the 2-adic picture the arc comes back to the same 0.'))
    E.append(sp(6))

    # ── Three Doors, One Passage ───────────────────────────────────────────────
    E.append(Paragraph('Three Closed Doors, One Open Passage', CS['h1']))
    E.append(cbody(
        'ZP-I does not violate any of the irreversibility results already proved. '
        'The framework established three ways that return to ⊥ is blocked  - three '
        '"closed doors." T-IZ uses a fourth passage that none of the three doors govern.'))
    E.append(cbody(
        '<b>Door 1  - R1 (No subtraction):</b> In the lattice, there is no subtraction. '
        'You cannot join your way back to a smaller state. The ascending chain never '
        'subtracts  - every step is a join S<sub>n+1</sub> = S<sub>n</sub> ∨ α<sub>n</sub>. '
        'T-IZ does not subtract. The chain joins forward, and the 2-adic geometry '
        'means "forward" is also "deeper." R1 is not an obstacle to T-IZ, and it is not a source of '
        'it either. What leaves the chain somewhere to go is the separate order property HasNoTop, '
        'and what makes the valuation climb is strict ascent.'))
    E.append(cbody(
        '<b>Door 2  - C3 (No continuous path to zero):</b> ZP-B proved there is no '
        'continuous function γ : [0,1] → Q₂ with γ(0) ≠ 0 and γ(1) = 0. '
        'T-IZ uses a Cauchy sequence  - a discrete countable list of points  - not a '
        'continuous function on an interval. C3\'s prohibition covers continuous paths; '
        'it says nothing about Cauchy sequences. Proved in Lean: t_iz_c3_compatible.'))
    E.append(cbody(
        '<b>Door 3  - AX-G2 (No morphism to initial object):</b> ZP-G proved that no '
        'morphism within the categorical structure C leads back to the initial object. '
        'T-IZ is not a morphism within C. The transition to ⊥′ is the termination of '
        'C and the opening of a new C\'. AX-G2 quantifies over morphisms within a single '
        'category; it says nothing about transitions between categories.'))

    E.append(three_doors_diagram())
    E.append(ccaption(
        'Three structures block return to zero: algebraic (R1), topological (C3), '
        'categorical (AX-G2). The fourth passage  - Cauchy sequence convergence  - '
        'is not governed by any of them. T-IZ passes through the fourth door.'))
    E.append(sp(6))

    E.append(remember_box(
        'Irreversibility and inside convergence are not in tension. Irreversibility '
        '(R1, C3, AX-G2) governs motion <i>within</i> an instantiation: no '
        'subtraction, no continuous return, no categorical reversal. T-IZ governs '
        'what happens at the instantiation\'s ordinal limit: the chain converges, by Cauchy '
        'convergence, to something filling the bottom role  - a structure that irreversibility '
        'does not reach. Reading that occupant as its own SUCCESSOR null is the commitment.'))
    E.append(sp(6))

    # ── The Complete Cycle ─────────────────────────────────────────────────────
    E.append(Paragraph('The Complete Cycle', CS['h1']))
    E.append(cbody(
        'ZP-E gave us the beginning: T-SNAP (⊥ → ε₀ - shape derived, occurrence committed to). ZP-I gives us '
        'the end that is also a beginning: T-IZ (the chain → ⊥′). Together, they '
        'describe a self-contained derivation cycle. ZP-I is not merely an emergence result  - '
        'it is a structural account of a repeating pattern:'))
    E.append(cbody(
        '1. <b>T-SNAP</b> fires: ⊥ and ε₀ emerge. The branch opens.'
        '<br/>'
        '2. <b>T3 (monotonicity)</b>: states ascend. Each step adds informational content irreversibly.'
        '<br/>'
        '3. <b>No top</b>: the chain never has to stop  - there is always a strictly greater state. '
        'That it DOES keep ascending through ω state changes is the strict-ascent condition. '
        '(Not ZP-A&#8217;s R1, which is Door 1, no subtraction.)'
        '<br/>'
        '<b>Occurrence fence.</b> T-SNAP fixes the SHAPE of each step and does not establish that '
        'any step is taken; a model in which T-SNAP holds and nothing moves is exhibited in the Lean '
        'source. Throughout this document, "fires" narrates the framework&#8217;s commitment that instantiation occurs - before this note as well as after it. '
        '4. <b>T-IZ</b>: the chain\'s unbounded depth forces convergence to 0. Reading that '
        'limit as filling the ⊥ role  - and then as ⊥′  - are the two commitments; on them, '
        'DA-1 fires, T-SNAP fires again, and the branch closes.'
        '<br/>'
        '5. <b>DA-2</b>: ⊥′ becomes the foundation of the next instantiation. '
        'The next T-SNAP fires. The cycle repeats.'))

    E.append(cycle_diagram())
    E.append(ccaption(
        'The complete cycle: T-SNAP opens the branch, strict ascent climbs it, '
        'T-IZ closes it at the bottom role; DA-2 licenses reading that occupant as ⊥′, the next null. '
        'The derivation chain T-SNAP through T-IZ is self-contained within the framework\'s axioms.'))
    E.append(sp(4))

    E.append(cbody(
        '⊥ is not just the bottom of the lattice '
        ' - it is the attractor of the chain\'s own unbounded forward motion. '
        'The chain does not end by running out of structure. It ends by generating '
        'the next beginning.'))
    E.append(cbody(
        '<b>Note on "closed system":</b> The closure established by T-IZ is conceptual '
        ' - the formal derivation chain from T-SNAP through T-IZ to the ⊥ ROLE is '
        'self-contained within the framework\'s axioms (AX-B1, AX-G1, AX-G2, A1–A4); '
        'reading that role\'s occupant as a new null ⊥′ is C-DA2, a commitment. '
        'Whether the successor instantiation is part of a single formal structure or requires '
        'an extended framework is a question about multi-instantiation scope, not about '
        'the derivation itself.'))
    E.append(sp(6))

    # ── Lean 4 Status ─────────────────────────────────────────────────────────
    E.append(Paragraph('Lean 4 Verification', CS['h1']))
    E.append(cbody(
        'T-IZ is carried in Lean 4 (ZeroParadox/Valuation/SemilatticeInstance.lean). All four steps '
        'appear in one theorem, as a conjunction: the role step takes its property as a hypothesis '
        'and is never joined to the 2-adic limit. '
        'Axiom-free results are noted individually in the table below.'))

    E.append(lean_status_box([
        'h_strict_from_r1_t3 (§Ib)  - derives strict per-step valuation growth from '
        'IsDepthChain + IsStrictStateSequence (2-adic depth tracks position index). '
        'Closes R-IZ-A: strict growth is no longer a construction hypothesis. ✓',
        't_iz_norm_tendsto_zero  - norm bound ≤ 2⁻ⁿ implies norms converge to 0. '
        'Proved via squeeze_zero + tendsto_pow_atTop_nhds_zero_of_lt_one. ✓ (no sorryAx)',
        't_iz_conv_zero  - norm convergence implies sequence convergence in Q₂. '
        'Proved via tendsto_zero_iff_norm_tendsto_zero. ✓ (no sorryAx)',
        't_iz_r1_t3_geometric_bound  - derives &#8214;S(n)&#8214; ≤ &#8214;S(0)&#8214; ⋅ 2⁻ⁿ '
        'from the chain being nowhere zero and its valuation strictly increasing at every step. '
        'Uses Padic.norm_eq_zpow_neg_valuation + zpow_le_zpow_right₀. ✓',
        't_iz_cauchy  - the complete topological convergence result. ✓ (no sorryAx)',
        't_iz_limit_is_new_null  - anything satisfying the DA-2 null role IS that '
        'lattice\'s bottom (⊥-role identification). The role property is the HYPOTHESIS; '
        'that the Cauchy limit satisfies it is not established here and is not statable '
        'in Q₂. Reading that occupant as ⊥′ is C-DA2, a further commitment. '
        'Proved directly from da2_bottom_characterization. ✓ (axiom-free)',
        'da1_computational (ZP-K KleeneStructure)  - DA-1 fires at ⊥′ via the '
        'computational fixed-point argument. ✓',
        't_iz_complete (§III-B)  - carries all four steps in one theorem: convergence, '
        '⊥-role identification, DA-1, T-SNAP. All formal, no Kolmogorov complexity needed. ✓ '
        '(a conjunction, not a chain: the convergence step is about Q₂ and the role step about a '
        'terminal in a separate semilattice, taken as the hypothesis h_role and not identified '
        'with the limit)',
        't_iz_complete_from_axioms (§III-C, optional)  - replaces the h_bound hypothesis with three: '
        'the chain is nowhere zero, IsDepthChain, and IsStrictStateSequence. Only the last is a ZP-A '
        'lattice condition; IsDepthChain is the bridge saying the 2-adic valuation tracks the depth '
        'index, and it binds no semilattice. ✓ It also still carries h_role explicitly, which is the '
        'one hypothesis nothing here grounds.',
        'c_t_iz_null_balance  - a non-bottom state cannot fill the bottom role. '
        'Proved from c_da2_novelty. ✓',
        't_iz_c3_compatible  - C3 irreversibility and T-IZ coexist. '
        'Cauchy sequences ≠ continuous paths. ✓',
    ]))
    E.append(sp(8))

    E.append(key_result_box('ZP-I Summary',
        'T-IZ requires no new axioms. '
        'All four steps are carried in Lean 4 (ZeroParadox/Valuation/SemilatticeInstance.lean, '
        't_iz_complete) as a conjunction, with the role step\'s property taken as a hypothesis. '
        'The Kolmogorov complexity route is superseded: the AFA/Kleene path via '
        'ZP-K KleeneStructure closes Steps 2–4 without Kolmogorov complexity. '
        'The derivation is self-contained: T-SNAP opens each branch; '
        'T-IZ closes it at a limit READ as filling the bottom role; DA-2 licenses reading that '
        'occupant as the next branch\'s foundation. Emergence and return are derived as far as '
        'the CONVERGENCE and the role-recognition implication; that the limit is the role\'s '
        'occupant is a commitment. Their NOVELTY - that each branch ends at a fresh bottom rather '
        'than the one it began at - is assumed, on the same footing as T-SNAP\'s occurrence.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
