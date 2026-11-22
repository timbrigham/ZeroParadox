"""
Build ZP-H Illustrated Companion (v1.36)
Standalone companion for ZP-H: Categorical Bridge only.
ZP-G has its own companion (build_zpg_companion.py).

Accessibility target: 2 years of college math.
Assumes reader has read ZP-G companion. Builds on category/functor vocabulary.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF

def four_functor_diagram():
    """Central category C with four arrows going to four domain frameworks."""
    # dh must be tall enough for boxes at cy±65 (box half-height 17) plus caption (14) + margin
    dw, dh = TW, 3.4 * inch
    d = Drawing(dw, dh)

    cx = dw / 2
    # fixed — do not derive from dh; boxes at cy±65±17=135/55 pts; dh-10=235, min=5 ✓
    cy = 136

    # Central C box
    box_w, box_h = 64, 36
    bx1, by1 = cx - box_w/2, cy - box_h/2
    d.add(Rect(bx1, by1, box_w, box_h,
               fillColor=colors.HexColor('#F0EAF8'), strokeColor=colors.HexColor('#5B2D8E'),
               strokeWidth=1.5))
    d.add(String(cx - 8, cy - 6, 'C', fontSize=16, fontName='DV-B',
                 fillColor=colors.HexColor('#5B2D8E')))

    # Four target boxes — keep within [0, dh].
    # cy + 65 = top targets;  cy - 65 = bottom targets (box half-height 17 → min y = cy-82 > 14 ok)
    targets = [
        # (label, color, box center x, box center y, arrow end x, arrow end y)
        ('ZP-A\nLattice',   TEAL,   cx - 195, cy + 65,  cx - 150, cy + 52),
        ('ZP-B\np-Adic',    GREEN,  cx + 100, cy + 65,  cx + 142, cy + 52),
        ('ZP-C\nInfo',      RED,    cx - 195, cy - 65,  cx - 150, cy - 52),
        ('ZP-D\nHilbert',   INDIGO, cx + 100, cy - 65,  cx + 142, cy - 52),
    ]

    functor_labels = ['FA', 'FB', 'FC', 'FD']
    arrow_starts = [
        (cx - box_w/2, cy + box_h/4),
        (cx + box_w/2, cy + box_h/4),
        (cx - box_w/2, cy - box_h/4),
        (cx + box_w/2, cy - box_h/4),
    ]

    for i, (lbl, col, bx, by, aex, aey) in enumerate(targets):
        asx, asy = arrow_starts[i]
        # Draw arrow
        d.add(Line(asx, asy, aex, aey, strokeColor=col, strokeWidth=2))
        # Arrowhead
        import math
        dx, dy = aex - asx, aey - asy
        L = math.sqrt(dx*dx + dy*dy) or 1
        ux, uy = dx/L, dy/L
        px, py = -uy, ux
        d.add(Polygon([aex, aey,
                       aex - ux*9 + px*4, aey - uy*9 + py*4,
                       aex - ux*9 - px*4, aey - uy*9 - py*4],
                      fillColor=col, strokeColor=col, strokeWidth=0))
        # Functor label on arrow midpoint
        mx = (asx + aex) / 2
        my = (asy + aey) / 2
        fl = functor_labels[i]
        d.add(String(mx - 8, my + 4, fl[0], fontSize=9, fontName='DV-B', fillColor=col))
        d.add(String(mx - 2, my, fl[1], fontSize=6, fontName='DV-B', fillColor=col))

        # Target box
        tw, th = 70, 34
        d.add(Rect(bx - tw/2, by - th/2, tw, th,
                   fillColor=colors.white, strokeColor=col, strokeWidth=1.2))
        lines = lbl.split('\n')
        for j, line in enumerate(lines):
            ly_text = by + (len(lines) - 1 - j) * 11 - 6
            d.add(String(bx - tw/2 + 6, ly_text, line,
                         fontSize=8.5, fontName='DV-B', fillColor=col))

    d.add(String(dw/2 - 200, 16,
                 'Four maps from C into four frameworks: FB, FC, FD have Lean functor terms; FA has none',
                 fontSize=8, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def snap_convergence_diagram():
    """Shows the Binary Snap described by all four frameworks."""
    # 1.9 * 72 = 136.8 pts; content top = T-SNAP at cy+44 = 112.4, bottom = snap line at cy-40 = 28.4
    dw, dh = TW, 1.9 * inch
    d = Drawing(dw, dh)

    cy = 68  # fixed — do not derive from dh; T-SNAP label at cy+44=112 < dh-10=127 ✓
    lx = 30
    rx = dw - 30
    snap_x = dw / 2

    domain_colors = [TEAL, GREEN, RED, INDIGO]
    domain_labels = ['Lattice', 'p-Adic', 'Info', 'Hilbert']
    y_offsets = [30, 10, -10, -30]

    # Draw lines from left (0) to snap, then snap to right (e0)
    for i, (col, lbl, yoff) in enumerate(zip(domain_colors, domain_labels, y_offsets)):
        y = cy + yoff
        d.add(Line(lx + 20, y, snap_x - 10, y, strokeColor=col, strokeWidth=1.5))
        d.add(Line(snap_x + 10, y, rx - 20, y, strokeColor=col, strokeWidth=1.5))

    # Left dot: 0 — open circle (white fill, amber stroke) so dark amber text is legible
    d.add(Circle(lx + 18, cy, 8, fillColor=WHITE, strokeColor=COMP_AMBER, strokeWidth=2))
    d.add(String(lx + 12, cy - 6, '0', fontSize=9, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(lx + 4, cy - 20, '(⊥)', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))

    # Snap marker (vertical line)
    d.add(Line(snap_x, cy - 40, snap_x, cy + 40, strokeColor=BLACK, strokeWidth=2))
    d.add(String(snap_x - 18, cy + 44, 'T-SNAP', fontSize=8, fontName='DV-B', fillColor=BLACK))

    # Right dot: ε₀ — open circle (white fill, indigo stroke) so indigo text is legible
    d.add(Circle(rx - 18, cy, 8, fillColor=WHITE, strokeColor=INDIGO, strokeWidth=2))
    d.add(String(rx - 26, cy - 6, 'ε₀', fontSize=8, fontName='DV-B', fillColor=INDIGO))
    d.add(String(rx - 30, cy - 20, '(first state)', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))

    # Labels on right side
    for i, (col, lbl, yoff) in enumerate(zip(domain_colors, domain_labels, y_offsets)):
        y = cy + yoff
        d.add(String(rx - 16, y - 5, lbl, fontSize=7, fontName='DV-I', fillColor=col))

    return d

VERSION = '1.36'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-H_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-H Companion  |  Functor Coherence  |  ' + version_date())
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-H Illustrated Companion',
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
    hdr = Table([[Paragraph('ZP-H Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Four maps, four facts', CS['title']),
        Paragraph('Functor Coherence', CS['subtitle']),
        Paragraph('ZP Companion | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal document — its results are proved in ZP-H Categorical Bridge '
            'or come from the other documents, papers and named theorems it cites, and a commitment or '
            'reading it mentions is not a result. Consult ZP-H for the '
            'authoritative mathematics. This document assumes familiarity with the ZP-G '
            'Illustrated Companion.',
            CS['disc']),
    ]

    # ── What ZP-H is doing ─────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-H Doing?', CS['h1']))
    E.append(cbody(
        'ZP-G built an abstract category C and proved that its structure — an initial object '
        'with no return morphisms — captures the essential shape of the Zero Paradox. But an '
        'abstract category on its own is just a skeleton. ZP-H puts flesh on the bones.'))
    E.append(cbody(
        'ZP-H constructs four explicit <b>functors</b> — structure-preserving maps — from the '
        'abstract category C into the four concrete mathematical frameworks of the Zero '
        'Paradox: the lattice algebra of ZP-A, the p-adic topology of ZP-B, the information '
        'theory of ZP-C, and the Hilbert space of ZP-D.'))
    E.append(cbody(
        'The result: in Lean, FB, FC and FD send 0 to an initial object of ℕ-indexed stand-ins (for FB, '
        'Q₂BallDepth; in TopCat its floor is terminal, not initial); FA has no functor term, and its '
        'witness is ℕ with 0 initial. Each framework has its own proved fact, none derived from another '
        'or from a functor. That the four are windows on one thing is the framework\'s reading; T-H3, '
        'the theorem that states the four facts together, itself relates none of them to another. Where they look alike, the likeness reflects a shared foundation (A1-A4, '
        'AX-B1 and the modelling commitment CC-1, S₀ = ⊥, restated in ZP-J, not forced), not independent '
        'confirmation.'))
    E.append(four_functor_diagram())
    E.append(ccaption(
        'ZP-H constructs four maps on paper from the abstract category C (center) into the four '
        'domain frameworks. In Lean, three are functors from ℕ into ℕ-indexed stand-ins (fb_functor, '
        'fc_functor, fd_functor), each sending 0 to an initial object there; FA has no functor term, '
        'and its witness is natSLat_initial_grounding (see T-H1).'))
    E.append(sp(6))

    # ── The structural floor ───────────────────────────────────────────────────
    E.append(Paragraph('The Structural Floor', CS['h1']))
    E.append(cbody(
        'Before the categorical machinery, it helps to understand one key property that ⊥ '
        'has in every ZP framework. ⊥ has nothing below it: a structural floor. How it is '
        'approached from above depends on the setting. In ℕ a path that drops at every step until it reaches 0 '
        'gets there in finitely many steps (descent_with_strict_steps_reaches_floor), and in a finite power set so does '
        'removing one element at a time (ps_descent_reaches_floor); in the 2-adic metric the doubling orbit converges to it '
        'without ever reaching it (see the box below), so there ⊥ is a limit point of the elements '
        'above it.'))
    E.append(cbody(
        'The simplest example of this property is one most readers have already encountered: '
        'the collection of all subsets of a set. Take any set S — say <i>{a, b, c}</i> — '
        'and collect every possible subset: ∅, {a}, {b}, {c}, {a, b}, and so on up to S '
        'itself. Order them by inclusion: A ≤ B means A is contained in B. The empty set ∅ '
        'sits at the bottom, below everything.'))
    E.append(cbody(
        'Now ask: can a sequence of nonempty subsets get "closer and closer" to ∅? No. Every '
        'nonempty subset has at least one element — its size is at least 1. There is no subset '
        'with size between 0 and 1, because you cannot have half an element. The gap between ∅ '
        'and every nonempty subset is exactly 1, a discrete, combinatorial gap with no room to '
        'subdivide. In this discrete setting, no element is a limit point of elements above it — '
        'there is no way to subdivide the gap of one element. ∅ has this property in its most '
        'extreme form: it sits below the entire lattice, so the minimum gap is between nothing '
        'and something. No sequence of nonempty sets closes that gap.'))
    E.append(cbody(
        'The floor appears in the ZP framework too, approached from above for deeper reasons. In ZP-B, the '
        '2-adic valuation v₂ assigns 0 the value +∞: v₂(0) = +∞, meaning 0 is divisible by '
        'every power of 2. Every nonzero element has a finite v₂. No nonzero element closes '
        'this valuation gap: a nonzero element always has finite v₂, while '
        '0 has infinite v₂, and no finite accumulation of finite values reaches infinity. '
        'In the 2-adic integers ℤ₂, sequences of nonzero elements can get metrically close to 0, '
        'but the valuation gap cannot be closed at any finite step (q2Val_unique: only 0 has '
        'infinite v₂ in ℤ₂). '
        'In ZP-A, ⊥ is the bottom of the lattice and the axioms forbid any non-trivial return. '
        'In ZP-C, the informational cost of approaching ⊥ diverges — infinite '
        'cost means no finite path reaches it. In ZP-D, the basis vector e₀ is orthogonal to '
        'e₁, the image of ε₀: their inner product is 0 (T4, t4_snap_orthogonal). The state vectors '
        'are orthonormal, so any two distinct ones sit exactly √2 apart (t4_state_gap): approach to '
        'the floor e₀ is a jump of that fixed size, never a sequence of state vectors drawing closer.'))
    E.append(remember_box(
        'The power set example shows that the structural floor property is not exotic: it appears '
        'in the most elementary object in set theory. What is non-trivial is how that floor is '
        'approached from above, which differs across four analytic settings — topology, algebra, '
        'information theory, Hilbert space — each with its own structural reason, given in the '
        'paragraph above. In ℚ₂, where the role is played by 0, the unique point of norm 0, the floor is '
        'approached but not reached in finitely many steps: the doubling orbit of any nonzero point '
        'converges to 0 in the 2-adic metric (doubling_orbit_tendsto_zero) and still never lands on 0 '
        'at any finite step (padic_orbit_never_reaches_zero). That ⊥ has nothing below it holds in '
        'every setting by A1–A4 (ZP-A T1, T2); the four settings also share AX-B1 and the modelling '
        'commitment CC-1 (S₀ = ⊥, restated in ZP-J, not forced). '
        'ZP-H states these four reasons side by side and proves no theorem relating one to another.'))
    E.append(sp(6))

    # ── Morphisms of C ─────────────────────────────────────────────────────────
    E.append(Paragraph('What Are the Morphisms of C?', CS['h1']))
    E.append(cbody(
        'ZP-G defined C abstractly — objects, morphisms, composition, identity — without '
        'specifying what the morphisms actually <i>are</i>. That abstraction was intentional: '
        'the theorems in ZP-G hold for any category with AX-G1 and AX-G2, regardless of the '
        'morphism content.'))
    E.append(cbody(
        'ZP-H fills in the detail (Definition D-H1): morphisms in C are <b>state transitions</b>. '
        'A morphism f: A → B represents a net addition of informational content — you can '
        'only move forward. Morphisms compose by sequential accumulation: going from A to B '
        'then B to C produces a state at least as large as B. This design choice is what '
        'makes the four functors well-defined.'))
    E.append(remember_box(
        'D-H1 is a design commitment, not a derived result. A different choice of morphism '
        'structure would produce different functors. ZP-H states this explicitly: the choice '
        'is the one that maps correctly to all four domain frameworks, and it is not '
        'laundered as a derivation.'))
    E.append(sp(6))

    # ── The four functors ──────────────────────────────────────────────────────
    E.append(Paragraph('The Four Functors', CS['h1']))
    E.append(cbody(
        'Each construction takes the abstract objects and morphisms of C and maps them into '
        'one of the four frameworks, checking on paper that the mapping preserves composition, '
        'identity, and the privileged role of the initial object (for FB, in its stand-in). '
        'The Lean status of each is stated at the end of its paragraph.'))
    E.append(cbody(
        '<b>FA (Lattice):</b> The initial object 0 maps to ⊥ (bottom of the lattice). '
        'Each morphism f: A → B maps to the join operation ⊥ ∨ S = S that witnesses the '
        'transition. Composition corresponds to iterated joins. The forward-only structure '
        'of C maps to the monotone structure of ZP-A. In Lean, FA has no functor term. Its witness is the '
        'ZPCategory instance on ℕ, where 0 is initial in the order category of ≤ (natSLat_initial_grounding), '
        'sorry-free.'))
    E.append(cbody(
        '<b>FB (p-Adic Topology):</b> The initial object 0 maps to the element 0 ∈ ℚ₂. '
        'Each morphism maps to a discrete jump across a clopen boundary — formalized as '
        'antitone depth in Q₂BallDepth. Composition corresponds to sequential jumps. '
        'In Lean, FB is a sorry-free functor in two forms: fb_functor lands in Q₂BallDepth, '
        'an ℕ-indexed stand-in that orders the nested balls around 0 by depth, and fB_functor '
        'lands in TopCat, the category of all topological spaces, where 0 is the limit of the '
        'shrinking balls. In the stand-in, AX-G2 holds by antisymmetry: a morphism from depth m '
        'to depth 0 means m ≤ 0, so m = 0. The irreversibility of ZP-B C3 (no continuous path '
        'returns to 0 in ℚ₂) is the domain analogue of that fact, proved in ZP-B.'))
    E.append(cbody(
        '<b>FC (Information Theory):</b> In Lean the initial object 0 maps to depth 0 of the stand-in and to '
        'Fin 0, the empty type, in the Kleisli category of the probability monad, where it is initial. ZP-C\'s '
        'information model reads the bottom as the point mass P = (1, 0), and no distribution lives on the '
        'empty type, so the two models differ at 0. Each morphism maps to an informational transition with '
        'a non-negative cost measured in bits. The fundamental transition costs exactly '
        '1 bit (ZP-C T1b). The unreachability of 0 in ZP-G (T3) and the diverging '
        'surprisal of ZP-C T2 hold together (T-H2), a pair of separately proved results. In Lean, FC is a sorry-free functor in two forms: fc_functor '
        'lands in InfoDepth, an ℕ-indexed stand-in, and fC_functor lands in KleisliCat PMF, '
        'the Kleisli category of the probability monad.'))
    E.append(cbody(
        '<b>FD (Hilbert Space):</b> In Lean the initial object 0 maps to depth 0 of the stand-in and to '
        'the zero module of ModuleCat ℂ. ZP-D\'s vector model reads the point 0 of ℚ₂ as the basis vector e₀, '
        'which the zero module does not contain, so the two models differ at 0. '
        'Each morphism maps to an orthogonal extension — a step to a perpendicular basis '
        'vector. The Binary Snap becomes a right-angle turn in state space. The design '
        'commitment DP-1 (orthogonality represents clopen separation) is inherited here. '
        'In Lean, FD is a sorry-free functor in two forms: fd_functor lands in HilbDimDepth, '
        'an ℕ-indexed stand-in, and fD_functor lands in ModuleCat ℂ, the category of '
        'ℂ-modules.'))
    E.append(cbody(
        '<b>Where the two axioms hold.</b> ZP-G assumes both axioms of C. In the targets, '
        'each one holds in some categories and fails in others. AX-G1 says there is an initial '
        'object and no terminal object (an object that every object maps into by exactly one '
        'morphism). The ℕ-indexed '
        'stand-ins have no terminal object, because depth n always has depth n + 1 above it. '
        'TopCat, ModuleCat ℂ and KleisliCat PMF each have one: the one-point space, the zero '
        'module and the one-point type. For FA, a lattice has a terminal element exactly when '
        'it has a top element, so AX-G1 there needs the optional ZP-A hypothesis HasNoTop; '
        'ZP-A\'s two-state carriers have a top. AX-G2 says nothing other than 0 maps into 0. It holds wherever '
        'the category is built from a partial order with a least element, by antisymmetry, as in '
        'ZP-A\'s semilattice and in the three stand-ins. It fails in ModuleCat ℂ: the zero map '
        'sends every module into the zero module, including modules that are not zero.'))

    E.append(example_box('Real-world analogy — Four instruments', [
        'Imagine four instruments, violin, trumpet, piano and voice, each playing a phrase. '
        'A listener may hear one melody in all four. ZP-H does not show that about ZP-A through '
        'ZP-D: it states four facts, one from each framework, side by side, and T-H3 itself relates '
        'none of them to another. Hearing them as four instruments playing one mathematical structure is the '
        'framework\'s reading, the listener\'s ear rather than the score.',
    ]))
    E.append(sp(6))

    # ── T-H1: Universal property preserved ─────────────────────────────────────
    E.append(key_result_box('T-H1: Each Functor Preserves the Initial Object',
        'For each of the four functors, the image of 0 is an initial object in the target '
        'framework (for FB, in its stand-in) — a universal source from which every other object '
        'has a unique morphism. '
        'The privileged status of 0 is not an artifact of the abstract category. The FB '
        'stand-in is Q₂BallDepth. In TopCat the FB leg fails: there the floor {0} is a '
        'one-point space, which is terminal and not initial. In Lean this is checked for FB, FC and FD '
        'in their ℕ-indexed stand-ins (fb_preserves_initial, fc_preserves_initial, fd_preserves_initial); '
        'FA has no functor term, and its witness is 0 initial in ℕ\'s order category.'))
    E.append(sp(6))

    # ── T-H2: Singularity compatibility ────────────────────────────────────────
    E.append(Paragraph('Two Characterizations That Hold Together', CS['h1']))
    E.append(cbody(
        'ZP-G said: there is no morphism from any non-initial object back to 0 (AX-G2). '
        'ZP-C said: the informational cost of approaching 0 is unbounded '
        '— the accumulated surprisal grows without bound. These look like two different '
        'statements about the same thing. Are they compatible?'))
    E.append(cbody(
        'T-H2 proves they are: both hold at once. It pairs two separately proved results, '
        'ZP-G Lemma T3 and ZP-C Theorem T2, and uses neither to prove the other. In ZP-C, ask: what happens to surprisal as you approach '
        '0 along an infinite path? The answer is divergence. In ZP-G, ask: can you reach '
        '0 by a morphism from outside? The answer is no. '
        'Read informally, if infinite cost is required to reach 0, then no finite morphism can '
        'accomplish it. That link is a reading, not a theorem.'))

    E.append(key_result_box('T-H2: Singularity Compatibility',
        'The categorical singularity (no return morphism to 0) and the information-theoretic '
        'singularity (diverging surprisal approaching 0) both hold. T-H2 proves them together, '
        'as a conjunction of two separately proved results, and uses neither to prove the other.'))
    E.append(sp(6))

    # ── T-H3: The Binary Snap ──────────────────────────────────────────────────
    E.append(Paragraph('The Binary Snap: Four Domain Facts', CS['h1']))
    E.append(cbody(
        'The Binary Snap is the transition from 0 to the first non-initial object. '
        'In the abstract category C, it is the unique morphism from 0 to ε₀ — guaranteed '
        'to exist by AX-G1 and to be unique by the definition of an initial object. '
        'In ZP-E, AX-1 (Binary Snap Causality) is retired. Its content was split in two: the shape of the snap is proved, '
        'as Theorem T-SNAP, and that the snap occurs is stated separately: it follows from the occurrence commitment '
        'together with DA-1 (closed given DP-2). The occurrence commitment is stated in two charts, execution and slot, in the header of ZeroParadox/Order/Snap.lean (indexed in ZeroParadox/Order/SnapCannotBe.lean &#167; II and CLAIMS.md), the slot chart as the hypothesis hw of t_snap_of_fires_once, that the tape fires at some stage, beside the theorem trials_fires_once that, for independent stages each firing with probability p, 0 &lt; p &#8804; 1, firing at some stage has probability one, which names no tape (ZeroParadox/Information/CrossingTrials.lean &#167; VIII).'))
    E.append(cbody(
        'T-H3 (th3_snap_all_functors) conjoins four separately proved domain facts, listed in the '
        'T-H3 box below; none is derived from another or from a functor, its type names no functor, and it '
        'relates no fact to another. The bullets here are not its conjuncts: they are how the framework '
        'reads the Snap in each setting.'))
    E.append(cbody(
        '• In lattice algebra: the first join — ⊥ ∨ ε₀ — producing the first non-bottom state.'
        '<br/>'
        '• In p-adic topology: a discrete jump from 0 to ε₀ across a clopen boundary, '
        'irreversible by the topological structure of ℚ₂.'
        '<br/>'
        '• In information theory: an informational transition costing exactly 1 bit (ZP-C T1b).'
        '<br/>'
        '• In Hilbert space: an orthogonal shift from basis vector e₀ to e₁, with '
        'inner product ⟨e₀, e₁⟩ = 0.'))

    E.append(snap_convergence_diagram())
    E.append(ccaption(
        'The framework\'s reading, drawn as one line per framework: each of the four has a transition '
        'of the Binary Snap\'s shape. No fact is derived from another, and T-H3 itself '
        'relates none of the four facts to another. The vertical line marks the moment of the Snap. '
        'Left: ⊥. Right: ε₀.'))
    E.append(sp(6))

    E.append(remember_box(
        'Where the four frameworks look alike, the likeness reflects coherence, not independent confirmation. '
        'All four share the same axioms — A1-A4 (lattice axioms), AX-B1 (binary existence) '
        '— and the modelling commitment CC-1 (S₀ = ⊥, restated in ZP-J, not forced). A transition of the '
        'snap\'s shape appears in each because those foundations are built into each framework, '
        'not because four separate arguments from unrelated starting points converged. That the four are '
        'one snap is the framework\'s reading; T-H3 itself relates none of them to another.'))
    E.append(sp(6))

    E.append(key_result_box('T-H3: The Binary Snap, Four Domain Facts',
        'T-H3 conjoins four domain facts, each proved in its own framework: the lattice join '
        'c₀ ∨ c₁ = c₁, no continuous path in ℚ₂ back to 0, a JSD of exactly 1 bit, and '
        'orthogonal basis vectors. No functor appears in its type and no fact is used to prove '
        'another. Read side by side, the framework takes them '
        'as coherence across shared structural '
        'commitments (A1-A4, AX-B1, CC-1), not independent replication. '
        'T-SNAP is a derived theorem inherited here from ZP-E. '
        'The only additional design premise is DP-1 (ZP-D). '
        'CC-1 (S₀ = ⊥) is a modelling commitment: ZP-J restates it as an equivalence with starting at '
        'a Quine atom, which expresses the choice through a role without forcing it.'))
    E.append(sp(8))

    E.append(cbody(
        '<b>What this means:</b> The shape of the snap is proved as Theorem T-SNAP. Each of the other '
        'three frameworks has its own separately proved fact, which the framework reads as the snap\'s '
        'counterpart there. ZP-H states the four together; that they are one snap translated, and so not '
        'a construct of any one framework, is a reading, not a theorem.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
