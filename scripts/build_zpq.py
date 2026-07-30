"""
Zero Paradox — ZP-Q: The Frame-Change PDF Builder
Version 1.1 | July 2026

v1.2: BEDROCK framing correction (Tim, 2026-07-30). The layer identified the SNAP with the frame-change; the Lean does not. Read at source, snap_is_frameflip proves the tower limit's two chart-readings and contains NO snap transition (no c0->c1, no bot-covers-a, no bot->eps0); catseam_is_frameflip proves the seam is a FIXED POINT of the flip (initial AND terminal), not a flip. What the three *_is_frameflip theorems establish is the exchange of the two poles and the point where they coincide. THE FRAME-CHANGE IS THE POLE EXCHANGE - bottom read as both 0 and infinity - and the SNAP is one covering step off the zero face (HasFirstStep, AX-B1, a commitment). Merging them is what made it look paradoxical that a frame-change reverses while the snap does not. Four sites corrected; the declaration handles are retained per the CC-2/MC-1 convention (cross-references stay valid) with the overclaim flagged in each Lean docstring. Also records that fork_collapse_iff (iii) is the general min=max condition, with epsilon0_min_eq_max, selfApp_bot_is_both_extremal and the categorical seam as its instances.
v1.1: Frame-change prose precision — the tower's ENCODINGS converge to ⊥ (a new bottom) and, via rInv,
diverge to ∞; ε₀ is never "realised as ⊥/the ceiling" (ε₀ ≠ ⊥). The theorems (snap_is_frameflip) were
always about the encodings; only the prose gloss is corrected.
v1.0: Initial release. Synthesis layer, ZP-P's sequel. The snap ⊥ → ε₀ is a change of point of view.
Three tiers: (§I) the abstract frame-flip schema — over any complete lattice, order-duality swaps the
fork's two closures (lfp ↔ gfp) and the fork collapses at the diagonal fixed point (fork_is_frameflip,
ForkFrameChange.lean; choice-free [propext, Quot.sound]). (§II) the instance catalogue — the per-domain
frame-flips: valuation (snap_is_frameflip / the Riemann sphere, SnapFrameChange.lean; RiemannSphere.lean),
category (catseam_is_frameflip, SeamFrameChange.lean), set theory / computability / Hilbert / information
referenced to their home layers; reals the NO-GO counterexample. (§III) the universal form and its walls —
the order-theoretic universal HOLDS; the categorical Lawvere universal is a PROVEN WALL (category-relative,
Cantor; Lawvere.lean); the cross-domain identity is a type boundary. "The fence is the bridge." Follows all
rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.2'
FIRST_RELEASED = 'July 2026'

from reportlab.graphics.shapes import Drawing, Circle, Ellipse, PolyLine, String, Polygon
from reportlab.lib.colors import HexColor


def _bez(p0, p1, p2, p3, n=22):
    pts = []
    for i in range(n + 1):
        t = i / n; u = 1 - t
        pts += [u*u*u*p0[0] + 3*u*u*t*p1[0] + 3*u*t*t*p2[0] + t*t*t*p3[0],
                u*u*u*p0[1] + 3*u*u*t*p1[1] + 3*u*t*t*p2[1] + t*t*t*p3[1]]
    return pts


def _qbez(p0, p1, p2, n=10):
    pts = []
    for i in range(n + 1):
        t = i / n; u = 1 - t
        pts += [u*u*p0[0] + 2*u*t*p1[0] + t*t*p2[0],
                u*u*p0[1] + 2*u*t*p1[1] + t*t*p2[1]]
    return pts


def sphere_figure():
    # dh = 250 pts; content top ~229 (< dh-10), bottom ~17 (> 5) — within the diagram bounds gate.
    dw, dh = TW, 250
    d = Drawing(dw, dh)
    cx, cy, R = dw / 2, 122, 88
    c0 = HexColor('#1c6f88'); cI = HexColor('#a4741c')
    cseam = HexColor('#3b352c'); cwire = HexColor('#8496a8')
    csil = HexColor('#b7a988'); cmut = HexColor('#6d6754')
    # sphere silhouette, one meridian, the equator seam
    d.add(Circle(cx, cy, R, strokeColor=csil, fillColor=None, strokeWidth=1.1))
    d.add(Ellipse(cx, cy, R * 0.55, R, strokeColor=cwire, fillColor=None, strokeWidth=0.7))
    d.add(Ellipse(cx, cy, R, R * 0.26, strokeColor=cseam, fillColor=None, strokeWidth=1.4))
    # the tower: nested balls of Z_p, from the seam down toward the floor
    d.add(Ellipse(cx, cy - 24, 58, 13, strokeColor=c0, fillColor=None, strokeWidth=0.8))
    d.add(Ellipse(cx, cy - 46, 36, 8, strokeColor=c0, fillColor=None, strokeWidth=0.8))
    d.add(Ellipse(cx, cy - 66, 17, 4, strokeColor=c0, fillColor=None, strokeWidth=0.8))
    # the inversion / bridge arc, floor -> ceiling (bows left)
    d.add(PolyLine(points=_bez((cx, cy - R), (cx - 84, cy - 50), (cx - 84, cy + 50), (cx, cy + R)),
                   strokeColor=cI, strokeWidth=1.4))
    # the one-way fall, seam -> floor
    d.add(PolyLine(points=_qbez((cx - 30, cy - 21), (cx - 18, cy - 58), (cx, cy - R)),
                   strokeColor=c0, strokeWidth=1.7))
    d.add(Polygon(points=[cx - 4, cy - R + 9, cx + 4, cy - R + 9, cx, cy - R + 1],
                  fillColor=c0, strokeColor=c0))
    # poles
    d.add(Circle(cx, cy + R, 4, fillColor=cI, strokeColor=cI))
    d.add(Circle(cx, cy - R, 4, fillColor=c0, strokeColor=c0))
    # labels (Unicode direct, per the diagram standards)
    d.add(String(cx, cy + R + 8, '∞', fontName='DV', fontSize=13, fillColor=cI, textAnchor='middle'))
    d.add(String(cx, cy - R - 14, '0 = ⊥', fontName='DV', fontSize=11, fillColor=c0, textAnchor='middle'))
    d.add(String(cx + R + 6, cy - 2, 'seam  ‖x‖ = 1', fontName='DV', fontSize=8.5, fillColor=cmut, textAnchor='start'))
    d.add(String(cx - 14, cy - 60, 'one way ↓', fontName='DV', fontSize=8.5, fillColor=c0, textAnchor='start'))
    d.add(String(cx - 96, cy + 2, 'z → 1/z', fontName='DV', fontSize=8.5, fillColor=cI, textAnchor='start'))
    return d


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-Q_The_Frame_Change.pdf')
    print(f'[build_zpq] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-Q: The Frame-Change',
                   'ZP-Q: The Frame-Change', 'Version ' + VERSION)
    E = []

    print('[build_zpq] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-Q: The Frame-Change', S['title']),
        Paragraph('&#8869; &#8594; &#949;<sub>0</sub> as a change of point of view', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Synthesis layer, the sequel to ZP-P. The abstract frame-flip schema is proved '
            'sorry-free and choice-free in Lean 4 (ForkFrameChange.lean); the per-domain instances '
            'are witnessed in their home layers (the valuation instance &#8212; the Riemann sphere '
            '&#8212; in SnapFrameChange.lean / RiemannSphere.lean; the categorical instance in '
            'SeamFrameChange.lean). The universal cross-category identity is not a theorem &#8212; it '
            'meets a proven wall (Cantor; Lawvere.lean). Adds no axiom; the bottom itself is never '
            'positively represented.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'The Zero Paradox proves the snap &#8869; &#8594; &#949;<sub>0</sub> as a theorem; ZP-Q is about the '
        'BOTTOM&#8217;s two-facedness, which is a different object from the snap. Across every layer the '
        'bottom shows the same two features: it '
        'is a fixed point &#8212; a zero &#8212; that carries an infinitude (v<sub>2</sub>(0) = '
        '&#8734;, unbounded surprisal, the self-referential closure), and every map to it runs one '
        'way and reverses only under an inversion that swaps the two poles. These are not two facts. '
        'They are two faces of one self-dual object, and the inversion is the <i>frame-change</i>. '
        '<b>The frame-change is that pole exchange &#8212; &#8869; being read as both 0 and &#8734; &#8212; '
        'and it is NOT the snap.</b> The snap is one covering step off the zero face '
        '(&#8869; &#8918; a, HasFirstStep), which is AX-B1, a modelling commitment; the frame-change is an '
        'involution and is proved. Merging the two is what makes it look paradoxical that a frame-change '
        'reverses while the snap does not: they were never the same map. '
        'Read from one frame the frame-change is a <i>bridge</i> (it joins the poles continuously); '
        'read from the other it is a <i>fence</i> (a boundary the map cannot cross). ZP-Q records the '
        'abstract frame-flip schema, its per-domain instances, and the universal form together with '
        'the wall that bounds it.'))
    E.append(body(
        'Like ZP-P, this is a synthesis layer, organised in three tiers held to three standards of '
        'proof. Tier 1 (Section I) is the abstract schema, proved in Lean over a complete lattice: it '
        'extends ZP-P&#8217;s fork with its second face, the order-duality that swaps the two '
        'closures. Tier 2 (Section II) is the instance catalogue: each domain&#8217;s frame-change is '
        'a theorem in its home layer, and the valuation instance is the framework&#8217;s originating '
        'figure, the p-adic Riemann sphere. Tier 3 (Section III) is the universal form and its walls: '
        'the order-theoretic universal holds, the categorical (Lawvere) universal is a proven wall, '
        'and the cross-domain identity is a type boundary. The fences in Section III are load-bearing '
        '&#8212; and they turn out to be built from the same diagonal as the bridges.'))
    E.append(remark_box(
        'A note on what is drawn',
        [
            'ZP-Q characterises the bottom apophatically, and the register is itself frame-relative. '
            'Seen from outside &#8212; from any frame that looks at &#8869; &#8212; there is no '
            'interior: nothing sits behind the description waiting to be opened. The boundary is the '
            'whole of it. &#8869; is the seam the frame-change joins, or the tear it leaves, a '
            'boundary of measure zero, all edge and no inside (read flat, this is the Quine atom '
            '&#8869; = {&#8869;} from without &#8212; a single node, not a region &#8212; and the '
            'tear on the sphere &#8212; a discontinuity, not a region).',
            'Seen from &#8869;&#8217;s own frame &#8212; inside the self-reference &#8212; the same '
            'point is the opposite: infinite depth. v<sub>2</sub>(0) = &#8734;; the endless regress '
            '&#8869; &#8712; &#8869; &#8712; &#8869;; unbounded surprisal. No-interior and '
            'infinite-interior are the 0 &#8596; &#8734; poles of one coin, swapped by the '
            'frame-change: what has no thickness from without has nothing but depth from within. So '
            'the bottom is not an object behind the boundary &#8212; it is the boundary, whose own '
            'thickness is the frame-flip.',
        ]
    ))
    E.append(hr())

    # ── Section I: The Frame-Flip Schema (Tier 1) ─────────────────────────────────
    print('[build_zpq] Building Section I...')
    E += [
        Paragraph('Section I: The Frame-Flip Schema (Tier 1)', S['h1']),
        hr(),
    ]

    E.append(body(
        'ZP-P recorded the fork&#8217;s first face: over a complete lattice a monotone self-map f has '
        'a least fixed point (lfp f, the well-founded / inductive closure, &#956;) and a greatest '
        'fixed point (gfp f, the non-well-founded / coinductive closure, &#957;), and the fork '
        'collapses to a single point &#8212; the diagonal fixed point &#8869; &#8212; exactly when f '
        'has a unique fixed point (fork_collapse_iff). ZP-Q adds the second face. The two closures are '
        'the two <i>charts</i>; the <i>frame-change</i> is the order-duality that carries one to the '
        'other. It is the abstract form of the concrete frame-changes below: the p-adic inversion '
        'z &#8614; 1/z, the categorical op-duality, lattice complementation.'))

    E.append(def_box(
        'Definition: the frame-change (ForkFrameChange.lean)',
        [
            'For a complete lattice &#945; and a monotone self-map f : &#945; &#8594; &#945;:',
            '  the two charts are lfp f (&#956;, the well-founded closure) and gfp f (&#957;, the '
            'non-well-founded closure);',
            '  the frame-change is the order-duality f &#8614; f.dual on &#945;<sup>op</sup> &#8212; '
            'the abstract analogue of z &#8614; 1/z, op, and complementation.',
            'The schema states that the frame-change swaps the two charts, and that they coincide '
            'exactly at the diagonal fixed point.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition: lfp_dual_eq_gfp / gfp_dual_eq_lfp',
        [
            'lfp (f.dual) = gfp f   and   gfp (f.dual) = lfp f.',
            'The frame-change (order-duality) carries the &#956;-closure to the &#957;-closure and '
            'back: the two charts are swapped, not merged. In Lean both are definitional (rfl) '
            '&#8212; the swap is built into how gfp is defined (sSup of post-fixed points).',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: fork_is_frameflip &#8212; the schema spine',
        [
            'Over any complete lattice, bundling both faces: (i) lfp (f.dual) = gfp f and '
            '(ii) gfp (f.dual) = lfp f (the frame-change swaps the charts), together with '
            '(iii) lfp f = gfp f &#8596; &#8707;! x, f x = x (the fork collapses at the diagonal '
            'fixed point &#8212; fork_collapse_iff).',
            'This is the domain-independent form of the POLE BEHAVIOUR: the two charts are swapped by the '
            'frame-change, and the bottom is where they meet. Note what (iii) says &#8212; least = greatest '
            'exactly when the fixed point is unique. That is the min&#8801;max coincidence in its general '
            'form, of which epsilon0_min_eq_max, selfApp_bot_is_both_extremal and the categorical seam '
            '(initial &#8743; terminal) are instances. It does NOT assert that the snap is a change of frame; '
            'that identification remains this layer&#8217;s open conjecture.',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The frame-flip schema is choice-free. fork_is_frameflip and both duality lemmas depend only '
        'on [propext, Quot.sound] &#8212; propositional extensionality and quotient soundness, the '
        'benign kernel axioms used throughout Mathlib. None depends on the Axiom of Choice. As in '
        'ZP-P, the conceptual skeleton needs no choice; choice enters only in the analytic '
        'realisations (Section II). See AxiomProfile.lean.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── Section II: The Instance Catalogue (Tier 2) ───────────────────────────────
    print('[build_zpq] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Instance Catalogue (Tier 2)', S['h1']),
        hr(),
    ]

    E.append(body(
        'The same frame-flip appears across the framework, each domain realising it with its own '
        'concrete involution. ZP-Q does not re-prove each instance &#8212; each is a theorem in its '
        'home layer &#8212; it records the catalogue and pins the two instances with a full '
        'frame-flip (valuation, category) to their Lean witnesses. The two poles of each row are the '
        'two charts; the frame-change is the involution that swaps them.'))

    E.append(data_table(
        headers=['Domain', 'The two poles (charts)', 'Frame-change &#8212; witness'],
        rows_data=[
            ['Valuation',
             '0 = &#8869;  &#8596;  &#8734;',
             'z &#8614; 1/z (rInv) &#8212; snap_is_frameflip'],
            ['Category',
             'initial (&#956;)  &#8596;  terminal (&#957;)',
             'op-duality &#8212; catseam_is_frameflip'],
            ['Set theory',
             'Foundation (&#956;)  &#8596;  AFA (&#957;)',
             'the fork &#8212; fork_collapse_iff'],
            ['Computability',
             'code  &#8596;  self-application',
             'the diagonal &#8212; AbstractSelfApp.unique_fp'],
            ['State / Hilbert',
             'X  &#8596;  X &#8862; X',
             'the biproduct diagonal &#8212; biprod_diagonal_only_zero'],
            ['Information',
             'measure 0  &#8596;  surprisal &#8734;',
             '&#8722;log &#8212; info_bottom_diverges'],
            ['Reals',
             '&#8212; (no discrete floor)',
             'inversion breaks at 0 &#8212; NO-GO (ZP-F)'],
        ],
        col_widths=[TW * 0.20, TW * 0.34, TW * 0.46],
    ))
    E.append(sp(6))

    E.append(body(
        'The valuation instance is the originating figure of the framework: the p-adic Riemann '
        'sphere. Under the tower-rank encoding (P8.lean) the &#969;-tower climbing to '
        '&#949;<sub>0</sub> has stage-encodings that converge to the 2-adic floor 0 = &#8869; &#8212; so in '
        'that chart the ascent to &#949;<sub>0</sub> resolves onto a new bottom (the encodings converge '
        'to &#8869;; &#949;<sub>0</sub> &#8800; &#8869;). Viewed through the inversion rInv (the one-point '
        'compactification of &#8474;<sub>2</sub>, RiemannSphere.lean), the same encodings diverge to '
        '&#8734;. rInv is the homeomorphism that swaps the poles 0 &#8596; &#8734;.'))

    E.append(sp(6))
    _fig = sphere_figure()
    _fig.hAlign = 'CENTER'
    E.append(_fig)
    E.append(ccaption(
        'Figure 1. The p-adic Riemann sphere. The poles 0 = &#8869; (the floor) and &#8734; (the '
        'ceiling) are antipodal; the equator &#8214;x&#8214; = 1 is the seam. Inside '
        '&#8484;<sub>p</sub> (the lower hemisphere) the &#969;-tower falls one way to 0; the '
        'inversion z &#8594; 1/z (rInv) swaps the poles 0 &#8596; &#8734; &#8212; continuous on the '
        'sphere, torn at 0 in the field.'))
    E.append(sp(8))

    E.append(result_box(
        'Theorem: snap_is_frameflip (SnapFrameChange.lean)',
        [
            'The one &#969;-tower&#8217;s encodings have two limits, one per chart: they fall to the '
            'floor 0 = &#8869; in the encoding chart (converging to a new bottom, '
            'cnf_encode_tower_tendsto_zero), and rise to the antipode &#8734; in the rInv chart '
            '(snap_frameflip_tower_tendsto_infty), with rInv the frame-change swapping the poles '
            '(rInv_swaps: 0 &#8596; &#8734;). The encodings converge to &#8869;; &#949;<sub>0</sub> &#8800; &#8869;.',
            'The descent to &#8869; and the ascent to &#8734; are the same tower-encodings under the '
            'frame-change &#8212; the valuation-frame realisation of the BOTTOM&#8217;s two chart-readings. '
            'Note the scope: no snap transition appears in this statement (no c&#8320; &#8594; c&#8321;, no '
            '&#8869; &#8918; a). The declaration handle snap_is_frameflip is retained for cross-reference '
            'but overclaims; the statement is the authority.',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; choice-carrying '
            '(Classical.choice from the Riemann-sphere continuity machinery). ✓',
        ]
    ))
    E.append(sp(4))

    E.append(remark_box(
        'Remark: continuity is frame-relative &#8212; the bridge and the fence',
        [
            'RiemannSphere.lean proves the content that makes the sphere the right figure. In the '
            'affine field &#8474;<sub>2</sub> the inversion z &#8614; 1/z is discontinuous at 0 '
            '(1/0 is undefined): the map tears. Adjoining &#8734; and sending 0 &#8614; &#8734; '
            'repairs the tear &#8212; on the sphere the inversion is a continuous homeomorphism '
            '(rInvHomeo). So the same point 0 is a discontinuity (a fence) from the field frame and '
            'a continuous join to &#8734; (a bridge) from the sphere frame. Continuity itself is '
            'frame-relative; one chart tears where the other heals. The tear at 0 is the '
            'apophatic bottom &#8212; the place the map fails, never positively drawn.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: catseam_is_frameflip (SeamFrameChange.lean)',
        [
            'The zero-object seam Z = fD_functor.obj 0 is the &#956;-bottom (initial) in one chart '
            'and the &#957;-top (terminal) in the other; the op-duality frame-change swaps the two '
            '&#8212; carrying Z&#8217;s initial-ness to a terminal-ness of Z<sup>op</sup> and its '
            'terminal-ness to an initial-ness of Z<sup>op</sup> (terminalOpOfInitial / '
            'initialOpOfTerminal). The seam is the op-self-dual zero object.',
            'Off the zero object the coincidence fails (SeamLimColim.lean: '
            'generic_object_empty_lim_ne_colim) &#8212; as with 0 on the sphere, the frame-change '
            'fixes only the bottom.',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; choice-carrying '
            '(inherited from the ModuleCat / category-theory library). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'The remaining instances are referenced, not re-proved here. Set theory: the Quine atom '
        '&#8869; = {&#8869;} is the collapse of the Foundation / AFA fork (ZP-J, ZP-P; '
        'fork_collapse_iff, selfMem_eq_singleton_bot). Computability: the bottom is the unique fixed '
        'point of self-application (ZP-K; AbstractSelfApp.unique_fp). State / Hilbert: &#8869; is the '
        'unique finite-dimensional fixed point of the biproduct-diagonal X &#8614; X &#8862; X (ZP-H; '
        'biprod_diagonal_only_zero). Information: measure runs to 0 at the floor exactly as surprisal '
        'runs to &#8734; (ZP-C; info_bottom_diverges, addVal_bot), the two joined by &#8722;log.'))

    E.append(remark_box(
        'Remark: the reals are the counterexample (the discriminator)',
        [
            'The real numbers are where the frame-change fails, and that is exactly what makes this '
            'a diagnostic rather than a pattern read into every domain. &#8477; has no discrete '
            'floor to fall to (density), and its inversion is discontinuous at 0 with no repair. '
            'Both features of the bottom &#8212; the infinitude at the zero and the one-way arrow '
            'that reverses under inversion &#8212; are absent, and the snap fails (ZP-F). The '
            'frame-flip is present precisely where the snap lives and absent precisely where it '
            'does not.',
        ]
    ))
    E.append(sp(6))

    # ── Section III: The Universal Form and Its Walls (Tier 3) ────────────────────
    print('[build_zpq] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Universal Form and Its Walls (Tier 3)', S['h1']),
        hr(),
    ]

    E.append(body(
        'Is there a single universal frame-flip &#8212; one theorem all the instances are cases of? '
        'The question resolves into two halves, and both are proved. At the order-theoretic level the '
        'universal holds: fork_is_frameflip (Section I) is a single choice-free theorem over any '
        'complete lattice that every instance realises. At the categorical level the universal is a '
        'wall. The fences below are not hedging; they mark a genuine boundary, and per-instance '
        'frame-flips remain full theorems on either side of it.'))

    E.append(def_box(
        'The wall: the categorical universal is category-relative (Lawvere.lean)',
        [
            'Lawvere&#8217;s fixed-point theorem derives a fixed point from a point-surjection '
            '&#945; &#8594; (&#945; &#8594; &#946;). ZP asks whether each bottom is such a '
            'Lawvere-produced fixed point. The answer is category-relative, and it is proved. In '
            '<b>Set</b> (all endofunctions) no nontrivial total type carries a Lawvere witness '
            '&#8212; Cantor forbids it (nontrivial_lattice_no_witness, q2_no_witness) &#8212; so '
            'the lattice and 2-adic bottoms share the diagonal <i>shape</i> but are provably NOT '
            'literal Lawvere instances. Only in the <b>effective</b> category is there a genuine '
            'one, where the fixed-point-free diagonal is not computable '
            '(computability_face_fixedPoint, Kleene&#8217;s recursion theorem). So the keystone '
            'unifies a shape, not a single mechanism.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Hard fence (permanent): cross-domain identity is a type boundary',
        [
            'The claim that the contact points of all the instances &#8212; the p-adic 0, the Quine '
            'atom, the Kleene quine, the categorical zero object &#8212; are numerically one object '
            'is not a theorem and cannot become one. Identity requires a shared type; these are '
            'terms of different types in different categories, so &#8220;x = y&#8221; across them is '
            'not false but not well-formed. This is proved at the measure level too: '
            'BottomMeasure.lean shows &#8220;+&#8734; at every floor&#8221; is a per-domain bundle in '
            'incompatible types, not one invariant. The interconnect is therefore '
            'point-of-view-specific. What is claimed formally is only that each domain forks, and '
            'flips, at its own contact point.',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The fence is the bridge. The frame-change that joins the two poles (the bridge) and the '
        'diagonal that forbids collapsing them into one object (the fence) are the <i>same</i> '
        'diagonal. The bridge only exists between poles that stay two: were they merged there would '
        'be nothing to cross. So the boundary is not the price of the connection &#8212; it is its '
        'condition. The keystone is bounded by the exact mechanism it is built from: the diagonal '
        'argument makes the fixed point and, in the same gesture, forbids its universal '
        'identification. Per-instance frame-flips are theorems and are not hedged; the fences scope '
        'only the universal cross-category claim.',
        bg=BLUE_LITE, border=BLUE
    ))
    E.append(sp(6))

    # ── Theorem Summary ───────────────────────────────────────────────────────────
    print('[build_zpq] Building theorem table...')
    E += [
        hr(),
        Paragraph('Theorem Summary', S['h1']),
        hr(),
    ]

    E.append(data_table(
        headers=['Result', 'Lean source (full path)', 'Axioms'],
        rows_data=[
            ['lfp_dual_eq_gfp', 'ZeroParadox/Settheory/ForkFrameChange.lean', 'choice-free'],
            ['gfp_dual_eq_lfp', 'ZeroParadox/Settheory/ForkFrameChange.lean', 'choice-free'],
            ['fork_is_frameflip', 'ZeroParadox/Settheory/ForkFrameChange.lean', 'choice-free'],
            ['fork_collapse_iff', 'ZeroParadox/Settheory/FixedPointFork.lean', 'choice-free'],
            ['snap_is_frameflip', 'ZeroParadox/Multihomed/SnapFrameChange.lean', 'Classical.choice'],
            ['rInv_swaps', 'ZeroParadox/Valuation/RiemannSphere.lean', 'Classical.choice'],
            ['catseam_is_frameflip', 'ZeroParadox/Category/SeamFrameChange.lean', 'Classical.choice'],
            ['nontrivial_lattice_no_witness', 'ZeroParadox/Category/Lawvere.lean', 'Classical.choice'],
            ['computability_face_fixedPoint', 'ZeroParadox/Category/Lawvere.lean', 'Classical.choice'],
        ],
        col_widths=[TW * 0.34, TW * 0.46, TW * 0.20],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Frame-flip schema (ForkFrameChange.lean): [propext, Quot.sound] &#8212; choice-free. The '
            'universal needs no Axiom of Choice; the duality-swap is definitional.',
            'Valuation instance (SnapFrameChange.lean / RiemannSphere.lean): [propext, '
            'Classical.choice, Quot.sound] &#8212; Classical.choice inherited from the p-adic / '
            'one-point-compactification analysis.',
            'Categorical instance (SeamFrameChange.lean): [propext, Classical.choice, Quot.sound] '
            '&#8212; inherited from the ModuleCat / category-theory library.',
            'The wall (Lawvere.lean): the concrete Cantor no-witness results '
            '(nontrivial_lattice_no_witness, q2_no_witness) and computability_face_fixedPoint '
            '(Kleene\'s recursion theorem) carry Classical.choice; the abstract witness machinery '
            '(fixedPoint_of_witness, no_witness_of_fixedPointFree) is axiom-free.',
            'Core choice-free, realisation choice-carrying &#8212; the framework&#8217;s standing '
            'pattern. Zero sorry. Verified: lake build, July 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-Q | The Frame-Change | fork_is_frameflip (choice-free order-theoretic '
            'universal) | the Riemann-sphere valuation instance (snap_is_frameflip) and the '
            'op-duality categorical instance (catseam_is_frameflip) | the categorical universal is a '
            'proven wall (Cantor; Lawvere.lean) | the fence is the bridge | the bottom is never '
            'positively represented.</i>',
            S['endnote']),
    ]

    print('[build_zpq] Building document...')
    doc.build(E)
    print(f'[build_zpq] Done: {out_path}')


if __name__ == '__main__':
    build()
