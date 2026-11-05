"""
Zero Paradox — ZP-Q: The Frame-Change PDF Builder
Version 1.22 | November 2026
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.22'
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
        Paragraph('The bottom read as both 0 and &#8734;, and what that does not settle', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Synthesis layer, the sequel to ZP-P. The abstract frame-flip schema is proved '
            'sorry-free and choice-free in Lean 4 (ForkFrameChange.lean); the per-domain realizations '
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
        '<b>The frame-change is that pole exchange &#8212; &#8869; being read as both 0 and &#8734;. Whether '
        'the snap is an instance of it is the layer&#8217;s open conjecture.</b> The snap, T-SNAP&#8217;s '
        'shape, is a join step off &#8869; of the state semilattice to a different state (t_snap_given); '
        'that the step is a cover, &#8869; &#8918; a (HasFirstStep), is AX-B1&#8217;s first-step form, a '
        'modelling commitment and a further hypothesis (t_snap_given_cover) that MachinePhase supplies '
        'and &#8474;&#8805;0 does not; the frame-change is an involution and is proved. Merging the two is what makes it look paradoxical that a frame-change '
        'reverses while the snap does not, and that reversibility mismatch is exactly what an '
        'identification would have to resolve. ZP-Q holds it open rather than settling it either way. '
        'Read from one frame the frame-change is a <i>bridge</i> (it joins the poles continuously); '
        'read from the other it is a <i>fence</i> (a boundary the map cannot cross). ZP-Q records the '
        'abstract frame-flip schema, its per-domain realizations, and the universal form together with '
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
            'ZP-Q characterises the bottom apophatically (by what it is not, never by a positive '
            'construction), and the register is itself frame-relative. '
            'Seen from outside &#8212; from any frame that looks at &#8869; &#8212; there is no '
            'interior: nothing sits behind the description waiting to be opened. The boundary is the '
            'whole of it. &#8869; is the seam the frame-change joins, or the tear it leaves, a '
            'boundary of measure zero, all edge and no inside (read flat, this is the Quine atom (CC-2) '
            'from without, the occupant of the role "steps to itself and to nothing else" '
            'under a self-application map supplied by AbstractSelfApp (selfApp_quine_role_iff) &#8212; a single node, not a region &#8212; and the '
            'tear on the sphere &#8212; a discontinuity, not a region).',
            'Seen from &#8869;&#8217;s own frame &#8212; inside the self-reference &#8212; the same '
            'point is the opposite: infinite depth. v<sub>2</sub>(0) = &#8734;; the endless regress '
            'Q &#8712; Q &#8712; Q &#8230; of the AFA set Q = {Q} that plays the role; unbounded surprisal. No-interior and '
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
            'exactly when the fixed point is unique &#8212; and note the hypotheses: it needs a COMPLETE LATTICE and a '
            'MONOTONE map. NONE of the framework&#8217;s min&#8801;max facts satisfies those, so none is an instance of it. '
            'epsilon0_min_eq_max is over the ordinals, where the omega-power map has a proper class of fixed points, so nothing '
            'collapses; selfApp_bot_is_both_extremal is over a bare join-semilattice whose self-application is not a monotone map; '
            'the categorical seam lives in a category, not a lattice. What they share is a SHAPE &#8212; one object carrying both '
            'extremal characterisations at once &#8212; and a shared shape across distinct structures is a type boundary, never a '
            'common theorem. State the shape, not an instance-of relation. It does NOT assert that the snap is a change of frame; '
            'that identification remains this layer&#8217;s open conjecture.',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The frame-flip schema is choice-free. fork_is_frameflip and both duality lemmas depend only '
        'on [propext, Quot.sound] &#8212; propositional extensionality and quotient soundness, two '
        'of Lean&#8217;s standard axioms, used throughout Mathlib. None depends on the Axiom of Choice. As in '
        'ZP-P, the conceptual skeleton needs no choice; choice enters mostly in the analytic '
        'realisations (ZeroParadox/AxiomProfile.lean &#167; III) &#8212; not only there, since the '
        'framework also carries bare classicals of its own; ZeroParadox/Category/ChoiceCannotBe.lean '
        '&#167; IV collects cases among them whose principles reduce to a taboo, with those '
        'reductions.',
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
             '0  &#8596;  &#8734; (no first step above 0)',
             'x &#8614; 1/x on the one-point compactification &#8212; onePointInv_swaps_real; '
             'holds, and is not a discriminator (the remark below)'],
        ],
        col_widths=[TW * 0.20, TW * 0.34, TW * 0.46],
    ))
    E.append(sp(6))

    E.append(body(
        'The valuation realization is the originating figure of the framework: the p-adic Riemann '
        'sphere. Under the tower-rank encoding (P8.lean) the &#969;-tower climbing to '
        '&#949;<sub>0</sub> has stage-encodings that converge to &#8484;<sub>[2]</sub>\'s 0 '
        '(cnf_encode_tower_tendsto_zero), least under the 2-adic norm and greatest under the 2-adic '
        'valuation &#8212; so in that chart, read by the norm, the ascent toward &#949;<sub>0</sub> '
        'resolves back onto the floor (the encodings converge to 0; &#949;<sub>0</sub> has no encoding, '
        'and &#949;<sub>0</sub> &#8800; &#8869; of Ordinal, epsilon0_ne_bot). Viewed through the inversion rInv (the one-point '
        'compactification of &#8474;<sub>2</sub>, RiemannSphere.lean), the same encodings diverge to '
        '&#8734;. rInv is the homeomorphism that swaps the poles 0 &#8596; &#8734;.'))

    E.append(sp(6))
    _fig = sphere_figure()
    _fig.hAlign = 'CENTER'
    E.append(_fig)
    E.append(ccaption(
        'Figure 1. The p-adic Riemann sphere. The poles 0 = &#8869; (the floor, least under the '
        '2-adic norm) and &#8734; (the '
        'ceiling) are antipodal; the equator &#8214;x&#8214; = 1 is the seam. Inside '
        '&#8484;<sub>p</sub> (the lower hemisphere) the &#969;-tower falls one way to 0; the '
        'inversion z &#8594; 1/z (rInv) swaps the poles 0 &#8596; &#8734; &#8212; continuous on the '
        'sphere, torn at 0 in the field.'))
    E.append(sp(8))

    E.append(result_box(
        'Theorem: snap_is_frameflip (SnapFrameChange.lean)',
        [
            'The one &#969;-tower&#8217;s encodings have two limits, one per chart: they fall to the '
            'floor 0 of &#8484;<sub>[2]</sub> in the encoding chart, read by the 2-adic norm '
            '(cnf_encode_tower_tendsto_zero; cnf_encode takes the values 2<sup>k</sup> and never starts '
            'at 0, so the return to the SAME 0 the arc started from is a fact about the other encoding, '
            'cnfToZp2: tower_image_loops_to_seed, snap_arc_z2_loop), and rise to the antipode &#8734; in the rInv chart '
            '(snap_frameflip_tower_tendsto_infty), with rInv the frame-change swapping the poles '
            '(rInv_swaps: 0 &#8596; &#8734;). The encodings converge to 0; &#949;<sub>0</sub> &#8800; '
            '&#8869; of Ordinal (epsilon0_ne_bot).',
            'The descent to 0 and the ascent to &#8734; are the same tower-encodings under the '
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
        'The remaining realizations are referenced, not re-proved here. Set theory: the Quine atom '
        '(CC-2) is the collapse of the Foundation / AFA fork (ZP-J, ZP-P; fork_collapse_iff, '
        'selfMem_eq_singleton_bot), stated as a role, a point that steps to itself and to nothing '
        'else, whose occupancy is settled chart by chart, with no equation across charts: occupied by &#8869; in the lattice chart, '
        'under a self-application map supplied by AbstractSelfApp (selfApp_quine_role_iff) and in the '
        'QuineAtomHost an AFAStructure on L builds (quineAtomHost_quine_role_iff with '
        'afaStructure_isQuineAtomHost), by no set in Mathlib\'s ZFSet '
        '(zfset_quine_role_unoccupied). Computability: ZP-K\'s class KleeneStructure requires a code '
        'meeting a periodicity condition (botCode_is_quine) and equates it with nothing. The reading '
        'that this code is the bottom\'s computational witness splits: its identity half is retired '
        '(no single code occupies the Quine-atom role under the eval step, '
        'evalStepMotion_not_selfOnlyAt, while a class of codes up to equal eval does, for a '
        'computable map respecting equal eval, codes_vs_classes), and its running half, that the bottom executes, is the occurrence '
        'commitment. That the bottom is the unique fixed '
        'point of self-application is the AbstractSelfApp class field unique_fp (ZP-J), a requirement '
        'rather than a theorem. State / Hilbert: &#8869; is the '
        'unique finite-dimensional fixed point of the biproduct-diagonal X &#8614; X &#8862; X (ZP-H; '
        'biprod_diagonal_only_zero). Information: measure runs to 0 at the floor exactly as surprisal '
        'runs to &#8734; (ZP-C; info_bottom_diverges, addVal_bot), the two joined by &#8722;log.'))

    E.append(remark_box(
        'Remark: the reals beside &#8474;<sub>2</sub> (what separates them)',
        [
            'Inversion does not separate &#8477; from &#8474;<sub>2</sub>. Inside each field it is '
            'discontinuous at 0. On the one-point compactification of any proper normed field it is '
            'continuous and swaps 0 and &#8734;, a standard fact for the Riemann sphere (Forster, Lectures '
            'on Riemann Surfaces, GTM 81, &#167;&#167; 1&#8211;2, as cited by TauCeti; not retrieved), which '
            'TauCeti formalizes for proper nontrivially normed fields: OnePoint.invChart (a chart) and '
            'OnePoint.instContinuousConstSMul (the global action). It is proved '
            'here with Mathlib alone (continuous_onePointInv, onePointInv_swaps, '
            'ZeroParadox/Valuation/RiemannSphere.lean), so for &#8477; as well as &#8474;<sub>2</sub> '
            '(continuous_onePointInv_real, onePointInv_swaps_real; for &#8474;<sub>2</sub>, the sphere '
            'above, continuous_rInv and rInv_swaps). What '
            'separates the two is topology: &#8477; is connected (place_topological_signature), so not '
            'totally disconnected (real_no_snap), while &#8474;<sub>2</sub> is totally '
            'disconnected (padic_snaps). Neither has a first step above 0, AX-B1&#8217;s form: in '
            '&#8477; because no linearly ordered field has a least positive element (ZP-F; '
            'f_snap_impossible, which, despite its name, states exactly that), and in '
            '&#8474;<sub>2</sub>, which carries no order of its own, under the norm preorder '
            '(ZeroParadox/BottomCannotBe.lean &#167; ROLE). T-SNAP&#8217;s shape does not need a '
            'first step: t_snap_given holds at a step taken in a densely ordered join-semilattice '
            '(&#8474;&#8805;0 under max, ZeroParadox/Order/Snap.lean).',
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
        'Is there a single universal frame-flip &#8212; one theorem all the faces are cases of? '
        'No, and the question resolves into two walls of different kinds. At the order-theoretic level a '
        'single choice-free theorem does exist over any complete lattice &#8212; fork_is_frameflip '
        '(Section I) &#8212; but as Section I records, none of the framework&#8217;s min&#8801;max faces '
        'satisfies its hypotheses of a complete lattice and a monotone map, so none of them is an instance '
        'of it. It is universal over its own domain, not over the faces. At the categorical level the '
        'universal is a proven wall (below). What the faces share is a SHAPE realized concretely in each '
        'domain. The instance table&#8217;s last row, the reals, carries the same pole exchange on its '
        'one-point compactification (onePointInv_swaps_real) and has no first step above 0 '
        '(f_snap_impossible), so the frame-flip does not separate &#8477; from &#8474;<sub>2</sub>; '
        'total disconnectedness does (padic_snaps, real_no_snap). The two walls are not hedging: they mark '
        'where the universal form stops, and each per-domain frame-flip remains a full theorem in its own domain.'))

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
            'one, where the fixed-point-free <i>diagonal construction</i> is not admissible '
            '&#8212; which is not the claim that no fixed-point-free computable endomap exists, since '
            'fun c =&gt; Code.pair c c is one (code_pair_diag_fixedPointFree); removing the obstruction does not by itself supply the '
            'witness, and the fixed point is cited rather than derived '
            '(computability_face_fixedPoint). So the keystone '
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
            ['onePointInv_swaps', 'ZeroParadox/Valuation/RiemannSphere.lean', 'Classical.choice'],
            ['onePointInv_swaps_real', 'ZeroParadox/Valuation/RiemannSphere.lean', 'Classical.choice'],
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
            'pattern.',
            'The footprints listed here are copies; the live record is the #print axioms output of '
            'each named .lean file.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-Q | The Frame-Change | fork_is_frameflip (choice-free order-theoretic '
            'universal) | the Riemann-sphere valuation face (snap_is_frameflip) and the '
            'op-duality categorical face (catseam_is_frameflip), neither an instance of it | the '
            'categorical universal is a '
            'proven wall (Cantor; Lawvere.lean) | the fence is the bridge | the bottom is never '
            'positively represented.</i>',
            S['endnote']),
    ]

    print('[build_zpq] Building document...')
    doc.build(E)
    print(f'[build_zpq] Done: {out_path}')


if __name__ == '__main__':
    build()
