"""
Zero Paradox — ZP-I: Inside Zero PDF Builder
Version 1.28 | October 2026
"""

import os
from zp_utils import *

VERSION = '1.28'
FIRST_RELEASED = 'April 2026'

# ZP-I uses justified body text; override the left-aligned zp_utils defaults
S['body']    = ParagraphStyle('body',    fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6, alignment=4)
S['bodyI']   = ParagraphStyle('bodyI',   fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6, alignment=4)
S['li']      = ParagraphStyle('li',      fontName='DVS',   fontSize=10, leading=14,
                               leftIndent=18, spaceAfter=3, alignment=4)
S['derived'] = ParagraphStyle('derived', fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=GREEN_DARK, alignment=4)
S['key']     = ParagraphStyle('key',     fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=4, textColor=INDIGO, alignment=4)


def key(text):
    return Paragraph(fix(text), S['key'])


def theorem_box(title, rows, color=SLATE):
    """Colored box for theorems/lemmas — default SLATE, can be INDIGO."""
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  color),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, color),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, color),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t


def key_result_box(rows):
    data = [[Paragraph(fix('Key Result'), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['key'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  INDIGO),
        ('BACKGROUND',    (0,1), (-1,-1), INDIGO_LITE),
        ('BOX',           (0,0), (-1,-1), 1.0, INDIGO),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, INDIGO),
        ('TOPPADDING',    (0,0), (-1,-1), 6),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
        ('RIGHTPADDING',  (0,0), (-1,-1), 10),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-I_Inside_Zero.pdf')
    print(f'[build_zpi] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-I: Inside Zero', 'ZP-I: Inside Zero',
                   'Version ' + VERSION)
    E   = []

    print('[build_zpi] Building title block...')
    # ── TITLE BLOCK ───────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-I: Inside Zero', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document establishes Theorem T-IZ (Inside Zero): every 2-adic depth chain '
        'S<sub>0</sub>, S<sub>1</sub>, ... in Q<sub>2</sub>, nowhere zero, whose valuation equals a depth '
        'index in &#8469; that climbs at every step (IsDepthChain, IsStrictStateSequence) is a Cauchy '
        'sequence that converges, in the 2-adic metric, to 0. The ascending chain of a ZP-A semilattice '
        'is a separate carrier. No '
        'new axioms are required for what it PROVES, which is that convergence, together with the '
        'separate fact that anything filling the bottom role IS the bottom of its own semilattice. '
        'Reading the 2-adic limit as the thing filling that role is a modelling commitment, not a '
        'theorem: the two live in different types, and Q<sub>2</sub>&#8217;s field structure supplies no join and the corpus defines none on Q<sub>2</sub>, so the role '
        'condition is not statable of the limit at all — they are distinct MEMBERS of the bottom '
        'family, not one object, and that identity is retired as ill-typed (MC-1). '
        'Reading the bottom so reached as a NEW one '
        'rather than the one already there is a further commitment (C-DA2 in ZP-E), and in the 2-adic '
        'chart the arc returns to the SAME 0 (snap_arc_z2_loop). T-IZ extends T-SNAP: where T-SNAP fixes the shape of the first transition '
        '&#8869; &#8594; &#949;<sub>0</sub>, and not that it is taken, T-IZ establishes, for a depth index that climbs at every step, '
        'that the 2-adic chain the IsDepthChain modelling commitment links to it converges to 0, as a Cauchy sequence result.'))
    E.append(body(
        'The key insight: the no-top property is not an obstacle to T-IZ. In a carrier that has it '
        '(HasNoTop is a hypothesis on the carrier; MachinePhase and OntologicalStates have a top), it is '
        'what makes the ascent AVAILABLE — there is always a strictly greater element, so no chain halts '
        'for want of anywhere to go. (It does NOT follow that the limit lies outside L; whether a limit escapes '
        'its carrier is a property of the particular lattice — the ordinals under max have no top, and '
        'the chain n &#8614; n has least upper bound &#969; inside them.) What drives the 2-adic '
        'valuation v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734; is that the chain actually takes those steps '
        '(IsStrictStateSequence, the hypothesis h_strict_from_r1_t3 binds); no-top alone does not, and the '
        'NO-GO gauge in &#167;Ib exhibits a no-top lattice holding a chain that never moves. '
        'Unbounded ascent is exactly the Cauchy convergence condition '
        '&#8214;S<sub>n</sub>&#8214;<sub>2</sub> &#8594; 0. The chain approaches the 2-adic depth of zero by going '
        'deeper into the p-adic structure — not by reversing direction. That DA-1 and T-SNAP fire again '
        'at the limit, so that the cycle begins again, is a reading; its premises are stated in &#167; V.III. '
        't_iz_complete takes a KleeneStructure on the limit&#8217;s successor semilattice L&#8242; as a hypothesis and '
        'links L&#8242; to nothing; its DA-1 conjunct, that L&#8242;&#8217;s &#8869; is its Quine atom, is the Lean '
        'counterpart of DA-1&#8217;s Path 1, which does not derive DA-1&#8217;s precondition (ZP-E &#167; IV).',
        style='bodyI'))
    E.append(hr())

    print('[build_zpi] Building Section I...')
    # ── SECTION I: THE ENGINE ─────────────────────────────────────────────────
    E += [
        Paragraph('Section I: Room to Ascend — No Top Element and Ordinal Unboundedness', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The No-Top Property: What It Supplies', S['h2']))
    E.append(body(
        'The no-top property (Lean: HasNoTop, ZeroParadox/Order/Lattice.lean) says the join-semilattice '
        '(L, &#8744;, &#8869;) has no top element: there is no T &#8712; L with x &#8804; T for all x. '
        '⚠ This is NOT ZP-A&#8217;s R1, which is the NO-SUBTRACTION restriction (&#167;I of the ZP-B '
        'section below); one label over two propositions is a citation nothing can check. What no-top '
        'supplies is ROOM: a chain never halts for want of a strictly greater element. The ascent '
        'itself is IsStrictStateSequence — see the NO-GO gauge in &#167;Ib. Reading the limit as '
        'occupying the bottom role is a commitment, and calling the occupant a successor null is '
        'C-DA2, a further one.'))
    E.append(body(
        'The reasoning is direct. An ascending chain (S<sub>n</sub>)<sub>n&lt;&#969;</sub> in L '
        'is a sequence satisfying S<sub>n</sub> &#8804; S<sub>n+1</sub> for all n (ZP-A T3 — monotonicity). '
        'Where L has no top element (HasNoTop is a hypothesis on the carrier, not a law of every '
        'ZP-A semilattice: the two-state carriers MachinePhase and OntologicalStates have a top, '
        'by the examples in ZeroParadox/Order/Snap.lean and ZeroParadox/Settheory/OntBridge.lean), '
        'for every S<sub>N</sub> there EXISTS an S with '
        'S<sub>N</sub> &lt; S — so no chain is ever forced to stabilise for want of somewhere to go. '
        '⚠ That is availability, not occurrence: a CONSTANT chain is still a legitimate state '
        'sequence in a no-top lattice (NO-GO gauge, &#167;Ib). That this chain is strictly ascending '
        'and unbounded is the separate hypothesis IsStrictStateSequence, and that is the one T-IZ '
        'consumes.'))
    E.append(body(
        'In the 2-adic model (ZP-B), the IsDepthChain modelling commitment links two carriers: a 2-adic '
        'chain S<sub>n</sub> in Q<sub>2</sub>, and a depth index in &#8469; (a ZP-A semilattice under max) that '
        'its valuation v<sub>2</sub>(S<sub>n</sub>) equals. Strict ascent of that depth index '
        '(IsStrictStateSequence) is increasing 2-adic valuation depth. Because the index is unbounded, v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734;. '
        'This follows from the strict-ascent hypothesis, not from the absence of a top element: no-top '
        'leaves room for the ascent, and IsStrictStateSequence is that the chain takes it.'))

    E.append(Paragraph('II. Ordinal Index Replaces Clock Time', S['h2']))
    E.append(body(
        'The state sequence is indexed by ordinals: (S<sub>&#945;</sub>)<sub>&#945;&lt;&#969;</sub>. '
        'The parameter &#969; is not a clock time and not a top bound. It is the ordinal index '
        'of the transition — the label for when the chain has completed &#969; state changes. '
        'The chain in L is genuinely unbounded; the ordinal &#969; is not a member of the sequence '
        'and not a ceiling on it.'))
    E.append(body(
        'This replaces the informal "time" language that sometimes accompanies descriptions of '
        'the Binary Snap. In the Zero Paradox, "time" is the index of state changes. What fixes '
        'the direction of that index is monotonicity (ZP-A T3) and irreversibility (ZP-B C3). '
        'Neither is a clock. '
        'What the chain reaches at the limit ordinal &#969;, after &#969; state changes, is Q<sub>2</sub>&#8217;s 0, '
        'and not at any clock time. Reading that 0 as filling the bottom role is a commitment, and reading it '
        'as a NEW bottom rather than the same one is a further commitment (C-DA2).'))
    E.append(body(
        'Remark R-I.1: &#969; is the first infinite ordinal — the smallest ordinal greater than '
        'every natural number. An ascending chain indexed by &#969; is a countable sequence with '
        'no last element in L. The no-top property guarantees only that no finite stage is a CEILING; '
        'that a given chain reaches through all of them is the strict-ascent hypothesis. The '
        'transition at &#969; is not a step within L. ⚠ Whether its limit lies OUTSIDE L is a '
        'property of the particular lattice and not a consequence of no-top.'))

    E.append(key_result_box([
        'Strict ascent (IsStrictStateSequence) drives v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734;; '
        'the no-top property supplies the room for it, and is not a hypothesis OF THAT THEOREM (it is a '
        'per-carrier assumption in its own right — nat_has_no_top is a theorem, and '
        'zpa_bot_not_greatest binds it explicitly). '
        'Strict valuation growth (v<sub>2</sub>(S(n)) &#8805; n) is Lean-derived from IsDepthChain and '
        'IsStrictStateSequence — Lean: h_strict_from_r1_t3 (&#167;Ib). R-IZ-A closed.',
        '&#8214;S<sub>n</sub>&#8214;<sub>2</sub> = 2<sup>-v<sub>2</sub>(S<sub>n</sub>)</sup> &#8594; 0 '
        '(Cauchy condition).',
        'The no-top property removes the ceiling; IsStrictStateSequence is that the chain climbs. '
        'Of those two only IsStrictStateSequence appears in h_strict_from_r1_t3&#8217;s binders — '
        'alongside IsDepthChain, which is not a lattice condition but the bridge to the 2-adic valuation.',
    ]))
    E.append(sp(6))

    print('[build_zpi] Building Section II...')
    # ── SECTION II: THE TWO PATHS ─────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Section II: The Topological Path and the Refuted Informational Bridge', S['h1']),
        hr(),
    ]

    E.append(body(
        'Two paths are set out here. The topological path, through Q<sub>2</sub> and the 2-adic '
        'norm, is proved (&#167; A). The informational path, through ZP-C L-INF and the Kolmogorov '
        'complexity threshold P<sub>0</sub>, rests on a valuation-complexity bridge that is REFUTED '
        '(&#167; B gives the counterexample). So the two are not two descriptions of one structure: '
        '2-adic depth and Kolmogorov complexity are different measures, and unbounded growth of the '
        'first does not carry the second to its threshold.'))

    E.append(Paragraph('A. Topological Path — Cauchy Convergence in Q<sub>2</sub>', S['h2']))
    E.append(body(
        'The 2-adic norm on Q<sub>2</sub> is defined by: &#8214;x&#8214;<sub>2</sub> = 2<sup>-v<sub>2</sub>(x)</sup>, '
        'where v<sub>2</sub>(x) is the 2-adic valuation of x. With the convention v<sub>2</sub>(0) = &#8734; '
        '(Mathlib&#8217;s valuation of 0 is 0), &#8214;0&#8214;<sub>2</sub> = 0, and Q<sub>2</sub>&#8217;s 0 is the element of infinite 2-adic depth. '
        'As the 2-adic depth chain has v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734; (forced by strict ascent, '
        'with IsDepthChain tying the valuation to the depth index), we have '
        '&#8214;S<sub>n</sub>&#8214;<sub>2</sub> &#8594; 0 by the norm&#8211;valuation identity above.'))
    E.append(body(
        'In a normed group, &#8214;S<sub>n</sub>&#8214;<sub>2</sub> &#8594; 0 already gives '
        'S<sub>n</sub> &#8594; 0: the limit is EXHIBITED as 0, not obtained from a Cauchy criterion, so '
        'no completeness is consumed at this step. Completeness of Q<sub>2</sub> is what the CONVERSE '
        'direction needs — Cauchy implies some limit exists — and T-IZ never takes it. '
        'A convergent sequence is automatically Cauchy. The '
        '2-adic depth chain is therefore a Cauchy sequence converging to 0 — the 2-adic limit of '
        'the chain is 0 &#8712; Q<sub>2</sub>.'))
    E.append(theorem_box(
        'Lemma T-IZ-A — Cauchy Convergence (Proved in Lean)',
        [
            'Let S : &#8469; &#8594; Q<sub>2</sub> be a sequence satisfying '
            '&#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> for all n &#8712; &#8469;. Then:',
            '(1) The norms &#8214;S(n)&#8214;<sub>2</sub> &#8594; 0 (squeeze between 0 and the '
            'geometric sequence 2<sup>-n</sup>, both tending to 0).',
            '(2) S(n) &#8594; 0 in Q<sub>2</sub> (norm &#8594; 0 iff sequence &#8594; 0 in a normed group).',
            'Lean: t_iz_cauchy — proved (sorry-free) in SemilatticeInstance.lean; footprint carries Classical.choice inherited from Mathlib&#8217;s p-adic analysis (see &#167; III). This is the topological core of T-IZ.',
        ]
    ))
    E.append(sp(6))
    E.append(body(
        'The geometry of the inside approach is the following: elements of Q<sub>2</sub> are arranged '
        'by their 2-adic valuation depth. Zero is the element of infinite depth — the deepest point. '
        'The 2-adic depth chain moves into greater and greater depth as n &#8594; &#8734;, approaching '
        'the depth of zero without ever reversing. The chain does not turn around and head back to 0. '
        'It descends into 0 by going deeper.'))
    E.append(body(
        'Remark R-II.1: The condition &#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> is '
        'equivalent to v<sub>2</sub>(S(n)) &#8805; n under the convention v<sub>2</sub>(0) = &#8734; (for S(n) &#8800; 0 no convention is needed). It asserts that the 2-adic valuation of '
        'S(n) is at least n — meaning S(n) is divisible by 2<sup>n</sup> in the 2-adic sense. '
        'As n &#8594; &#8734;, divisibility by arbitrarily large powers of 2 forces &#8214;S(n)&#8214;<sub>2</sub> '
        '&#8594; 0 and therefore S(n) &#8594; 0. This is the formal content of the "chain approaching '
        'the 2-adic depth of zero by forward motion."'))
    E.append(body(
        'Remark R-IZ-A — Closure of the valuation growth hypothesis: The strict growth condition '
        'v<sub>2</sub>(S(n)) &#8805; n was previously treated as a construction-level assumption '
        'stronger than the proved result t_iz_valuation_unbounded (sup v<sub>2</sub>(S(n)) = &#8734;). '
        'It is now Lean-derived. Theorem h_strict_from_r1_t3 (SemilatticeInstance.lean &#167;Ib) proves that any '
        'Q<sub>2</sub> chain satisfying the IsDepthChain modeling commitment — meaning its 2-adic '
        'valuations track a strict &#8469;-depth-index sequence — inherits strict valuation growth '
        'from IsDepthChain and IsStrictStateSequence. IsDepthChain (&#8704; n, v<sub>2</sub>(S(n)) = depths(n)) is the '
        'remaining modeling commitment: it asserts that 2-adic depth tracks the lattice depth index. '
        'This is a structural feature of the embedding, not a consequence of the abstract axioms. '
        'With IsDepthChain in place, R-IZ-A is formally closed.'))

    E.append(Paragraph('B. Informational Path — The Valuation-Complexity Bridge (Refuted)', S['h2']))
    E.append(body(
        'ZP-C L-INF establishes that the surprisal I(n) = n at ball-hierarchy depth n is unbounded. '
        'ZP-C reads &#8869; as corresponding to the limit point 0 &#8712; Q<sub>2</sub> — the limit of '
        'the binary ball hierarchy at infinite depth; that correspondence is a reading across carriers (MC-1). The depth-surprisal correspondence (ZP-C D4) '
        'gives the informational content of the 2-adic depth chain: as v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734;, '
        'the surprisal I(n) &#8594; &#8734; without bound.'))
    E.append(body(
        'Surprisal at depth n is a property of POSITION in the ball hierarchy: every point at 2-adic '
        'depth n has I(n) = n under the branching measure (ZP-C D4). Kolmogorov complexity '
        'K(x | n) is a property of the particular point x: the length of the shortest program that '
        'outputs x given n. The two are different measures, and the counterexample in the box below '
        'refutes the bridge between them.'))
    E.append(theorem_box(
        'Refuted Claim — Valuation-Complexity Bridge',
        [
            'Claim (REFUTED): v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734; &#8658; '
            'K(S<sub>n</sub> | n) / |S<sub>n</sub>| &#8594; 1.',
            'Counterexample: S<sub>n</sub> = 2<sup>n</sup>. Its 2-adic valuation is n (scaleChain_isDepthChain, '
            'ZeroParadox/Valuation/ScaleDepthWitness.lean, a file marked EXPERIMENTAL), so the premise holds, and the corpus&#8217;s ordinal tower read in '
            '&#8484;<sub>2</sub> has the same valuation profile (cnfToZp2_tower_valuation, '
            'ZeroParadox/Ordinal/Gentzen.lean). One fixed program computes S<sub>n</sub> from n, so '
            'K(S<sub>n</sub> | n) is bounded by a constant while |S<sub>n</sub>| = n + 1 bits, and the '
            'ratio tends to 0, not 1.',
            'Lean scope: the valuation half is checked. The complexity half is not in Lean, since '
            'Kolmogorov complexity is outside Lean scope (same category as DA-1 Path 3 in ZP-E): the '
            'bound K(2<sup>n</sup> | n) &#8804; c holds because one fixed program prints 2<sup>n</sup> '
            'from n, and c is the length of that program.',
            'The same chain meets T-IZ&#8217;s own bound: &#8214;2<sup>n</sup>&#8214;<sub>2</sub> = '
            '2<sup>-n</sup>, so S<sub>n</sub> = 2<sup>n</sup> satisfies h_bound of t_iz_complete '
            '(ZeroParadox/Valuation/SemilatticeInstance.lean). That hypothesis therefore does not encode '
            'incompressibility.',
        ],
        color=INDIGO
    ))
    E.append(sp(6))
    E.append(body(
        'Remark R-II.2: The formal spine of T-IZ is Steps 1 and 6. Step 1 (Cauchy convergence '
        'to 0 in Q<sub>2</sub>, t_iz_cauchy) is proved in Lean carrying Classical.choice from Mathlib&#8217;s '
        'p-adic analysis. Step 6 (anything filling the &#8869; ROLE IS that lattice&#8217;s &#8869;) '
        'is proved axiom-free in Lean via t_iz_limit_is_new_null &#8212; '
        'which establishes the role identification ONLY and must not be cited as a witness for the '
        'successor reading (t_iz_limit_is_new_null, declared in ZeroParadox/Valuation/SemilatticeInstance.lean and indexed in ZeroParadox/Order/SnapCannotBe.lean). '
        '&#8226; <b>The two steps are not joined.</b> Step 1 is about 0 &#8712; Q<sub>2</sub>; Step 6 is about a '
        'terminal in a semilattice L&#8242;, and takes the role property as its hypothesis h_role. '
        't_iz_complete conjoins them without identifying the two objects, and the identification is '
        'not merely unproved &#8212; Q<sub>2</sub>&#8217;s field structure supplies no join and the corpus defines none on Q<sub>2</sub>, so the role condition cannot be '
        'stated of the limit at all. That junction is not an open gap: the 0 of Q<sub>2</sub> and the '
        'algebraic &#8869; are distinct MEMBERS of the bottom family, and the cross-category identity '
        'is retired as ill-typed rather than outstanding (MC-1, CLAIMS.md). Steps 2–5 describe the original '
        'ZP-E informational argument connecting 2-adic depth to Kolmogorov complexity and DA-1 '
        'Path 3. Since DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying '
        'Path 3 as a KleeneStructure requirement — without Kolmogorov complexity — Steps 2–5 are informational context, not a '
        'proof dependency. The bridge in Step 2 is REFUTED (&#167; B): 2-adic depth growing without '
        'bound does not carry Kolmogorov complexity to the threshold P<sub>0</sub>, so this route does '
        'not reach P<sub>0</sub>.'))

    print('[build_zpi] Building Section III...')
    # ── SECTION III: THEOREM T-IZ ─────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Section III: Theorem T-IZ — Inside Zero', S['h1']),
        hr(),
    ]

    E.append(theorem_box(
        'Theorem T-IZ — Inside Zero',
        [
            'Statement: Every 2-adic depth chain (S<sub>n</sub>)<sub>n&lt;&#969;</sub> in Q<sub>2</sub>, '
            'nowhere zero, whose valuation equals a depth index in &#8469; that climbs at every step, so that '
            'its 2-adic valuation grows without bound, is a Cauchy sequence that converges, in the 2-adic metric, to 0. '
            'Reading that limit as an OCCUPANT of the bottom role is a modelling commitment and not '
            'part of the statement — Q<sub>2</sub>&#8217;s field structure supplies no join and the corpus defines none on Q<sub>2</sub>, so the role condition is not '
            'statable of it. Reading that occupant as a SUCCESSOR null is C-DA2, a further commitment.',
            'Formal hypotheses (t_iz_complete): S : &#8469; &#8594; Q<sub>2</sub> with '
            '&#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> for all n; for S(n) &#8800; 0 this is v<sub>2</sub>(S(n)) &#8805; n, and at S(n) = 0 it '
            'matches only under the convention v<sub>2</sub>(0) = &#8734; (Mathlib&#8217;s valuation of 0 is 0). '
            'That bound is derived (t_iz_h_bound_from_depth_chain) from IsStrictStateSequence on a depth '
            'index in &#8469;, IsDepthChain tying the valuations of S to that index, and S nowhere zero '
            '(Remark R-IZ-A, &#167;Ib). CC-1&#8217;s start at &#8869; and T3 monotonicity are statements about a '
            'chain in a ZP-A semilattice, not about S: Q<sub>2</sub>&#8217;s field structure supplies no join and no order of that kind.',
            'Conclusion: S(n) &#8594; 0 in Q<sub>2</sub>. That is the whole of what is proved here. '
            'The framework then READS the limit as satisfying the bottom role — a step stated in a '
            'different type and not carried by T-IZ — and DA-2 supplies the one-directional fact '
            'that anything satisfying that role IS the bottom already present. On that reading, DA-1 and then '
            'T-SNAP are CONDITIONAL on the limit reaching P<sub>0</sub> (which nothing here establishes) and on '
            'what DA-1 needs. DA-1 needs DP-2 and DP-2&#8217;s precondition, that the '
            'configuration reaching P<sub>0</sub> is there in Sense B (a running machine&#8217;s current configuration) '
            'and not in Sense A (an inert string); that precondition is what the occurrence commitment asserts, '
            'and DA-1 consumes it and does not supply it (ZP-E &#167; IV). Nothing here establishes that the limit '
            'reaches P<sub>0</sub>: its only route in this document, the bridge of &#167; II.B, is refuted. '
            't_iz_complete takes a KleeneStructure on the limit&#8217;s successor semilattice L&#8242; as a hypothesis and '
            'links L&#8242; to nothing; its DA-1 conjunct, that L&#8242;&#8217;s &#8869; is its Quine atom, is the Lean '
            'counterpart of DA-1&#8217;s Path 1, which does not derive the precondition. '
            'Reading the occupant as &#8869;\', a successor null for the next instantiation, is C-DA2, '
            'a modelling commitment, since nothing here produces a SECOND bottom.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('I. The Six-Step Proof', S['h2']))
    E.append(body('The proof of T-IZ follows six steps, corresponding to the proof obligation table:'))
    E += [
        li('Step 1 — Cauchy convergence: The 2-adic depth chain has &#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> '
           '(from v<sub>2</sub>(S(n)) &#8805; n — Lean-derived via h_strict_from_r1_t3 given IsDepthChain; R-IZ-A closed). '
           'By T-IZ-A (&#167; II.A), S(n) &#8594; 0 in Q<sub>2</sub>. Proved in Lean: t_iz_cauchy (carries Classical.choice from Mathlib p-adic analysis, &#167; III). ✓'),
        li('Step 2 — Valuation-complexity bridge (REFUTED): the claim that v<sub>2</sub>(S(n)) &#8594; &#8734; '
           'gives K(S(n)|n)/|S(n)| &#8594; 1 fails at S(n) = 2<sup>n</sup>, whose valuation is n and whose '
           'complexity given n is bounded (&#167; II.B). '
           'Not a proof dependency for T-IZ — DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement.'),
        li('Step 3 — P<sub>0</sub> at the limit (informational context): ZP-C D1&#8217;s threshold '
           'K(c<sub>1</sub>|n)/|c<sub>1</sub>| = 1. Step 2 is this step&#8217;s only route from the chain to that '
           'threshold, and with Step 2 refuted nothing here establishes that the limit meets the threshold.'),
        li('<b>Occurrence fence.</b> T-SNAP fixes the SHAPE of each step. It does not establish that any step is taken: tsnap_holds_but_nothing_moves exhibits a model in which T-SNAP holds and nothing moves. Throughout this document, "fires" narrates the commitment that instantiation occurs - before this note as well as after it - not a consequence of the theorem.'),
        li('Step 4 — DA-1, CONDITIONALLY: DA-1 needs DP-2 and DP-2&#8217;s precondition, that the configuration '
           'reaching P<sub>0</sub> is there in Sense B (a running machine&#8217;s current configuration) and not in '
           'Sense A (an inert string); that precondition is what the occurrence commitment asserts, and DA-1 '
           'consumes it and does not supply it (ZP-E &#167; IV). The Lean route (t_iz_complete) takes a KleeneStructure on L&#8242; '
           'as a hypothesis; its DA-1 conjunct, that L&#8242;&#8217;s &#8869; is its Quine atom, is the Lean counterpart '
           'of DA-1&#8217;s Path 1, which does not derive the precondition. Given the limit reaching P<sub>0</sub> '
           '(which nothing here establishes) and what DA-1 needs, DA-1 (ZP-E) applies. '
           'The TrackedOutput formal core (DP-2, Snap.lean § VI) establishes the machine-state transition.'),
        li('Step 5 — T-SNAP fires, on the same conditions as Step 4: given DA-1, instantiation = execution, and T-SNAP (ZP-E) gives '
           '&#8869; &#8744; &#949;<sub>0</sub> = &#949;<sub>0</sub>. '
           'Lean: t_snap_derived, proved axiom-free in Snap.lean. ✓ &#8212; the checkmark covers '
           'the transition SHAPE only. Reading the limit as a NEW &#8869;\' is a commitment; '
           'Snap.lean\'s NO-GO gauge holds T-SNAP in a model where nothing moves.'),
        li("Step 6 — DA-2 role identification: DA-2 (ZP-E) establishes that any state satisfying "
           '&#8704; x, S &#8744; x = x IS the &#8869; of its own lattice. '
           'That the Cauchy limit 0 &#8712; Q<sub>2</sub> satisfies that condition is a HYPOTHESIS, never a result: '
           't_iz_complete takes it as the argument h_role, about a terminal in a separate semilattice L&#8242;, '
           'and does not identify that terminal with the limit. Q<sub>2</sub>&#8217;s field structure supplies no join, and the corpus defines none on Q<sub>2</sub> &#8212; '
           'its ring structure supplies none with 0 as bottom (ZeroParadox/Valuation/ScaleBridge.lean) &#8212; '
           'so the condition is not statable there. '
           'Lean: t_iz_limit_is_new_null, proved directly from da2_bottom_characterization. ✓ &#8212; '
           'the checkmark covers the ROLE identification only, and only inside L&#8242;. It is NOT a novelty witness and must not be cited as one; reading the occupant as the &#8869; of a SUCCESSOR instantiation is C-DA2.'),
        sp(4),
    ]

    E.append(Paragraph('II. Proof Obligation Table', S['h2']))
    proof_rows = [
        ['Chain is Cauchy in (Q<sub>2</sub>, ‖·‖<sub>2</sub>)',
         'The geometric norm bound. What the framework supplies to REACH it (via &#167;Ia) is '
         'IsStrictStateSequence (T3 rides inside it &#8212; T3 alone is MONOTONE, and monotone does '
         'not reach this bound), IsDepthChain, the chain being nowhere zero, '
         'and the norm&#8211;valuation identity &#8214;x&#8214;<sub>2</sub> = '
         '2<sup>-v<sub>2</sub>(x)</sup> from ZP-B&#8217;s valuation construction (Lean: '
         'Padic.norm_eq_zpow_neg_valuation). NOT ZP-B T2, which is &#8220;every ball is clopen&#8221; '
         '&#8212; a separation result that says nothing about a valuation growing. '
         't_iz_cauchy itself binds none of them, and no lattice at all.',
         'Follows from existing structure — no new axiom',
         'Lean: t_iz_cauchy ✓ (proved; carries Classical.choice, Mathlib p-adic)'],
        ['‖S(n)‖<sub>2</sub> → 0 (Cauchy limit = 0)',
         'The geometric norm bound alone. Completeness of Q<sub>2</sub> is NOT consumed here: the '
         'limit is exhibited as 0 rather than obtained from a Cauchy criterion, so the proof runs '
         'through squeeze_zero and tendsto_zero_iff_norm_tendsto_zero, which hold in any normed group.',
         'Already in framework',
         'Lean: t_iz_cauchy (composite of t_iz_norm_tendsto_zero + t_iz_conv_zero) ✓'],
        ['sup v<sub>2</sub>(S(n)) = ∞',
         'Strict ascent (IsStrictStateSequence) + IsDepthChain (the valuation tracks the depth index). '
         'NOT no-top: a chain can satisfy HasNoTop and IsDepthChain with its valuation BOUNDED.',
         'Follows from strict ascent + T3 — no-top supplies the room, not the growth',
         'Lean: t_iz_valuation_unbounded ✓ (proved; carries Classical.choice, Mathlib p-adic)'],
        ['v<sub>2</sub> → ∞ ⟹ K/|S| → 1 (REFUTED)',
         'Counterexample S<sub>n</sub> = 2<sup>n</sup>: valuation n (scaleChain_isDepthChain), '
         'complexity given n bounded by the length of one fixed program printing 2<sup>n</sup> from n (not Lean)',
         'Not a proof dependency',
         'Refuted (&#167; II.B). Not required: formal spine is Steps 1 + 6; '
         'DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement.'],
        ['P<sub>0</sub> fires DA-1, CONDITIONALLY: given the limit reaching P<sub>0</sub> '
         '(which nothing here establishes), DP-2, and DP-2&#8217;s precondition Sense B, which the occurrence commitment asserts',
         'ZP-C D1 + DA-1 (ZP-E)',
         'No new axiom; all three premises are outside this document&#8217;s results',
         'ZPE formal core: da1_minimal_path, DP-2. No checkmark: none of the three premises is established here'],
        ['DA-1 fires T-SNAP',
         'ZP-E T-SNAP',
         'Already in framework',
         'Lean: t_snap_derived ✓ (axiom-free)'],
        ['The limit occupies the ⊥ role (READING; ⊥\' a further READING)',
         'DA-2 (ZP-E)',
         'Role-recognition: already in framework. Occupancy and novelty: COMMITMENTS',
         'Lean: t_iz_limit_is_new_null, c_da2_novelty ✓ — these prove role ⟹ identity with the '
         'bottom ALREADY THERE. Neither is a novelty witness and neither may be cited as one.'],
    ]
    E.append(data_table(
        ['Claim', 'Source', 'New axiom?', 'Lean status'],
        proof_rows,
        [TW*0.26, TW*0.26, TW*0.24, TW*0.24]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. Lean Scope', S['h2']))
    E.append(body(
        'The Lean file SemilatticeInstance.lean formalizes the formal spine of T-IZ: Step 1 (Cauchy convergence, '
        '§ I) and Step 6 (DA-2 role identification, § IV), which are carried together as a CONJUNCTION '
        'and are not joined to each other. The two steps sit on different footings, and the document states this honestly: Step 6 '
        '(t_iz_limit_is_new_null) is proved <i>axiom-free</i> — it is the ROLE half only: in one semilattice, '
        'anything satisfying the join-identity IS that semilattice&#8217;s &#8869;, the one already there. '
        'That the &#8869; so reached is a NEW one, &#8869;&#8242;, is a commitment (C-DA2) and not this theorem; '
        'in the 2-adic realization the arc reapproaches the SAME 0 (snap_arc_z2_loop). Step 1 (t_iz_cauchy) '
        'is proved sorry-free but carries Classical.choice, and NOT because of the analysis. '
        'Measured: (1 : &#8474;<sub>[2]</sub>) &#8800; 0 — no limit, no filter, no convergence '
        'lemma anywhere in the statement — already reports [propext, Classical.choice, Quot.sound]. '
        'The dependence sits in Mathlib&#8217;s instance packaging, not in the metric: '
        'Polynomial (ZMod 5) is no kind of completion and reports the same footprint, while ZMod 5 '
        'reports [propext, Quot.sound]. Mathlib&#8217;s analytic lemmas (squeeze_zero, the '
        'geometric-limit lemma, tendsto_zero_iff_norm_tendsto_zero) carry it too, so the '
        'footprint cannot separate the two. ⚠ A footprint is a fact about the PROOF, never about the '
        'type: the same statement (1 : &#8474;) &#8800; 0 reports Classical.choice through one_ne_zero '
        'and [propext, Quot.sound] through decide. ⚠ The corpus&#8217;s choice-free valuation facts are NOT a '
        'counterexample here: v2_bot is [propext] because v2 : &#8469; &#8594; &#8469;&#8734; is stated over '
        'the NATURALS, so that contrast is between two carriers and not between algebra and analysis. '
        'The footprint reports the library this development is built on. Where choice enters this corpus, '
        'and what is established about it, is recorded at ZeroParadox/AxiomProfile.lean (the core is '
        'choice-free; T-SNAP depends on no axioms at all) and ZeroParadox/Ordinal/SyntacticCollapse.md '
        '(a choice-free syntactic surrogate for the metric collapse, which states of itself that it '
        'settles the standing conjecture in neither direction). Steps 2–5 (the '
        'valuation-complexity bridge and DA-1/T-SNAP path) describe the ZP-E informational '
        'argument and are not proof dependencies; the bridge in Step 2 is refuted (&#167; II.B). DA-1 is closed given DP-2 '
        '(da1_minimal_path; CLAIMS.md, Tier 5); ZP-K witnesses its Path 1 (da1_closed_concrete: ⊥ is the '
        'unique Quine atom of MachinePhase). The DP-2 commitment is not discharged by either. '
        'The theorems in SemilatticeInstance.lean, '
        'with their axiom footprints:'))
    E += [
        li('t_iz_limit_is_new_null: anything satisfying the DA-2 &#8869; role IS that lattice&#8217;s &#8869; '
           '(the structural core of the snap-arc; <b>axiom-free</b>). The role property is its HYPOTHESIS; '
           'that the Cauchy limit satisfies it is not established here, and is not statable in Q<sub>2</sub>.'),
        li('c_t_iz_null_balance: a non-bottom state cannot satisfy the &#8869; role (choice-free, [propext]).'),
        li('t_iz_cauchy: a sequence in Q<sub>2</sub> with &#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> converges to 0 (topological core; carries Classical.choice from '
           'Mathlib&#8217;s p-adic convergence, not a framework commitment).'),
        li('t_iz_valuation_unbounded: sup v<sub>2</sub>(S(n)) = &#8734; (carries Classical.choice, Mathlib p-adic).'),
        li('t_iz_c3_compatible: C3 irreversibility is preserved — Cauchy sequences &#8800; continuous paths '
           '(carries Classical.choice, Mathlib p-adic).'),
        li('t_iz_h_bound_from_depth_chain: h_bound derived from THREE hypotheses, of which exactly one is a '
           'ZP-A lattice condition — IsStrictStateSequence, and it is a condition on the DEPTH INDEX. The '
           'other two live in Q<sub>2</sub>: that the chain is nowhere zero, and IsDepthChain, the BRIDGE '
           'saying the 2-adic valuation tracks that index. IsDepthChain takes no ZPSemilattice instance at '
           'all; &#167;Ib records it as an undischarged modelling commitment, and it links the depth index '
           'and the chain in Q<sub>2</sub> without identifying them. '
           'Closes the &#8214;S<sub>0</sub>&#8214; factor gap between &#167;Ib and t_iz_complete (optional '
           'transparency lemma; the analytic proof carries Classical.choice).'),
        li('t_iz_complete_from_axioms: T-IZ complete variant taking the three hypotheses above in place of a '
           'bare h_bound, and binding four more — a second semilattice L&#8242; with a KleeneStructure '
           'instance, a terminal, an &#949;<sub>0</sub>&#8242;, and h_role, the role property HANDED IN and '
           'never derived. Auditable in one theorem, but its hypotheses are not all lattice conditions (carries '
           'Classical.choice; optional transparency variant; t_iz_complete is the canonical theorem).'),
        sp(4),
    ]
    E.append(derived(
        'Status: DERIVED THEOREM — formal spine: t_iz_cauchy (Step 1, proved; carries Classical.choice '
        'from Mathlib p-adic analysis) + '
        't_iz_limit_is_new_null (Step 6, axiom-free via DA-2). These two steps '
        'are the formal spine, carried as a conjunction and not joined to one another. '
        't_iz_valuation_unbounded, c_t_iz_null_balance, t_iz_c3_compatible also proved. '
        'Transparency variants: t_iz_h_bound_from_depth_chain + t_iz_complete_from_axioms '
        'name each hypothesis separately for reviewer auditability — one lattice condition '
        '(IsStrictStateSequence), one 2-adic depth bridge (IsDepthChain, a modelling commitment), '
        'one nonvanishing condition, and for the complete variant h_role handed in — t_iz_complete '
        'is the canonical theorem. '
        'Steps 2–5 (valuation-complexity bridge, refuted, + DA-1/T-SNAP) are informational context — '
        'DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement, no Kolmogorov complexity required. '
        'No new axioms. ✓'))

    print('[build_zpi] Building Section IV...')
    # ── SECTION IV: COMPATIBILITY WITH IRREVERSIBILITY ────────────────────────
    E += [
        hr(),
        Paragraph('Section IV: Compatibility with the Irreversibility Results', S['h1']),
        hr(),
    ]

    E.append(body(
        'T-IZ does not violate any irreversibility result in the framework. The inside approach '
        'is not a reversal — it is a structurally different operation. Each irreversibility result '
        'governs a specific structure; T-IZ uses a different structure not governed by any of them.'))

    E.append(Paragraph('I. ZP-A R1 — No Subtraction', S['h2']))
    E.append(body(
        'R1 states that the join-semilattice (L, &#8744;, &#8869;) has no subtraction operator: '
        'for any x, y &#8712; L with x &lt; y, there is no z such that y &#8744; z = x. '
        'This closes the algebraic door to reversal.'))
    E.append(body(
        'T-IZ does not use subtraction. The chain never joins "downward." Every step is a join '
        'operation S<sub>n+1</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub> for some &#945;<sub>n</sub> &#8805; 0 '
        '(ZP-A T3 monotonicity). The approach to 0 in Q<sub>2</sub> is not a join toward 0 — it '
        'is a Cauchy sequence whose 2-adic norm tends to 0. The chain never subtracts, so R1 is not '
        'violated. R1 plays no further part in T-IZ: what makes the valuation grow without bound is '
        'strict ascent, and what leaves the chain somewhere to go, in a carrier that has it, is the order '
        'property HasNoTop (ZeroParadox/Order/Lattice.lean), a hypothesis on the carrier and a different proposition.'))

    E.append(Paragraph('II. ZP-B C3 — No Continuous Path to Zero', S['h2']))
    E.append(body(
        'C3 states: there is no continuous path &#947; : [0,1] &#8594; Q<sub>2</sub> with '
        '&#947;(0) = x &#8800; 0 and &#947;(1) = 0. This closes the topological door to reversal '
        'via continuous motion.'))
    E.append(body(
        'T-IZ uses Cauchy sequence convergence, not a continuous path. A Cauchy sequence '
        '(S<sub>n</sub>)<sub>n&#8712;&#8469;</sub> tending to 0 is a countable sequence of '
        'discrete points. It is not a continuous function [0,1] &#8594; Q<sub>2</sub>. These '
        'are distinct mathematical structures. C3\'s universal quantifier ranges over continuous '
        'functions; T-IZ\'s convergence is a statement about countable sequences. The two results '
        'do not conflict.'))
    E.append(body(
        'Lean: t_iz_c3_compatible (SemilatticeInstance.lean) proves this directly: the statement of C3 '
        '(c3_irreversible from ZPB) holds without modification alongside T-IZ. C3 blocks '
        'continuous paths; T-IZ uses Cauchy sequences. They govern different structures. ✓'))

    E.append(Paragraph('III. ZP-G AX-G2 — No Morphism to the Initial Object', S['h2']))
    E.append(body(
        'AX-G2 states that in the categorical structure C, hom(X, 0) = &#8709; for X &#8800; 0: '
        'no morphism within C leads back to the initial object. This closes the categorical door '
        'to reversal.'))
    E.append(body(
        'T-IZ is not a morphism within C: it is a convergence statement in Q<sub>2</sub>, and no arrow of '
        'the category C of the current instantiation is involved. Reading the limit as the termination of C '
        'and the opening of a successor C\', with its own &#8869;\', is the cycle reading, not a result; its '
        'premises are stated in &#167; V.III. AX-G2 quantifies only over morphisms within a single category; it has nothing to '
        'say about the transition between categories. The categorical structure is preserved '
        'intact within each instantiation.'))

    E.append(Paragraph('IV. Summary', S['h2']))
    E.append(body(
        'The irreversibility results and T-IZ are not in tension. They describe different things. '
        'Irreversibility (R1, C3, AX-G2) governs motion within an instantiation branch: no '
        'algebraic subtraction, no continuous topological return, no categorical reversal. '
        'T-IZ governs what happens at the branch\'s ordinal limit: the 2-adic depth chain converges, by Cauchy '
        'convergence, to 0 &#8712; Q<sub>2</sub> — a structure that none of the irreversibility '
        'results governs or addresses. Reading that 0 as filling the bottom role is a commitment, and '
        'reading it as a successor null is C-DA2, a further one.'))
    E.append(callout(
        'The inside approach is not a violation of irreversibility. It is the discovery of a '
        'structure that irreversibility does not reach. Three doors to zero are closed (R1, C3, '
        'AX-G2). T-IZ uses a fourth passage — Cauchy sequence convergence — that none of the '
        'three irreversibility theorems govern.',
        bg=GREEN_LITE, border=GREEN_DARK
    ))
    E.append(sp(6))

    print('[build_zpi] Building Section V...')
    # ── SECTION V: FRAMEWORK CLOSURE ──────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Section V: OQ-E2, the Null Balance, and the Cycle Reading', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. Resolution of OQ-E2', S['h2']))
    E.append(body(
        'OQ-E2 (Cardinality-Semilattice Correspondence) has been open since the initial ZP-E release. '
        'It asks: do specific semilattice structures correspond to specific cardinality regimes, '
        'and can the framework make predictions about which instantiations satisfy CH?'))
    E.append(body(
        'T-IZ provides the path to closing OQ-E2 as follows. The ascending chain '
        '(S<sub>n</sub>)<sub>n&lt;&#969;</sub> is indexed by &#969; — the first infinite ordinal. '
        'This indexing is forced, not chosen: the binary alphabet gives a countable state space; '
        'Q<sub>2</sub> is a separable metric space; surprisal I(n) = n grows by integer steps '
        '(ZP-C D4). Every component of the framework that generates an ordinal index generates '
        'a countable one. The state sequence is necessarily indexed by &#969;, not &#969;<sub>1</sub> '
        'or any uncountable ordinal.'))
    E.append(body(
        'This pins the ordinal depth of each instantiation to &#969;. OQ-E2\'s perspective-relative '
        'cardinality (DA-3) is then resolved as follows: internal observers see a proper initial '
        'segment of &#969; (finite); external observers see all of &#969;. The perspective-relativity '
        'is ordinal, not set-theoretically free — it is the difference between a finite position '
        'in the chain and the view of the full chain from outside. The cardinality of the fan at '
        'each node is determined by the countable substrate.'))
    E.append(derived(
        'OQ-E2 status after T-IZ: PARTIALLY CLOSED. The ordinal indexing &#937; = &#969; is forced '
        'by the countable binary substrate (ZP-C D4, ZP-B Q<sub>2</sub> separability, binary alphabet). '
        'Internal/external perspective relativity is ordinal, not set-theoretically free. '
        'Formal connection between specific semilattice structures and specific CH instances '
        'remains deferred — that is the remaining open question in OQ-E2. ✓ (partial)'))

    E.append(Paragraph('II. The Null Balance', S['h2']))
    E.append(body(
        'The null balance 0 + x + (&#8722;x) = 0 is an arithmetic READING of the cycle of an '
        'instantiation branch, never a theorem of the structure: a ZPSemilattice carries join and '
        '&#8869; and no additive inverse, so the identity is not statable there at all. The cycle it reads '
        'is itself a reading; its premises are stated in &#167; V.III. As a reading the balance strings its '
        'three terms across &#969; state changes: the branch begins at &#8869; (0), generates '
        '&#949;<sub>0</sub> and successors (+x), and at the ordinal limit the 2-adic chain converges to '
        'Q<sub>2</sub>&#8217;s 0 (&#8722;x).'))
    E.append(body(
        'What T-IZ supplies to this reading is the convergence; the balance itself stays a reading. "Balance" here is not '
        'subtraction in (L, &#8744;, &#8869;) — R1 prohibits that. Two carriers carry the reading: the lattice '
        'chain begins at its semilattice&#8217;s &#8869; (CC-1) and ascends under T3, and the 2-adic depth chain, '
        'nowhere zero, converges to 0 &#8712; Q<sub>2</sub>. That the branch closes there is the cycle '
        'reading; its premises are stated in &#167; V.III. The '
        'CONVERGENCE is a theorem, given IsDepthChain (a modelling commitment); that the role-filler is a '
        'DISTINCT &#8869;\' rather than the &#8869; it began at is C-DA2, and in the '
        '2-adic realization the arc returns to the same 0 (snap_arc_z2_loop).'))
    E.append(callout(
        'Null Balance (role-RECOGNITION derived; occupancy and novelty COMMITTED): For every sequence '
        '(S<sub>n</sub>)<sub>n&lt;&#969;</sub> in Q<sub>2</sub>, nowhere zero, with &#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> '
        '(derived via t_iz_h_bound_from_depth_chain from IsDepthChain and IsStrictStateSequence on a depth index in &#8469; — R-IZ-A closed): '
        'the sequence converges to 0 in Q<sub>2</sub>. CC-1&#8217;s start at &#8869; belongs to the semilattice chain, not to S. '
        'The balance 0 + x + (&#8722;x) = 0 is a '
        'READING of the cycle of &#167; V.III, whose premises are stated there, and not a theorem — a ZPSemilattice has no additive inverse, so it is not '
        'statable in the structure T-IZ is about — where x '
        'represents &#969; state changes under T3, and (&#8722;x) represents the convergence to Q<sub>2</sub>&#8217;s 0. '
        'No new axioms required for the convergence.',
        bg=INDIGO_LITE, border=INDIGO
    ))
    E.append(sp(6))

    E.append(Paragraph('III. The Cycle Reading', S['h2']))
    E.append(body(
        'The framework reads the steps below as a cycle. The cycle is a reading, not a theorem. What T-IZ '
        'proves is that the 2-adic depth chain converges to 0 in Q<sub>2</sub>, given IsDepthChain (a modelling '
        'commitment), IsStrictStateSequence and the chain being nowhere zero (t_iz_h_bound_from_depth_chain, '
        't_iz_cauchy), together with the separate implication that anything filling the bottom '
        'role of a semilattice IS that semilattice&#8217;s &#8869; (t_iz_limit_is_new_null). For the cycle to '
        'begin again or close at the limit, it needs every one of the following further premises, and none is '
        'established here: (a) the reading that the limit fills the &#8869; role, a modelling commitment and a '
        'reading across two carriers, since the role condition is not statable in Q<sub>2</sub> (MC-1); '
        '(b) the limit reaching the incompressibility threshold P<sub>0</sub>, which nothing here establishes, '
        'since its only route in this document, the valuation-complexity bridge, is refuted (&#167; II.B); '
        '(c) what DA-1 needs: DP-2 and DP-2&#8217;s precondition, that the configuration reaching P<sub>0</sub> '
        'is there in Sense B (a running machine&#8217;s current configuration) and not in Sense A (an inert '
        'string), which the occurrence commitment asserts and DA-1 consumes and does not supply (ZP-E &#167; IV); '
        'and (d) for the next branch to start from a NEW null &#8869;\' rather than the &#8869; already there, '
        'C-DA2, a further commitment; in the 2-adic realization the arc returns to the SAME 0 '
        '(snap_arc_z2_loop). The steps of the cycle:'))
    E += [
        li('T-SNAP: From &#8869;, existence emerges — the shape of that emergence is derived and its '
           'occurrence is committed to, not proved. The Binary Snap '
           '&#8869; &#8594; &#949;<sub>0</sub> is irreversible. This is the opening of the branch.'),
        li('T3 (Monotonicity): The state sequence ascends without interruption. Each step '
           'adds informational content irreversibly. The chain climbs.'),
        li('No Top: In a carrier with HasNoTop (a hypothesis on the carrier, not a law: MachinePhase and '
           'OntologicalStates have a top) there is always a strictly greater element, so no chain halts for want of '
           'anywhere to go. It supplies the POSSIBILITY of ascent; IsStrictStateSequence is its '
           'OCCURRENCE, and that is the hypothesis T-IZ actually consumes. Not ZP-A&#8217;s R1, '
           'which is no-subtraction.'),
        li('T-IZ: The 2-adic depth chain converges to 0 &#8712; Q<sub>2</sub> at the ordinal limit &#969;. '
           'That DA-1 and T-SNAP fire again there, closing the branch, is the reading whose premises are '
           'stated above.'),
        li('DA-2 (Instantiation Succession): &#8869;\' is read as the foundation of the next instantiation, '
           'and the cycle repeats; this too is the reading whose premises are stated above.'),
        sp(4),
    ]
    E.append(body(
        'The formal spine of T-IZ takes the bound &#8214;S(n)&#8214;<sub>2</sub> &#8804; 2<sup>-n</sup> '
        'as a condition derived from IsStrictStateSequence, the IsDepthChain modeling commitment and the chain '
        'being nowhere zero (t_iz_h_bound_from_depth_chain, &#167;Ib — R-IZ-A closed). Given that condition, two charts, two carriers. '
        'In Q<sub>2</sub>: the 2-adic depth chain converges to Q<sub>2</sub>&#8217;s 0 (t_iz_cauchy), and 0 is the LIMIT, '
        'not a term, since the chain is nowhere zero. Q<sub>2</sub>&#8217;s field structure supplies no join, and the '
        'corpus defines no ZPSemilattice on Q<sub>2</sub>, so the role condition is not statable of the limit here. '
        '(A join could be chosen: every inhabited carrier admits one, ZeroParadox/Order/Lattice.lean. On &#8484;<sub>2</sub>, '
        'the 2-adic integers, the corpus supplies one with 0 as its bottom (the example at '
        'ZeroParadox/Valuation/Scale.lean &#167; V); 0 filling that bottom is a choice of operation, '
        'not something T-IZ derives.) In a ZPSemilattice: the bottom ROLE is the join-identity, and anything filling '
        'it IS that semilattice&#8217;s existing &#8869; (t_iz_limit_is_new_null). Reading the 2-adic limit as '
        'filling that role is a READING across the two carriers, and the cross-carrier identity is retired '
        'as ill-typed (MC-1). That the &#8869; so reached is a NEW one is C-DA2, a commitment; in the 2-adic '
        'realization the arc returns to the SAME 0 (snap_arc_z2_loop).'))

    E.append(key_result_box([
        'T-SNAP: &#8869; &#8594; &#949;<sub>0</sub>, shape derived and occurrence committed (existence emerges from null).',
        'T-IZ: a nowhere-zero 2-adic depth chain S<sub>0</sub>, S<sub>1</sub>, S<sub>2</sub>, ... &#8594; 0 &#8712; Q<sub>2</sub> at &#969;, '
        'ROLE-RECOGNITION derived; OCCUPANCY and NOVELTY committed. What is proved is the 2-adic '
        'convergence (t_iz_cauchy) and, separately, that anything playing the bottom role IS the '
        'bottom (t_iz_limit_is_new_null). That the limit is a thing playing that role is a '
        'commitment, not a theorem — the role condition is not statable in Q<sub>2</sub>; that the '
        'bottom so reached is a NEW one is a further commitment.',
        'The cycle and its closure are a reading, not a theorem; its premises are stated in &#167; V.III. '
        'Strict valuation growth is '
        'Lean-derived from IsDepthChain (a modelling commitment) + IsStrictStateSequence (h_strict_from_r1_t3). '
        'No new axioms required beyond AX-B1, AX-G1, AX-G2.',
    ]))
    E.append(sp(6))

    print('[build_zpi] Building registers...')
    # ── UPDATED OPEN ITEMS REGISTER ───────────────────────────────────────────
    E += [hr(), Paragraph('Open Items Register', S['h1'])]

    oq_rows = [
        ['T-IZ: Inside Zero Theorem',
         'CONVERGENCE + ROLE-RECOGNITION DERIVED — occupancy and novelty COMMITTED',
         'Every nowhere-zero 2-adic depth chain S<sub>0</sub>, S<sub>1</sub>, ... in Q<sub>2</sub> whose '
         'valuation equals a depth index in &#8469; that climbs at every step converges to 0 in '
         'Q<sub>2</sub>; reading that limit as the '
         'occupant of the bottom role, and that occupant as a successor null, are commitments. '
         'Formal spine: Step 1 (t_iz_cauchy, carries Mathlib p-adic Classical.choice) + Step 6 '
         '(t_iz_limit_is_new_null, axiom-free via DA-2). Steps 2–5 are informational context — the ZP-E path, whose valuation-complexity bridge is refuted (&#167; II.B); '
         'DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement. No new axioms required.'],
        ['OQ-E2: Cardinality-semilattice correspondence',
         'PARTIALLY CLOSED — &#937; = &#969; forced',
         'Ordinal indexing &#937; = &#969; forced by countable binary substrate (ZP-C D4, Q<sub>2</sub> separability). '
         'Internal/external perspective relativity is ordinal, not set-theoretically free. '
         'Formal connection to specific CH instances: still open — deferred to future work.'],
        ['Null balance: 0 + x + (&#8722;x) = 0',
         'CLOSED for ROLE-RECOGNITION — occupancy and novelty COMMITTED',
         'The convergence half is derived from T-IZ: the lattice chain starts at its semilattice&#8217;s &#8869; '
         '(CC-1) and ascends under T3, and the nowhere-zero 2-adic depth chain converges to 0 &#8712; Q<sub>2</sub>. Reading that '
         'limit as an occupant of the bottom role is a COMMITMENT, not a consequence — the '
         'join-identity is not statable in Q<sub>2</sub>. On that reading, DA-2 identifies the '
         'occupant with the &#8869; already there. '
         '"&#8722;x" is not subtraction in L — it is the 2-adic approach to 0 by forward motion; reading it as a '
         'return in the cycle is the reading whose premises are stated in &#167; V.III. '
         'That the occupant is a NEW &#8869;\' is the commitment, not the theorem.'],
        ['Valuation-complexity bridge',
         'REFUTED — counterexample S<sub>n</sub> = 2<sup>n</sup>',
         'The ZP-E route from 2-adic depth to Kolmogorov complexity and DA-1 Path 3. '
         'Its implication v<sub>2</sub>(S<sub>n</sub>) &#8594; &#8734; &#8658; K(S<sub>n</sub> | n) / |S<sub>n</sub>| &#8594; 1 '
         'fails at S<sub>n</sub> = 2<sup>n</sup> (&#167; II.B): valuation n, complexity given n bounded, '
         'ratio &#8594; 0. The valuation half is checked (scaleChain_isDepthChain); the complexity half is '
         'outside Lean scope: one fixed program prints 2<sup>n</sup> from n, which bounds K(2<sup>n</sup> | n) by its length. '
         'Not a proof dependency for T-IZ: formal spine is Steps 1 + 6 (Step 6 axiom-free; Step 1 carries Mathlib p-adic choice); '
         'DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement.'],
        ['T-IZ Lean sorry fill',
         'CLOSED — ZeroParadox/Valuation/SemilatticeInstance.lean',
         't_iz_norm_tendsto_zero and t_iz_conv_zero filled; t_iz_cauchy proved (carries Mathlib p-adic Classical.choice). '
         'All SemilatticeInstance.lean theorems compile with no sorry. '
         'Axiom footprint: standard foundational axioms only (propext, Quot.sound, and Classical.choice '
         'from Mathlib p-adic analysis on the convergence theorems; the DA-2 step is axiom-free).'],
        ['AX-1: Binary Snap Causality',
         'RETIRED — shape proved as T-SNAP (ZP-E); the first snap occurs given the occurrence commitment and DA-1',
         'AX-1 (Binary Snap Causality) is retired. Its content was split in two: the shape of the snap is proved, as Theorem T-SNAP, and that the first snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). '
         'tsnap_holds_but_nothing_moves shows T-SNAP does not carry it. T-SNAP is derived in ZP-E. '
         'A snap at the ordinal limit is the cycle reading, not a consequence of T-IZ; its premises are '
         'stated in &#167; V.III.'],
        ['Remaining axioms',
         'INTENTIONAL — AX-B1, AX-G1, AX-G2',
         'These are the named axioms. The occurrence commitment is not on this list because it is a commitment, not a named axiom. T-IZ requires no additions.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.20, TW*0.58]
    ))

    # ── TRACEABILITY REGISTER ─────────────────────────────────────────────────
    E += [sp(8), hr(), Paragraph('Traceability Register', S['h1'])]

    trace_rows = [
        ['T-IZ: Inside Zero',
         'What the chain CONSUMES: IsStrictStateSequence, IsDepthChain, the chain being nowhere zero, and '
         'ZP-B&#8217;s norm&#8211;valuation identity. HasNoTop supplies the room and is consumed by nothing '
         'here. Also ZP-B T5/C3 for the irreversibility comparison only; ZP-C L-INF, D1; '
         'ZP-E DA-1, T-SNAP, DA-2',
         'None',
         'Role derived — T-IZ ✓ (formal spine Steps 1+6: Step 6 axiom-free, Step 1 carries Mathlib p-adic choice; bridge: refuted). Novelty of the successor bottom: COMMITMENT, not proved.'],
        ['Null Balance 0 + x + (&#8722;x) = 0',
         'T-IZ + T-SNAP + DA-2 (ZP-E)',
         'None',
         'Role derived — the convergence is T-IZ; the balance is a reading, not a theorem. Novelty: commitment.'],
        ['OQ-E2 partial closure',
         'ZP-C D4 (binary alphabet, I(n)=n); ZP-B (Q<sub>2</sub> separable); T-IZ (&#937; = &#969;)',
         'None',
         'Partially closed — &#937; = &#969; forced by countable substrate; CH connection deferred.'],
        ['t_iz_valuation_unbounded (Lean)',
         'int_strict_mono_ge (induction on &#8484;); omega (integer arithmetic)',
         'None',
         'Lean: proved ✓ — standard foundational axioms only. '
         'Formalises "sup v<sub>2</sub>(S(n)) = &#8734;" — proof obligation table row 3.'],
        ['t_iz_cauchy (Lean)',
         'ZP-B (Q<sub>2</sub> normed field); geometric tendsto; Mathlib.Analysis.SpecificLimits.Basic',
         'None',
         'Lean: proved ✓ (t_iz_norm_tendsto_zero, t_iz_conv_zero filled; carries Mathlib p-adic Classical.choice)'],
        ['t_iz_limit_is_new_null (Lean)',
         'da2_bottom_characterization',
         'None',
         'Lean: proved ✓ (direct delegation to DA-2)'],
        ['c_t_iz_null_balance (Lean)',
         'c_da2_novelty',
         'None',
         'Lean: proved ✓ (direct delegation to C-DA2)'],
        ['t_iz_c3_compatible (Lean)',
         'c3_irreversible',
         'None',
         'Lean: proved ✓ (C3 holds unmodified; Cauchy sequences &#8800; continuous paths)'],
        ['Valuation-complexity bridge',
         'ZP-C D1, L-INF, Remark R-BRIDGE; ZP-B T2; AIT (standard)',
         'N/A',
         'REFUTED (&#167; II.B; counterexample S<sub>n</sub> = 2<sup>n</sup>) — not load-bearing. DA-1 is closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement. '
         'The complexity half is outside Lean scope.'],
        ['t_iz_h_bound_from_depth_chain (Lean)',
         'h_strict_from_r1_t3 (&#167;Ib); t_iz_r1_t3_geometric_bound; '
         'Padic.norm_eq_zpow_neg_valuation (depths 0 : &#8469; &#8658; &#8214;S<sub>0</sub>&#8214;<sub>2</sub> &#8804; 1)',
         'None',
         'Lean: proved ✓ — optional transparency lemma. Derives h_bound from IsStrictStateSequence '
         '(the one lattice condition), IsDepthChain (the 2-adic bridge, binding no semilattice) and '
         'the chain being nowhere zero, closing the &#8214;S<sub>0</sub>&#8214; factor gap '
         'between &#167;Ib and t_iz_complete.'],
        ['t_iz_complete_from_axioms (Lean)',
         't_iz_h_bound_from_depth_chain; t_iz_complete',
         'None',
         'Lean: proved ✓ — optional transparency variant. Replaces h_bound with three hypotheses, '
         'of which only IsStrictStateSequence is a ZP-A lattice condition; IsDepthChain is the '
         'bridge to the 2-adic valuation and binds no semilattice, and the chain must be nowhere '
         'zero. It still carries h_role explicitly, which is the hypothesis nothing here grounds. '
         'Canonical theorem: t_iz_complete.'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.20, TW*0.32, TW*0.10, TW*0.38]
    ))

    # ── CLOSING ───────────────────────────────────────────────────────────────
    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>End of ZP-I | Theorem T-IZ: Inside Zero | '
            'R-IZ-A closed: strict valuation growth derived from IsDepthChain + IsStrictStateSequence (h_strict_from_r1_t3, &#167;Ib) | '
            'IsDepthChain remains a modelling commitment | '
            'Framework closure: a reading; its premises are stated in &#167; V.III | '
            'Formal spine: Step 6 axiom-free (t_iz_limit_is_new_null), Step 1 carries Mathlib p-adic Classical.choice (t_iz_cauchy) | '
            'Valuation-complexity bridge: refuted; not load-bearing, since the convergence T-IZ proves does not pass through it | '
            'DA-1 closed given DP-2 (ZP-E), with ZP-K witnessing Path 1 and carrying Path 3 as a KleeneStructure requirement | '
            'Remaining axioms: AX-B1, AX-G1, AX-G2 | No new axioms required</i>',
            S['endnote']),
    ]

    print(f'[build_zpi] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpi] Written: {out_path}')


if __name__ == '__main__':
    build()
