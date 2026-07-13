"""
Zero Paradox — ZP-N: The Constructive Snap PDF Builder
Version 1.0 | July 2026

v1.0: Initial release. The choice-free constructive companion to ZP-L. The ε₀ snap-from-below is rebuilt
syntactically on ordinal notations (ONote / Cantor normal form), never touching Mathlib's choice-saturated
Ordinal type, so the three snap results are choice-free — [propext] only, free even of Quot.sound:
exp_lt_term (an exponent is strictly below its own term), omegaPow_no_fixedpoint (no notation is a fixed
point of x ↦ ω^x), tower_strictMono (the ω-tower climbs without bound below ε₀). Finding: ZP-L's
Classical.choice at ε₀ is representational (inherited from Mathlib's Ordinal), not intrinsic. Side finding:
tower_NF (well-formedness) DOES carry Classical.choice — choice lives at the syntax→semantics bridge. Open:
the matching minimality (ε₀ is the LEAST fixed point) quantifies over the limit no notation names.
Lean: ConstructiveOrdinals.lean. Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.0'
FIRST_RELEASED = 'July 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-N_The_Constructive_Snap.pdf')
    print(f'[build_zpn] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-N: The Constructive Snap',
                   'ZP-N: The Constructive Snap', 'Version ' + VERSION)
    E = []

    print('[build_zpn] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-N: The Constructive Snap', S['title']),
        Paragraph('the &#949;<sub>0</sub> snap from below, choice-free on ordinal notations', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>The choice-free constructive companion to ZP-L. The snap-from-below is rebuilt '
            'syntactically on ordinal notations (ONote), never touching Mathlib&#8217;s '
            'choice-saturated Ordinal type; the three snap results are choice-free &#8212; [propext] '
            'only &#8212; in contrast to every &#949;<sub>0</sub> result in ZP-L, which carries '
            'Classical.choice. Proved sorry-free in Lean 4 (ConstructiveOrdinals.lean).</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'ZP-L derived the snap at &#949;<sub>0</sub>, but every &#949;<sub>0</sub> result in its Lean '
        'development carries Classical.choice &#8212; inherited from Mathlib&#8217;s Ordinal type, '
        'which is choice-saturated. ZP-N asks whether that choice is intrinsic to the snap or merely '
        'representational. The answer is representational. The snap&#8217;s downward structure &#8212; '
        'the &#969;-tower climbs without bound, and no ordinal notation is a fixed point of '
        'x &#8614; &#969;<sup>x</sup> &#8212; is genuinely constructive, provable with no Axiom of '
        'Choice.'))
    E.append(body(
        'The move is to work at the level of ordinal <i>notations</i> (ONote, Cantor-normal-form '
        'terms), whose comparison ONote.cmp is choice-free (propext-only) and never passes through '
        'repr into the semantic Ordinal type. &#949;<sub>0</sub> is not itself a notation: the '
        'notations name exactly the ordinals below &#949;<sub>0</sub>, and &#949;<sub>0</sub> is their '
        'limit &#8212; the fixed point the notation system cannot reach. So the snap threshold is '
        'characterised <i>from below</i>: the tower ascends, and the fixed point (&#949;<sub>0</sub>) '
        'is precisely what lies beyond every notation. This layer adds no axiom; it isolates where '
        'choice actually enters the ordinal snap.'))
    E.append(hr())

    # ── Section I: The Syntactic Substrate ────────────────────────────────────────
    print('[build_zpn] Building Section I...')
    E += [
        Paragraph('Section I: The Syntactic Substrate', S['h1']),
        hr(),
    ]

    E.append(body(
        'The Cantor normal form gives each ordinal below &#949;<sub>0</sub> a finite syntactic name. '
        'At the notation level, &#969;<sup>x</sup> is simply the term oadd x 1 0 (leading exponent x, '
        'coefficient 1, empty remainder) &#8212; no general ordinal exponentiation is needed. The '
        '&#969;-tower is built by iterating it. Comparison of notations is the purely syntactic '
        'ONote.cmp, which returns lt / eq / gt by structural recursion and never evaluates repr, so it '
        'is choice-free.'))

    E.append(def_box(
        'Definitions (ConstructiveOrdinals.lean)',
        [
            'omegaPow x = oadd x 1 0 &#8212; the notation for &#969;<sup>x</sup>; purely syntactic and '
            'computable.',
            'tower 0 = 0,  tower (n+1) = omegaPow (tower n) &#8212; the &#969;-tower '
            '(&#969;<sup>&#183;</sup>)<sup>[n]</sup> 0, constructive.',
            'ONote.cmp &#8212; the syntactic three-way comparison on notations (lt / eq / gt); '
            'choice-free (it does not touch repr / Ordinal).',
        ]
    ))
    E.append(sp(6))

    # ── Section II: The Choice-Free Snap from Below ───────────────────────────────
    print('[build_zpn] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Choice-Free Snap from Below', S['h1']),
        hr(),
    ]

    E.append(result_box(
        'Lemma: exp_lt_term (ConstructiveOrdinals.lean)',
        [
            'For every notation e, coefficient n, and remainder a: cmp e (oadd e n a) = lt.',
            'An exponent is strictly below its own term. Proof: structural induction on the exponent, '
            'pure syntax &#8212; no repr, no Ordinal.',
            'Lean purity: [propext] only &#8212; choice-free, and free even of Quot.sound. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: omegaPow_no_fixedpoint (ConstructiveOrdinals.lean)',
        [
            'For every notation x: cmp x (omegaPow x) = lt.',
            'No ordinal notation is a fixed point of x &#8614; &#969;<sup>x</sup>: every notation is '
            'strictly below its own &#969;-power, in the choice-free syntactic comparison (holds for '
            'all notations, well-formed or not). This is the constructive shadow of &#8220;'
            '&#949;<sub>0</sub> is the least fixed point of x &#8614; &#969;<sup>x</sup>, lying beyond '
            'every notation.&#8221;',
            'Lean purity: [propext] only &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: tower_strictMono (ConstructiveOrdinals.lean)',
        [
            'For every n: cmp (tower n) (tower (n+1)) = lt.',
            'The &#969;-tower is strictly increasing: the snap stages climb without bound below '
            '&#949;<sub>0</sub>. Immediate from omegaPow_no_fixedpoint applied at tower n.',
            'Lean purity: [propext] only &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The snap from below is choice-free. All three results depend on [propext] alone &#8212; not '
        'Classical.choice, and not even Quot.sound. The ascent of the &#969;-tower and the absence of '
        'any notation fixed point are proved by pure structural recursion on the syntax. This is the '
        'sharpest form of the framework&#8217;s choice-free-core pattern (see '
        'ZeroParadox/AxiomProfile.lean): the '
        'snap&#8217;s downward structure needs nothing beyond propositional extensionality.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── Section III: The Finding and Its Fences ───────────────────────────────────
    print('[build_zpn] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Finding and Its Fences', S['h1']),
        hr(),
    ]

    E.append(body(
        'The point of ZP-N is the contrast with ZP-L. There, every &#949;<sub>0</sub> result carries '
        'Classical.choice; here, the same downward structure is proved with [propext] only. The '
        'difference is entirely the substrate: ZP-L works in Mathlib&#8217;s Ordinal type, which is '
        'choice-saturated, while ZP-N works in ONote, which is not. So the Classical.choice in '
        'ZP-L&#8217;s snap is <b>representational, not intrinsic</b>: it is inherited from the '
        'semantic representation, and vanishes once the same fact is stated syntactically. Choice '
        'enters the ordinal snap only at the syntax&#8594;semantics bridge, not in the snap itself.'))

    E.append(remark_box(
        'Remark: even well-formedness inherits choice (the bridge, made visible)',
        [
            'tower_NF &#8212; the statement that each tower stage is in normal form &#8212; DOES carry '
            'Classical.choice ([propext, Classical.choice, Quot.sound]), because Mathlib&#8217;s NF '
            'predicate is defined through repr into Ordinal. The snap facts (Section II) do not depend '
            'on NF, so they stay choice-free; but the fact that even &#8220;this notation is '
            'well-formed&#8221; inherits choice pins the location precisely: choice lives at the '
            'syntax&#8594;semantics bridge, exactly where ZP-L crosses it and ZP-N does not.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Scope fence: the snap from below, not minimality',
        [
            'ZP-N proves the snap <i>from below</i>: &#949;<sub>0</sub> is the fixed point unreachable '
            'from within the notation system (no notation is a fixed point of '
            'x &#8614; &#969;<sup>x</sup>; the tower climbs without bound). The matching '
            '<i>minimality</i> &#8212; that &#949;<sub>0</sub> is the LEAST fixed point of '
            'x &#8614; &#969;<sup>x</sup> &#8212; is a separate, harder target: it quantifies over the '
            'limit, which no notation names, so it cannot be stated purely syntactically on ONote. '
            'That direction remains open; what is proved here is the from-below half, choice-free.',
        ]
    ))
    E.append(sp(6))

    # ── Theorem Summary ───────────────────────────────────────────────────────────
    print('[build_zpn] Building theorem table...')
    E += [
        hr(),
        Paragraph('Theorem Summary', S['h1']),
        hr(),
    ]

    E.append(data_table(
        headers=['Result', 'Lean source (full path)', 'Axioms'],
        rows_data=[
            ['exp_lt_term', 'ZeroParadox/Ordinal/ConstructiveOrdinals.lean', 'propext only'],
            ['omegaPow_no_fixedpoint', 'ZeroParadox/Ordinal/ConstructiveOrdinals.lean', 'propext only'],
            ['tower_strictMono', 'ZeroParadox/Ordinal/ConstructiveOrdinals.lean', 'propext only'],
            ['tower_NF', 'ZeroParadox/Ordinal/ConstructiveOrdinals.lean', 'Classical.choice'],
        ],
        col_widths=[TW * 0.34, TW * 0.46, TW * 0.20],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'The snap from below (exp_lt_term, omegaPow_no_fixedpoint, tower_strictMono): [propext] '
            'only &#8212; choice-free, and free even of Quot.sound. Proved by structural recursion on '
            'ONote; repr / Ordinal are never touched.',
            'Well-formedness (tower_NF): [propext, Classical.choice, Quot.sound] &#8212; Classical.choice '
            'inherited from Mathlib&#8217;s NF / repr, which passes through the Ordinal type.',
            'This localises the Classical.choice in ZP-L&#8217;s &#949;<sub>0</sub> results to the '
            'syntax&#8594;semantics bridge: the snap itself is constructive. Zero sorry. Verified: '
            'lake build, July 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-N | The Constructive Snap | the snap from below on ordinal notations, '
            'choice-free ([propext] only): exp_lt_term, omegaPow_no_fixedpoint, tower_strictMono | '
            'ZP-L&#8217;s &#949;<sub>0</sub> choice is representational, not intrinsic | tower_NF '
            'carries choice, at the syntax&#8594;semantics bridge | minimality (&#949;<sub>0</sub> the '
            'least fixed point) open.</i>',
            S['endnote']),
    ]

    print('[build_zpn] Building document...')
    doc.build(E)
    print(f'[build_zpn] Done: {out_path}')


if __name__ == '__main__':
    build()
