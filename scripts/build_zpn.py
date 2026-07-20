"""
Zero Paradox — ZP-N: The Constructive Snap PDF Builder
Version 2.0 | July 2026

v2.0: Major revision. Corrects v1.0's mechanism and adds the construction it was missing.

v1.0 claimed ZP-L's Classical.choice at ε₀ was "representational, not intrinsic," on the grounds that
Mathlib's Ordinal type is "choice-saturated." That justification is false as measured — #print axioms
Ordinal reports [propext, Quot.sound], no choice in the type — and the conclusion overreached its
evidence: everything v1.0 proved choice-free is a fact about the ASCENT, while ε₀ is past what the
notation system can name (tower_cofinal). The claim was also not measurable by the instrument used:
Classical.choice sits in the Ordinal.partialOrder INSTANCE TERM, so every statement mentioning that
order inherits it however proved (order_footprint_le vs order_footprint_eq).

v2.0 says something sharper and true. The ascent is constructive (unchanged from v1.0, and still the
layer's genuine content). The classical dependency in the ε₀ results comes from Mathlib's order
instance and operations, which are genuinely non-constructive — comparability of arbitrary well-orders
implies excluded middle (em_of_wellOrder_comparable; the taboo is Kraus / Nordvall Forsberg / Xu,
arXiv:2104.02549 Thm 38(d), cited not claimed) — and genuinely more than ε₀ needs. And here is a
carrier sized to the job: E0Note = WithTop ONote, whose crossing into Ordinal is one named map with a
measured price (PricedInterface.lean; carrier choice-free, crossing carries choice at every decl).
Construction credited to Castéran & Contejean (hydra-battles ON_plus / ON_correct).

Lean: ConstructiveOrdinals.lean, SnapNucleusConstructive.lean, OrdinalChoiceEssential.lean,
PricedInterface.lean. Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '2.0'
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
            '<i>The constructive companion to ZP-L. The snap-from-below is rebuilt syntactically on '
            'ordinal notations (ONote), where it is choice-free &#8212; [propext] only. Beside it: a '
            'carrier sized to &#949;<sub>0</sub> whose crossing into Mathlib&#8217;s Ordinal is one '
            'named map with a measured price, and a proof that the generality ZP-L borrows is '
            'genuinely non-constructive. Proved sorry-free in Lean 4.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'ZP-L derived the snap at &#949;<sub>0</sub>, and every &#949;<sub>0</sub> result in its Lean '
        'development carries Classical.choice. ZP-N asks where that choice actually lives and whether '
        'the snap needs it. Two answers, and they point in opposite directions. The snap&#8217;s '
        'downward structure &#8212; the &#969;-tower climbs without bound, and no ordinal notation is '
        'a fixed point of x &#8614; &#969;<sup>x</sup> &#8212; is genuinely constructive, provable '
        'with no Axiom of Choice. But the machinery ZP-L reaches for to state that structure '
        'semantically is not: comparing arbitrary well-orders implies excluded middle. The choice is '
        'neither an artifact nor intrinsic to the snap. It is the price of a tool stronger than the '
        'job requires.'))
    E.append(body(
        'So this layer does two things. It rebuilds the ascent syntactically, where it is choice-free. '
        'And it builds a carrier sized to &#949;<sub>0</sub> &#8212; ordinal notations with one point '
        'adjoined on top &#8212; where the crossing into Mathlib&#8217;s semantic ordinals is a single '
        'named map whose cost can be read off directly. Staying on the notation side is free of choice; '
        'crossing is not; and the crossing is one function rather than a diffuse dependency.'))
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
        'Classical.choice; here, the same downward structure is proved with [propext] only. It is '
        'tempting to conclude that the choice is therefore an artifact of representation. It is not, '
        'and the reason is worth stating precisely, because the natural diagnosis is wrong twice over.'))
    E.append(body(
        'First, the choice is not in the type. #print axioms Ordinal reports [propext, Quot.sound]. It '
        'is in the <i>order instance</i> and the operations built on it &#8212; Ordinal.partialOrder, '
        'instLinearOrder, typein, omega0, nfp, deriv, epsilon. Second, and consequently, an axiom '
        'footprint on any &#949;<sub>0</sub> result measures that ambient instance rather than the '
        'proof: a &#8804; a carries Classical.choice while a = a does not, for the same element, '
        'differing only in whether the statement mentions the order (order_footprint_le, '
        'order_footprint_eq). The instrument cannot answer the question it was being asked.'))
    E.append(body(
        'What it can answer is a different question: is that instance&#8217;s classical content real? '
        'It is. Merely knowing, of any two well-orders, that one of them embeds in the other &#8212; '
        'without being handed which &#8212; already yields excluded middle (em_of_wellOrder_comparable, '
        'itself choice-free: the classical content is the hypothesis, not the proof). The hypothesis is '
        'a bare disjunction, not a procedure that computes the answer, which makes the implication '
        'sharper than it first sounds; it is also the form Mathlib&#8217;s le_total actually takes. '
        'This is a known taboo in constructive mathematics, not a result of this framework: it is '
        'Theorem 38(d) of Kraus, Nordvall Forsberg and Xu, stated there in the data form, and their '
        'witnesses are the ones used here. So the generality Mathlib&#8217;s order provides &#8212; '
        'comparing '
        '<i>any</i> two well-orders &#8212; genuinely requires the classical assumption. '
        '&#949;<sub>0</sub> never needed that generality.'))

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

    E.append(body(
        'That diagnosis suggests its own remedy: build a carrier sized to the job. E0Note is ordinal '
        'notations with a single point adjoined on top, that point standing for &#949;<sub>0</sub>. '
        'Below the top, comparison is the existing syntactic comparator and stays decidable; the map '
        'e0Repr sends the carrier into Mathlib&#8217;s Ordinal. Measured, the boundary is priced: the '
        'carrier side carries no Classical.choice anywhere, and the map carries it at every '
        'declaration. Staying constructive is free; crossing costs the classical assumption; and the '
        'crossing is one named function.'))

    E.append(def_box(
        'Scope fences on the carrier &#8212; what it is and is not',
        [
            'The fixed point at the top is <b>stipulated, not discovered</b>. Defining the tower '
            'operator to fix the adjoined point makes the closure exist by fiat at the added point; '
            'only its uniqueness is a theorem. This does not weaken no_snap_closure, which says no '
            'such closure exists on the notations alone.',
            'E0Note is a notation system for <b>&#949;<sub>0</sub> + 1</b>, not for &#949;<sub>0</sub>. '
            'The standard alternative is a Veblen system where &#949;<sub>0</sub> is an ordinary term; '
            'the top&#8217;s honest advantage is that it is minimal and leaves the comparator untouched.',
            'Correctness in Cast&#233;ran&#8217;s sense (ON_correct) is <b>not</b> claimed: on raw '
            'notations the representation map is not injective, which e0Repr_not_injective proves. '
            'Restricting to normal forms is the standard repair and is not done here, because that '
            'predicate is itself defined through the representation map.',
            'The construction is <b>not new</b>. The carrier is Cast&#233;ran and Contejean&#8217;s '
            'generic sum of notation systems (hydra-battles, ON_plus) instantiated with a one-point '
            'right summand, and the map is an instance of their ON_correct, already instantiated at '
            '&#949;<sub>0</sub>. What is contributed here is the measurement.',
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
            ['tower_cofinal', 'ZeroParadox/Ordinal/SnapNucleusConstructive.lean', 'propext only'],
            ['no_snap_closure', 'ZeroParadox/Ordinal/SnapNucleusConstructive.lean', 'propext only'],
            ['em_of_wellOrder_comparable', 'ZeroParadox/Ordinal/OrdinalChoiceEssential.lean',
             'propext, Quot.sound'],
            ['order_footprint_eq', 'ZeroParadox/Ordinal/OrdinalChoiceEssential.lean',
             'propext, Quot.sound'],
            ['order_footprint_le', 'ZeroParadox/Ordinal/OrdinalChoiceEssential.lean',
             'Classical.choice'],
            ['E0Note (carrier)', 'ZeroParadox/Ordinal/PricedInterface.lean', 'no axioms'],
            ['e0Repr (the crossing)', 'ZeroParadox/Ordinal/PricedInterface.lean', 'Classical.choice'],
            ['e0Repr_not_injective', 'ZeroParadox/Ordinal/PricedInterface.lean', 'Classical.choice'],
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
            'The taboo (em_of_wellOrder_comparable): [propext, Quot.sound] &#8212; choice-free by '
            'design, because the classical content is the hypothesis rather than the proof. Its '
            'converse (comparable_of_classical) carries Classical.choice, as it must.',
            'The carrier (E0Note, e0Coe): no axioms at all; its decidable-order instances '
            '[propext, Quot.sound]. The crossing (e0Repr and every lemma about it): '
            '[propext, Classical.choice, Quot.sound]. The carrier side carries no choice anywhere.',
            'Together these locate the Classical.choice in ZP-L&#8217;s &#949;<sub>0</sub> results: it '
            'is not in the Ordinal type, and not in the snap, but in the order instance the semantic '
            'statement passes through &#8212; where it is load-bearing rather than removable. Zero '
            'sorry. Verified: lake build, July 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-N | The Constructive Snap | the snap from below on ordinal notations, '
            'choice-free ([propext] only): exp_lt_term, omegaPow_no_fixedpoint, tower_strictMono | '
            'the classical dependency is in Mathlib&#8217;s order instance, where comparing arbitrary '
            'well-orders implies excluded middle (taboo cited to Kraus, Nordvall Forsberg and Xu) | '
            'a carrier sized to &#949;<sub>0</sub>, with the crossing priced at one named map | '
            'minimality (&#949;<sub>0</sub> the least fixed point) open.</i>',
            S['endnote']),
    ]

    print('[build_zpn] Building document...')
    doc.build(E)
    print(f'[build_zpn] Done: {out_path}')


if __name__ == '__main__':
    build()
