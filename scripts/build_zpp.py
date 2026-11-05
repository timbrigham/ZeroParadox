"""
Zero Paradox — ZP-P: The Fixed-Point Fork PDF Builder
Version 1.36 | November 2026
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.36'
FIRST_RELEASED = 'June 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-P_The_Fixed_Point_Fork.pdf')
    print(f'[build_zpp] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-P: The Fixed-Point Fork',
                   'ZP-P: The Fixed-Point Fork', 'Version ' + VERSION)
    E = []

    print('[build_zpp] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-P: The Fixed-Point Fork', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Synthesis layer. The abstract fork schema is proved sorry-free and choice-free in '
            'Lean 4 (FixedPointFork.lean); the number-system instance via Ostrowski (Ostrowski.lean) and '
            'the categorical-parent instance via QPF.Fix / QPF.Cofix (Coalgebra.lean) are '
            'Lean-witnessed; the set-theory and computation instances are referenced to ZP-J and '
            'ZP-K. Generalizes the ZFC+Foundation / ZFC+AFA orthogonal-contact-point claim.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'A <b>monotone</b> self-map of a complete lattice has a least fixed point and a '
        'greatest fixed point (Knaster&#8211;Tarski); monotonicity is required. Whether the '
        'framework&#8217;s own self-referential operators instantiate that schema is <i>not</i> '
        'claimed here &#8212; see the fences in Section III. ZP-P records a single elementary '
        'fact and '
        'develops its consequences across the framework: these two fixed points coincide &#8212; '
        'the fork <i>collapses</i> to one point &#8212; exactly when the operator has a unique '
        'fixed point. Read intuitively, the least fixed point is the inductive (well-founded) '
        'closure and the greatest is the coinductive (non-well-founded) closure; the collapse '
        'point is where the two closures meet. In the Zero Paradox that point is the diagonal '
        'fixed point, filled by &#8869; of the state semilattice in the Quine-atom role (CC-2), the '
        'role of a point that steps to itself and to nothing else, occupied chart by chart: under a '
        'self-application map that fixes &#8869; and nothing else it is the only occupant '
        '(selfApp_quine_role_iff); in Mathlib\'s ZFSet no set occupies the role '
        '(zfset_quine_role_unoccupied).'))
    E.append(body(
        'This layer is a synthesis layer, not a foundational one: it adds no axiom or primitive. '
        'It names a pattern that several existing layers already realise, and it is organised in '
        'three tiers held to three different standards of proof. Tier 1 (Section I) is the '
        'abstract schema, proved in Lean over a complete lattice. Tier 2 (Section II) is the '
        'instance catalogue: each framework forks at its own contact point, and the instances are '
        'theorems in their home layers. Tier 3 (Section III) is the unification, stated as a role '
        'rather than an identity: one role, defined once, against which each chart either has an '
        'occupant or provably has none, and no equation across charts is claimed. The fences in Section III are load-bearing: keeping the tiers separate is '
        'what makes the formal content honest.'))
    E.append(hr())

    # ── Section I: The Fork Schema (Tier 1) ───────────────────────────────────────
    print('[build_zpp] Building Section I...')
    E += [
        Paragraph('Section I: The Fork Schema (Tier 1)', S['h1']),
        hr(),
    ]

    E.append(body(
        'Over a complete lattice, a monotone self-map f has a least fixed point (lfp f) and a '
        'greatest fixed point (gfp f), and lfp f &#8804; gfp f always. The width between them is '
        'the fork. The schema theorem states that the fork collapses to a single point precisely '
        'when f has a unique fixed point &#8212; and in that case the common value is that fixed '
        'point. The proofs rest only on Mathlib\'s order-theoretic fixed-point API '
        '(OrderHom.lfp / OrderHom.gfp); they make no claim about the categorical '
        'inductive/coinductive reading, which is offered as analogy only.'))

    E.append(def_box(
        'Definition: the fork (FixedPointFork.lean)',
        [
            'For a complete lattice &#945; and a monotone self-map f : &#945; &#8594; &#945;:',
            '  lfp f = the least fixed point of f   (Mathlib OrderHom.lfp)',
            '  gfp f = the greatest fixed point of f  (Mathlib OrderHom.gfp)',
            'The fork is the ordered pair (lfp f, gfp f), always satisfying lfp f &#8804; gfp f.',
            'Collapse = lfp f = gfp f: the two ends meet at a single contact point.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Proposition: fork_le (FixedPointFork.lean)',
        [
            'lfp f &#8804; gfp f',
            'The inductive closure never exceeds the coinductive closure: the fork has '
            'non-negative width. (Mathlib OrderHom.lfp_le_gfp.)',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: collapse_of_unique (FixedPointFork.lean)',
        [
            'If x is the unique fixed point of f, then lfp f = x and gfp f = x.',
            'Both ends of the fork land on the sole fixed point.',
            'Proof: lfp f and gfp f are fixed points (map_lfp, map_gfp); uniqueness sends each to x.',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: unique_of_collapse (FixedPointFork.lean)',
        [
            'If lfp f = gfp f, then every fixed point of f equals that common value.',
            'Every fixed point lies between lfp f and gfp f, so collapse forces uniqueness.',
            'Proof: lfp_le_fixed and le_gfp bracket any fixed point y; antisymmetry closes it.',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: fork_collapse_iff (FixedPointFork.lean) &#8212; the schema spine',
        [
            'lfp f = gfp f  &#8596;  &#8707;! x, f x = x',
            'The fork collapses to a single contact point if and only if f has a unique '
            'fixed point.',
            'This is the abstract form of "the framework forks, and the diagonal fixed point '
            'is where the two closures meet."',
            'Proof: collapse_of_unique and unique_of_collapse, both directions.',
            'Lean purity: [propext, Quot.sound] &#8212; choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The fork spine is choice-free. All four results depend only on [propext, Quot.sound] '
        '&#8212; propositional extensionality and quotient soundness, two of Lean\'s standard axioms, '
        'used throughout Mathlib. None depends on the Axiom of Choice. This is consistent with '
        'the choice-free core (see ZeroParadox/AxiomProfile.lean): the conceptual skeleton needs no '
        'choice; choice enters mostly in the analytic realisations (that file\'s &#167; III) &#8212; '
        'not only there, since the framework also carries bare classicals of its own; '
        'ZeroParadox/Category/ChoiceCannotBe.lean &#167; IV collects cases among '
        'them whose principles reduce to a taboo, with those reductions.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── Section II: The Instance Catalogue (Tier 2) ───────────────────────────────
    print('[build_zpp] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Instance Catalogue (Tier 2)', S['h1']),
        hr(),
    ]

    E.append(body(
        'The same fork appears across frameworks. ZP-P does not re-prove each instance &#8212; '
        'each is a theorem in its home layer &#8212; it records the catalogue and pins the '
        'number-system instance to a checkable Lean witness. The original ZFC+Foundation / '
        'ZFC+AFA orthogonal-contact-point claim is the set-theory entry: in the standard '
        'category-theoretic characterisation (Aczel; Lambek), Foundation is the initial algebra '
        '(&#956;) and AFA the final coalgebra (&#957;) of the bounded powerset functor, and the '
        'Quine atom (CC-2), a set equal to its own singleton, x = {x}, is exactly an element present in '
        '&#957; but not in &#956;. No equation identifies it with &#8869; of a ZPSemilattice; the two are '
        'measured against the Quine-atom role of Section III.'))

    E.append(data_table(
        headers=['Domain', 'The two closures fork into', 'Contact point / home layer'],
        rows_data=[
            ['Set theory',
             'Foundation (&#956;, well-founded) vs AFA (&#957;, non-well-founded)',
             'Quine atom (CC-2), x = {x}; ZP-J / ZP-K'],
            ['Number systems',
             'Archimedean &#8477; vs non-Archimedean &#8474;<sub>p</sub>',
             '0: in &#8477; no first step above it (AX-B1\'s form); &#8474;<sub>2</sub> removes the '
             'topological obstruction to an irreversible step (c3_irreversible) and supplies no first step; ZP-B / ZP-F'],
            ['Computation',
             'total (well-founded) vs partial (non-terminating)',
             'the Kleene quine / self-application; ZP-K'],
            ['Category theory',
             'initial algebra (W-types) vs final coalgebra (M-types)',
             'QPF.Fix vs QPF.Cofix; Coalgebra.lean'],
        ],
        col_widths=[TW * 0.20, TW * 0.42, TW * 0.38],
    ))
    E.append(sp(6))

    E.append(body(
        'The number-system instance is the one with a genuine classification theorem behind it. '
        'Ostrowski\'s theorem says the nontrivial absolute values on &#8474; are exactly the real '
        '(Archimedean) one and the p-adic (non-Archimedean) ones &#8212; the complete, '
        'pairwise-inequivalent list. The contact point is 0: in the Archimedean completion '
        '&#8477;, a densely ordered field, 0 has no first step above it, AX-B1\'s form '
        '(f_snap_impossible, which, despite its name, states that no linearly ordered field has a '
        'least positive element). In the 2-adic completion &#8474;<sub>2</sub>, 0 is the unique '
        'fixed point of x &#8614; 2x (q2_unique_fp) and the only point of infinite valuation '
        '(v<sub>2</sub>(0) = &#8734;, padic_addVal_eq_top_iff); &#8474;<sub>2</sub> is totally disconnected (padic_snaps, an instance Mathlib already supplies), '
        'which removes the topological obstruction to an irreversible step (c3_irreversible: no continuous '
        'path in &#8474;<sub>2</sub> from a nonzero point to 0) and supplies no first step: under the norm '
        'preorder 0 is least and has no first step (ZeroParadox/BottomCannotBe.lean &#167; ROLE), '
        'and on &#8484;<sub>2</sub>, the 2-adic integers, 0 is least in the norm preorder and '
        'greatest in the valuation order (z2_two_views). T-SNAP\'s shape needs no first step: '
        't_snap_given holds at a step taken in a densely ordered join-semilattice (&#8474;&#8805;0 under '
        'max, whose &#8869; is 0; ZeroParadox/Order/Snap.lean).'))

    E.append(result_box(
        'Theorem: completions_exhaustive (Ostrowski.lean)',
        [
            'Every nontrivial absolute value on &#8474; is equivalent to the real absolute '
            'value, or to a p-adic absolute value for a unique prime p.',
            'The two kinds of completion are the complete list. (Ostrowski\'s theorem, '
            'Mathlib Rat.AbsoluteValue.equiv_real_or_padic.)',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; choice-carrying. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: real_not_equiv_padic (Ostrowski.lean)',
        [
            'The real absolute value is inequivalent to every p-adic absolute value.',
            'The two kinds of completion are genuinely distinct &#8212; never the same metric. '
            'This is the orthogonality leg of the number-system fork. (Mathlib '
            'Rat.AbsoluteValue.not_real_isEquiv_padic.)',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; choice-carrying. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: choice-free spine, choice-carrying realisation',
        [
            'The fork spine (Section I) is choice-free [propext, Quot.sound]. The Ostrowski '
            'instance carries Classical.choice, inherited from Mathlib\'s classical analysis '
            'and number theory. This split is the framework\'s standing pattern: the conceptual '
            'core is choice-free, while the analytic realisations are choice-carrying.',
            'The number-system fork is theorem-backed on its own terms &#8212; Ostrowski is a '
            'genuine classification theorem, stronger backing than the metatheoretic '
            'Foundation/AFA orthogonality. It is NOT claimed to be an instance of the '
            '&#956;/&#957; (least-vs-greatest fixed point) schema: Ostrowski concerns absolute '
            'values, not fixed points of a functor. The thread to the diagonal fixed point runs '
            'through the contact point 0 (the unique fixed point of x &#8614; 2x in '
            '&#8474;<sub>2</sub>), not through the schema theorem.',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'The categorical instance is the genuine &#956;/&#957; case &#8212; the parent of the '
        'set-theory entry. On a one-shape, one-child polynomial functor (no leaf), the initial '
        'algebra (W-type, &#956;) is empty while the final coalgebra (M-type, &#957;) is inhabited '
        'by the infinite self-referential element: the non-well-founded closure contains a point '
        'the well-founded closure lacks &#8212; the categorical analog of the Quine atom present '
        'in &#957;F but not &#956;F.'))

    E.append(result_box(
        'Theorem: categorical_fork_strict (Coalgebra.lean)',
        [
            'IsEmpty (Fix idPF_Coalgebra.Obj) &#8743; Nonempty (Cofix idPF_Coalgebra.Obj)',
            'The initial algebra (least fixed point, &#956;) is empty; the final coalgebra '
            '(greatest fixed point, &#957;) is inhabited. (Mathlib QPF.Fix / QPF.Cofix.)',
            'Split footprint: fix_isEmpty (&#956; empty) is choice-free [propext, Quot.sound]; '
            'cofix_nonempty (&#957; inhabited) carries Classical.choice from the QPF '
            'corecursion machinery &#8212; a QUOTIENT-LAYER artifact: QPF.Cofix carries the '
            'choice in the TYPE. The M-type FORMER and constructors are axiom-free while the '
            'M-type DESTRUCTOR (M.children / M.dest) is not &#8212; that is where the axiom '
            'originates &#8212; and strict_cofix_nonempty proves the same inhabitation over '
            'the M-type with no axioms, by only building. For a polynomial functor the final '
            'coalgebra '
            'is constructible choice-free '
            '(Ahrens&#8211;Capriotti&#8211;Spadotti, TLCA 2015). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: where choice appears in the &#956;/&#957; fork',
        [
            'The Classical.choice in cofix_nonempty is a library dependency, not a fact about '
            'the mathematics, and it is worth locating exactly. Measured: the M-type former '
            'and its constructors are axiom-free (PFunctor.M, M.mk, M.corec), while its <i>destructor</i> '
            'carries the axiom (M.children, M.dest) &#8212; and QPF.Cofix inherits it in the '
            'type through the congruence it quotients by. That is why strict_cofix_nonempty '
            'is axiom-free: it only <i>builds</i>, and never destructs. '
            'For a polynomial functor the final coalgebra is '
            'constructible choice-free (Ahrens&#8211;Capriotti&#8211;Spadotti, TLCA 2015, who '
            'construct it as an &#969;-limit). Their ambient setting is intensional type theory '
            'with univalence, but the <i>construction</i> itself uses only function '
            'extensionality &#8212; univalence enters only for their uniqueness result.',
            'The <b>finite-powerset</b> functor is a different case &#8212; it is not polynomial, '
            'and the argument above does not cover it. It is also not this document\'s subject. '
            'The per-presentation detail there, with citations, is recorded in the Lean source '
            '(Coalgebra.lean) and is deliberately not restated here.',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'The remaining two instances are referenced, not re-proved here. The set-theory fork '
        '(Foundation vs AFA) has its Lean witness in ZP-J: quine_atom_unique proves that any two '
        'Quine atoms are equal &#8212; a uniqueness statement about self-MEMBERSHIP in the sense '
        'x = {x}, a set that is its own sole member. Bare self-membership is not unique under AFA: '
        '0* = {&#8709;, 0*} also contains itself (Aczel 1988, Example 1.5). That the '
        'bottom is one of them is a separate result (bot_is_quine_atom), and self-APPLICATION is '
        'a third (selfApp_pinnable, in the experimental Lawvere bridge rather than ZP-J proper). The computation fork '
        '(total vs partial) has its Lean witness in ZP-K: the Kleene quine. Each is the contact '
        'point of its own fork.'))
    E.append(sp(6))

    # ── Section III: The Unification and Its Fences (Tier 3) ──────────────────────
    print('[build_zpp] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Unification and Its Fences (Tier 3)', S['h1']),
        hr(),
    ]

    E.append(body(
        'The tempting claim is that the contact points of all the instances &#8212; the Quine '
        'atom, the 2-adic 0, the Kleene quine, the self-referential element of the final '
        'coalgebra &#8212; are faces '
        'of one object, the diagonal fixed point. ZP-P does not state that identity. It states '
        'what the contact points are measured against as a role, defined once in the corpus&#8217;s shared '
        'vocabulary of step relations (ZeroParadox/Die.lean, called the die; each carrier with its own '
        'step relation is a chart): '
        'the Quine-atom role, a point that steps to itself and to nothing else (Motion.SelfOnlyAt). '
        'Each chart either has an occupant or provably has none, and each is a theorem: the '
        'self-referential element of the final coalgebra occupies it (cofix_quine_role_occupied), '
        'no well-founded set does (zfset_quine_role_unoccupied), on the 2-adic integers 0 is the only '
        'occupant under doubling (z2_double_selfOnlyAt_iff), &#8869; is the only occupant '
        'under a self-application map on a semilattice, given as an AbstractSelfApp instance '
        '(selfApp_quine_role_iff), and on Kleene\'s codes, stepping from a code '
        'to the codes whose output is what a map assigns it, no single code '
        'occupies it while, for a computable map respecting equal output, some class of codes up to '
        'equal output does (codes_vs_classes). Under a function step, occupying the role is being a '
        'fixed point (Motion.selfOnlyAt_ofFun_iff), so the 2-adic and self-application rows restate '
        'their fixed points; the self-application row holds by the AbstractSelfApp class fields, so the '
        'constant map to &#8869; satisfies it too. The '
        'final-coalgebra chart has one point, so its occupancy restates its fork and adds nothing '
        'further. The fences are not hedging; they mark a genuine boundary, and per-instance '
        'forks remain full theorems on either side of them.'))

    E.append(def_box(
        'Hard fence (permanent): cross-instance identity is not a theorem',
        [
            'The claim "the contact points are one object" is not a theorem and cannot become '
            'one. Identity requires a shared type: the 2-adic 0, the Quine atom (a set), the '
            'Kleene quine (a code), and an element of a final coalgebra (an object up to '
            'isomorphism) are terms of different types in different categories. The proposition '
            '"x = y" across them is not false &#8212; it is not well-formed. So this is a type '
            'boundary, not a missing proof, and no such identity is committed to either. What '
            'relates the instances is the one role each chart is measured against. What is '
            'claimed formally is that each framework forks at its own contact point, and which '
            'charts have an occupant of the role.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'Soft fence (conjecture): not every fork is a &#956;/&#957; instance',
        [
            'That every domain fork is an instance of the least-vs-greatest fixed point schema '
            'is an open generalisation, not established here. The schema is a theorem in this '
            'layer and for canonical functors (W-types vs M-types). The number-system fork '
            '(Ostrowski) is the clear case that is theorem-backed yet NOT visibly a &#956;/&#957; '
            'instance &#8212; it is the live caution against overstating the generalisation.',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'Per-instance forks are theorems and are not hedged. The fences scope only the '
        'cross-instance identity (Tier 3) and the universal schema claim. Each individual fork '
        '&#8212; Foundation/AFA, &#8477;/&#8474;<sub>2</sub>, total/partial &#8212; stands on '
        'its own proof.',
        bg=BLUE_LITE, border=BLUE
    ))
    E.append(sp(6))

    # ── Theorem Summary ───────────────────────────────────────────────────────────
    # PageBreak, not a spacer: three gate rounds reported a widow -- the heading and all but the last
    # data row on p.5, `cofix_nonempty` alone on p.6 under a repeated header. Nudging the spacing
    # only moves which row is orphaned; starting the section on its own page removes the class.
    print('[build_zpp] Building theorem table...')
    E += [
        PageBreak(),
        Paragraph('Theorem Summary', S['h1']),
        hr(),
    ]

    E.append(data_table(
        headers=['Result', 'File / Section', 'Axioms'],
        rows_data=[
            ['fork_le', 'FixedPointFork.lean §I', 'choice-free'],
            ['collapse_of_unique', 'FixedPointFork.lean §I', 'choice-free'],
            ['unique_of_collapse', 'FixedPointFork.lean §I', 'choice-free'],
            ['fork_collapse_iff', 'FixedPointFork.lean §I', 'choice-free'],
            ['completions_exhaustive', 'Ostrowski.lean §II', 'Classical.choice'],
            ['real_not_equiv_padic', 'Ostrowski.lean §II', 'Classical.choice'],
            ['fix_isEmpty', 'Coalgebra.lean §II', 'choice-free'],
            ['cofix_nonempty', 'Coalgebra.lean §II', 'Classical.choice'],
        ],
        col_widths=[TW * 0.42, TW * 0.33, TW * 0.25],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Fork spine (FixedPointFork.lean): [propext, Quot.sound] &#8212; choice-free. The schema needs '
            'no Axiom of Choice.',
            'Number-system instance (Ostrowski.lean): [propext, Classical.choice, Quot.sound] '
            '&#8212; Classical.choice inherited from Mathlib\'s classical analysis / number '
            'theory (Ostrowski).',
            'Categorical instance (Coalgebra.lean): split &#8212; fix_isEmpty (&#956; empty) '
            'is choice-free [propext, Quot.sound]; cofix_nonempty (&#957; inhabited) carries '
            'Classical.choice from the QPF corecursion machinery (the quotient layer).',
            'Core choice-free, realisation choice-carrying &#8212; the framework\'s standing '
            'pattern.',
            'The footprints listed here are copies; the live record is the #print axioms output of '
            'each named .lean file.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-P | The Fixed-Point Fork | fork_collapse_iff (choice-free spine) | '
            'Ostrowski number-system instance | categorical &#956;/&#957; instance '
            '(Fix empty / Cofix inhabited) | hard fence: cross-instance identity is a type '
            'boundary; what relates the instances is one role, which a point of each chart occupies or provably none does | '
            'soft fence: not every fork '
            'is &#956;/&#957; | '
            'All FixedPointFork.lean / Ostrowski.lean / Coalgebra.lean theorems verified; the role '
            'occupancies of Section III are verified at the declarations Section III names.</i>',
            S['endnote']),
    ]

    print('[build_zpp] Building document...')
    doc.build(E)
    print(f'[build_zpp] Done: {out_path}')


if __name__ == '__main__':
    build()
