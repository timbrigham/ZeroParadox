"""
Zero Paradox — ZP-R Addendum: The Diagonal Family — PDF Builder
Version 1.0 | July 2026
v1.0: Initial release. Addendum to ZP-R. The COMPLETE roster of the self-referential / diagonal
relationship at the bottom element ⊥, organized by the μ/ν fork: wall faces (self-reference cannot
close — no fixed point) and floor faces (self-reference closes — a fixed point exists). Supersedes the
private "Zero as a Wall" working draft (ZP-W, never public). Every variant is tied to ⊥ and carries a
machine-checked Lean 4 witness. The diagonal-family unification is Lawvere (1969) / Yanofsky (2003),
cited; the delta is the axiom-free formalization and the tie to ⊥. Follows scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.0'
FIRST_RELEASED = 'July 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-R_Diagonal_Family_Addendum.pdf')
    print(f'[build_zpr_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-R Addendum: The Diagonal Family',
                   'ZP-R Addendum: The Diagonal Family', 'Version ' + VERSION)
    E = []

    print('[build_zpr_addendum] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-R Addendum: The Diagonal Family', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Addendum to ZP-R. Where ZP-R locates and realizes the framework\'s self-application '
            'fixed point &#8869; as a Lawvere fixed point, this addendum maps the <b>complete family</b> '
            'of that relationship: every variant of self-reference at &#8869;, organized by the '
            '&#956;/&#957; fork &#8212; the <b>wall</b> faces where self-reference cannot close (no fixed '
            'point) and the <b>floor</b> faces where it does (a fixed point exists). Every entry is tied '
            'to &#8869; and carries a machine-checked Lean 4 witness. The diagonal-family unification is '
            'Lawvere (1969) / Yanofsky (2003), cited; the contribution is the axiom-free formalization '
            'and the tie to the bottom element. It supersedes the earlier private "Zero as a Wall" '
            'working draft.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'The self-referential paradoxes &#8212; Cantor, Russell, G&#246;del, Turing, Tarski &#8212; are '
        'one theorem seen from many sides: <b>Lawvere\'s fixed-point theorem</b> (Lawvere 1969), unified '
        'by Yanofsky (2003). ZP-R identifies the framework\'s bottom element &#8869; as an instance of '
        'that fixed point and locates where it is realized. This addendum takes the next step and lays '
        'out the whole family in one place, each variant with its Lean witness, so the framework can say '
        'plainly: <i>every variant of the self-referential relationship at &#8869; is accounted for.</i>'))
    E.append(body(
        'The organizing principle is a single discriminator, the &#956;/&#957; fork (ZP-R &#167;I; ZP-P): '
        'the engine is negation, which has no fixed point, and Lawvere\'s theorem turns that one fact '
        'into the whole family. Where the self-reference relation is <b>well-founded</b>, no self-loop '
        'exists &#8212; the <b>wall</b> (&#956;): Cantor, Russell, Turing, Tarski, Curry. Where it is '
        '<b>non-well-founded</b>, a self-referential fixed point exists &#8212; the <b>floor</b> '
        '(&#957;): the Quine atom, the Kleene quine, the L&#246;b sentence, and (with a twist) Rice. '
        'Most of the engine and the classical faces are already formalized in the framework\'s Wall '
        'module; this addendum completes the roster with the four faces added in the diagonal-family '
        'build (Tarski, Curry, Rice, L&#246;b) and ties every entry to &#8869;.'))
    E.append(hr())

    # -- Section I: The Engine --------------------------------------------------------
    print('[build_zpr_addendum] Building Section I...')
    E += [
        Paragraph('Section I: The Engine', S['h1']),
        hr(),
    ]

    E.append(body(
        'The root of the entire family is one fact: <b>negation has no fixed point.</b> No proposition p '
        'satisfies p &#8596; &#172;p. Lawvere\'s theorem is the amplifier: a point-surjection e : A '
        '&#8594; (A &#8594; B) forces every f : B &#8594; B to have a fixed point, so a fixed-point-free '
        'f (negation) refutes the surjection. Every wall face below is this contrapositive; every floor '
        'face is the same engine where the refutation is lifted (the relation is non-well-founded, or '
        'the diagonal is not constructible, so the fixed point returns).'))

    E.append(result_box(
        'The engine (Wall.lean)',
        [
            'negation_no_fixedpoint: &#172; (p &#8596; &#172; p) &#8212; negation is fixed-point-free '
            '(the root).',
            'lawvere_fixedpoint: a point-surjection A &#8594; (A &#8594; B) forces every f : B &#8594; B '
            'to have a fixed point (Lawvere 1969, the general engine).',
            'The &#956;/&#957; fork is exactly its two regimes: &#956; = no fixed point (the wall); '
            '&#957; = a fixed point exists (the self-referential object).',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section II: The Wall Faces (mu) ----------------------------------------------
    print('[build_zpr_addendum] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Wall Faces (&#956;) &#8212; self-reference cannot close', S['h1']),
        hr(),
    ]

    E.append(body(
        'On a well-founded relation there is no self-loop: no x with x pointing at itself '
        '(wf_no_selfloop). Under Foundation this is "no set is self-membered." Each wall face is the '
        'same obstruction in its own domain &#8212; self-reference tries to close and cannot, and the '
        'failure is the bottom element refusing to be internalized.'))

    E.append(result_box(
        'The wall, general (Wall.lean)',
        [
            'wf_no_selfloop: a well-founded relation admits no self-loop &#8212; the object-level core '
            'the metatheoretic boundary reduces to. no_quine_atom: under Foundation, no set is '
            'self-membered.',
            'Lean purity: wf_no_selfloop choice-free; no_quine_atom [propext, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Cantor / Russell / Turing (Wall.lean) &#8212; the classical wall faces',
        [
            'Cantor (cantor_via_engine): no g : A &#8594; (A &#8594; Prop) is surjective &#8212; no '
            'self-surjection onto predicates.',
            'Russell (russell_via_engine): no membership relation realizes every predicate (naive '
            'comprehension is impossible).',
            'Turing (no_self_decider): no g : A &#8594; (A &#8594; Bool) is surjective &#8212; the '
            'halting diagonal flips the decider.',
            'Lean purity: choice-free (all three, off the engine). ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Tarski (Tarski.lean) &#8212; the truth face',
        [
            'tarski_no_internal_truth: no internal universal truth-naming exists &#8212; truth is not '
            'definable inside a system that can name all its own predicates (Tarski 1936). The liar '
            'sentence (tarski_liar_from_naming) is the explicit diagonal; the T-schema at the liar is '
            'absurd (tarski_Tschema_liar_absurd).',
            'The bottom relationship: no floor &#8212; tarski_no_truth_bottom (&#172; HasLawvereWitness '
            'Prop). Truth is the wall dual of G&#246;del\'s provability.',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Curry (Curry.lean) &#8212; the explosion face',
        [
            'curry_paradox: a self-referential p &#8596; (p &#8594; C) proves C, for ANY C &#8212; a '
            'strict generalization of the engine (the liar is the C = False case, '
            'liar_is_curry_at_false). curry_from_naming: a surjective internal comprehension proves '
            'everything.',
            'The bottom relationship: no floor, and pretending otherwise explodes &#8212; curry_no_bottom '
            '(&#172; Surjective naming, via explosion at C = False).',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section III: The Floor Faces (nu) --------------------------------------------
    print('[build_zpr_addendum] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Floor Faces (&#957;) &#8212; self-reference closes', S['h1']),
        hr(),
    ]

    E.append(body(
        'Where the self-reference relation is non-well-founded, or the fixed-point-free diagonal is not '
        'constructible, the fixed point returns: self-reference closes on a bottom element. These are '
        'the &#957; faces &#8212; the framework\'s keystone, seen in each domain.'))

    E.append(result_box(
        'The Quine atom (SetTheoryAFA.lean) &#8212; the set-theoretic floor',
        [
            '&#8869; = {&#8869;}: the self-containing bottom. t_exec / T-EXEC (t_exec_iff): every Quine '
            'atom IS &#8869; (IsQuineAtom q &#8596; q = &#8869;) &#8212; location and uniqueness of the '
            'floor. Lives in ZF + AFA (walled off under Foundation, Section II).',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'The Kleene quine (SelfApp.lean / Lawvere.lean) &#8212; the computability floor',
        [
            'computability_face_fixedPoint: every computable self-map on codes has a fixed point &#8212; '
            'Kleene\'s recursion theorem, the reflexive object of the computable category (the crossing '
            'realized in ZP-R). This is the one face where the fixed point is genuinely Lawvere-sourced.',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; Mathlib recursion theory. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'L&#246;b (Loeb.lean) &#8212; the provability floor; and G&#246;del\'s second incompleteness',
        [
            'loeb: given a L&#246;b diagonal (&#968; &#8596; (&#9633;&#968; &#8594; A)), &#8866; '
            '&#9633;A &#8594; A yields &#8866; A. The L&#246;b sentence is a genuine fixed point '
            '(loeb_sentence_is_fixedpoint) &#8212; the provability face has a floor.',
            'godel_two: a consistent system cannot prove &#9633;&#8869; &#8594; &#8869; &#8212; its own '
            'consistency (G&#246;del\'s second incompleteness, the A = &#8869; corollary). Built from '
            'scratch (no modal logic in Mathlib): an abstract ProvabilityLogic typeclass with the '
            'Hilbert&#8211;Bernays&#8211;L&#246;b derivability conditions.',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Rice (Rice.lean) &#8212; the exists-but-undecidable floor',
        [
            'The floor exists but membership at it is undecidable. quine_exists_yet_rice: the Kleene '
            'quine EXISTS (recursion theorem) yet every non-trivial semantic property is UNDECIDABLE '
            '(rice_face; Rice 1953, cited from Mathlib). rice_face_has_bottom: the recursion-theorem '
            'fixed point is the computability bottom.',
            'This is the pivot face: the fixed point is not refuted (as on the wall) but present '
            '(&#957;) &#8212; the failure migrates from existence to decidability.',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; Mathlib recursion theory. ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section IV: The Complete Map -------------------------------------------------
    print('[build_zpr_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: The Complete Map', S['h1']),
        hr(),
    ]

    E.append(body(
        'The whole family in one table. G&#246;del\'s first incompleteness (G &#8596; &#172;Prov(G)) '
        'sits between the columns &#8212; the diagonal via the engine, incompleteness rather than '
        'inconsistency. Every row is a machine-checked Lean witness tied to &#8869;.'))

    E.append(data_table(
        headers=['Variant', 'Face', 'What self-reference does', 'Lean witness'],
        rows_data=[
            ['the engine', '&#8212;', 'negation has no fixed point (the root)',
             'negation_no_fixedpoint, lawvere_fixedpoint (Wall.lean)'],
            ['Cantor', '&#956;', 'no self-surjection onto predicates',
             'cantor_via_engine (Wall.lean)'],
            ['Russell', '&#956;', 'no membership realizes every predicate',
             'russell_via_engine (Wall.lean)'],
            ['Turing', '&#956;', 'the halting decider is flipped',
             'no_self_decider (Wall.lean)'],
            ['Tarski', '&#956;', 'truth is not internally definable',
             'tarski_no_internal_truth (Tarski.lean)'],
            ['Curry', '&#956;', 'self-reference proves everything (explosion)',
             'curry_paradox, curry_no_bottom (Curry.lean)'],
            ['G&#246;del 1st', 'between', 'self-reference is true-but-unprovable',
             'via lawvere_fixedpoint (Wall.lean)'],
            ['Quine atom', '&#957;', '&#8869; = {&#8869;}: self-containing bottom',
             't_exec / t_exec_iff (SetTheoryAFA.lean)'],
            ['Kleene quine', '&#957;', 'a program computes its own code',
             'computability_face_fixedPoint (Lawvere.lean)'],
            ['L&#246;b / G&#246;del 2nd', '&#957;', 'the provability diagonal closes; consistency unprovable',
             'loeb, godel_two (Loeb.lean)'],
            ['Rice', '&#957;', 'the floor exists but is undecidable',
             'rice_face_has_bottom, quine_exists_yet_rice (Rice.lean)'],
        ],
        col_widths=[TW * 0.16, TW * 0.10, TW * 0.34, TW * 0.40],
    ))
    E.append(sp(6))

    E.append(callout(
        'The map is a placement, not a new theorem. The unification of the diagonal family is Lawvere '
        '(1969) and Yanofsky (2003); each face is a classical result (or a direct instance of the '
        'engine), formalized here axiom-free where the logic is pure and choice-carrying where it '
        'inherits Mathlib\'s recursion theory. What the framework adds is the tie to &#8869; and the '
        'completeness of the roster &#8212; every variant of the one relationship, in one place.',
        bg=BLUE_LITE, border=BLUE
    ))
    E.append(sp(6))

    E.append(def_box(
        'Fence: the cross-face identity is a type boundary',
        [
            'The faces are the same <i>relationship</i>, not the same <i>object</i>. The Quine atom (a '
            'set), the Kleene quine (a code), the L&#246;b sentence, the 2-adic 0 &#8212; these are terms '
            'of different types in different categories; "x = y" across them is not false, it is not '
            'well-formed (ZP-P hard fence; ZP-R F2). What is claimed is that each domain forks at its own '
            'self-referential contact point, and that &#8869; is the framework\'s name for that point in '
            'each. The global identification &#8212; that these are one object &#8212; is held as a '
            'fenced conjecture, here as in ZP-R and ZP-P.',
        ]
    ))
    E.append(sp(6))

    # -- Prior work + Axiom purity ----------------------------------------------------
    E += [
        hr(),
        Paragraph('Relation to Prior Work', S['h1']),
        hr(),
    ]

    E.append(body(
        'The diagonal-family unification via one fixed-point theorem is Lawvere, "Diagonal Arguments and '
        'Cartesian Closed Categories," LNM 92 (1969), and Yanofsky, "A Universal Approach to '
        'Self-Referential Paradoxes, Incompleteness and Fixed Points," Bull. Symbolic Logic 9(3) (2003). '
        'The individual faces are classical: Cantor; Russell (1901); G&#246;del (1931); Turing (1936); '
        'Tarski (1936); Curry (1942); L&#246;b (1955); Rice (1953); Kleene\'s recursion theorem. The '
        'point-surjective theorem is in Mathlib (Function.exists_fixed_point_of_surjective); the '
        'framework\'s engine re-derives it axiom-free for a self-contained family. The contribution of '
        'this addendum is the axiom-free formalization of the family and its tie to the bottom element '
        '&#8212; a placement, not an extension.'))

    E += [
        hr(),
        Paragraph('Axiom Purity', S['h1']),
        hr(),
    ]

    E.append(axiom_box(
        'Axiom Purity',
        [
            'The engine and the wall faces (negation_no_fixedpoint, lawvere_fixedpoint, '
            'cantor_via_engine, russell_via_engine, no_self_decider, wf_no_selfloop, Tarski, Curry) and '
            'the pure-logic floor (Quine atom t_exec; L&#246;b, godel_two) are choice-free &#8212; the '
            'diagonal family needs no Axiom of Choice.',
            'The computability floor faces (Kleene: computability_face_fixedPoint; Rice: '
            'rice_face_has_bottom, quine_exists_yet_rice) carry [propext, Classical.choice, Quot.sound], '
            'inherited from Mathlib\'s classical recursion theory &#8212; disclosed, not claimed '
            'otherwise.',
            'Core choice-free, computability realization choice-carrying &#8212; the framework\'s '
            'standing pattern. Zero sorry. Verified: lake build, July 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-R Addendum | The Diagonal Family | one engine (negation has no fixed point) | '
            'wall faces &#956; (Cantor, Russell, Turing, Tarski, Curry) | floor faces &#957; (Quine '
            'atom, Kleene, L&#246;b / G&#246;del 2, Rice) | every variant tied to &#8869; and '
            'Lean-witnessed | cross-face identity a type boundary | the map is a placement, not a new '
            'theorem.</i>',
            S['endnote']),
    ]

    print('[build_zpr_addendum] Building document...')
    doc.build(E)
    print(f'[build_zpr_addendum] Done: {out_path} ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
