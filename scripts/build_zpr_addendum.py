"""
Zero Paradox — ZP-R Addendum: The Diagonal Family — PDF Builder
Version 1.12 | October 2026
Follows scripts/PDF_Rendering_Standards.md.
Search record behind § IV's Gödel-first sentence (2026-10-06, ripgrep over ZeroParadox/**/*.lean):
  (a) godel_?(one|1|first)|first_?incompleteness|incompleteness_?(one|1|first)|godel_?sentence|true_?but_?unprovable  -> 0 hits
  (b) (theorem|lemma|def)\\s+\\S*(godel|gödel|incomplet)  -> only godel_two (ZeroParadox/Settheory/Loeb.lean)
  (c) ↔\\s*¬\\s*\\(?\\s*(□|prov|Prov|provable)  -> 0 hits
"""

import os
from zp_utils import *

VERSION = '1.12'
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
            '<i>Addendum to ZP-R. ZP-R treats the framework\'s self-application fixed point as a role '
            'filled per face: in the fork / AFA face by &#8869; of the ZPSemilattice (the order-bottom), '
            'in the computability face by a Kleene code, a term of another type; it locates the '
            'face where the role is filled by a Lawvere fixed point. In this addendum, "at &#8869;" and "tied to '
            '&#8869;" refer to that role, not to one object. The addendum maps the faces formalized here, '
            'organized by the '
            '&#956;/&#957; fork &#8212; the <b>wall</b> faces where self-reference cannot close (no fixed '
            'point) and the <b>floor</b> faces where it does (a fixed point exists). Every entry except '
            'the G&#246;del-first row carries a machine-checked Lean 4 witness. The diagonal-family unification is '
            'Lawvere (1969) / Yanofsky (2003), cited; the contribution is the formalization '
            'and the tie to the self-application role (the engine, the wall faces, and the Quine-atom '
            'and L&#246;b / G&#246;del-2 floor faces choice-free; the computability floor faces choice-carrying). It supersedes the earlier private "Zero as a Wall" '
            'working draft.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'The diagonal arguments of Cantor, Russell, G&#246;del and Tarski are special cases of one '
        'theorem, <b>Lawvere\'s fixed-point theorem</b> (Lawvere 1969, whose introduction names exactly '
        'those four). Yanofsky (2003) carries the same scheme to the halting problem and to Kleene\'s '
        'recursion theorem, with Rice\'s theorem as an application. ZP-R asks where the framework\'s '
        'self-application role is filled by an instance of that fixed point, and finds one face: the '
        'computability face, where the occupant is a Kleene code, a term of another type than '
        '&#8869; of the ZPSemilattice. This addendum lays out the faces formalized here in one place, '
        'each with its Lean witness where one exists.'))
    E.append(body(
        'The organizing principle is the &#956;/&#957; fork (ZP-R &#167;I; ZP-P). The engine is '
        'negation, which has no fixed point, and Lawvere\'s theorem, with Yanofsky\'s extensions, turns '
        'that one fact into the wall faces. One direction is proved about the fork\'s two regimes: a '
        'self-loop rules out well-foundedness (mu_nu_branch_exclusion). The <b>wall</b> (&#956;) faces '
        'are Cantor, Russell, Turing, Tarski and Curry; the <b>floor</b> (&#957;) faces are the Quine '
        'atom, the Kleene quine, the L&#246;b sentence, and (with a twist) Rice. '
        'Most of the engine and the classical faces are already formalized in the framework\'s Wall '
        'module; this addendum adds the four faces formalized in the diagonal-family build (Tarski, '
        'Curry, Rice, L&#246;b).'))
    E.append(hr())

    # -- Section I: The Engine --------------------------------------------------------
    print('[build_zpr_addendum] Building Section I...')
    E += [
        Paragraph('Section I: The Engine', S['h1']),
        hr(),
    ]

    E.append(body(
        'The root of the wall faces is one fact: <b>negation has no fixed point.</b> No proposition p '
        'satisfies p &#8596; &#172;p. Lawvere\'s theorem is the amplifier: a point-surjection e : A '
        '&#8594; (A &#8594; B) forces every f : B &#8594; B to have a fixed point, so a fixed-point-free '
        'f (negation) refutes the surjection. Every wall face below is this contrapositive.'))

    E.append(result_box(
        'The engine (Wall.lean)',
        [
            'negation_no_fixedpoint: &#172; (p &#8596; &#172; p) &#8212; negation is fixed-point-free '
            '(the root).',
            'lawvere_fixedpoint: a point-surjection A &#8594; (A &#8594; B) forces every f : B &#8594; B '
            'to have a fixed point (Lawvere 1969, the general engine).',
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
        '(wf_no_selfloop). Under Foundation this is "no set is self-membered."'))

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
            'Placement is by witness, not by phenomenon: no_self_decider is the Cantor-over-Bool '
            'skeleton of the halting argument and sits on the wall. The halting problem as an '
            'undecidability fact (halting_undecidable, Rice.lean) is an instance of Rice\'s theorem '
            'and sits with the Rice face in Section III.',
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
        'At each floor face a fixed point is supplied, and the supplier differs by face. In the fork / '
        'AFA face it is &#8869; of the ZPSemilattice, by the class fields (a commitment, not engine '
        'output). In the computability face it is a Kleene code (Rogers\' fixed point). In the L&#246;b '
        'face it is given by a hypothesized L&#246;b diagonal.'))

    E.append(result_box(
        'The Quine atom (SetTheoryAFA.lean) &#8212; the set-theoretic floor',
        [
            '&#8869; = {&#8869;}: the self-containing &#8869; of the ZPSemilattice. t_exec / T-EXEC '
            '(t_exec_iff): every Quine atom equals &#8869; of the ZPSemilattice (IsQuineAtom q &#8596; '
            'q = &#8869;), derived from the ZPSemilattice / AFAStructure class fields &#8212; location '
            'and uniqueness of the floor in this face. Lives in ZF + AFA (walled off under Foundation, '
            'Section II).',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'The Kleene quine (Lawvere.lean) &#8212; the computability floor',
        [
            'computability_face_fixedPoint: every computable self-map on codes has a fixed point '
            '<i>up to eval</i> &#8212; two codes computing the same function, not a literal one &#8212; '
            'Rogers\' form of the recursion theorem (Mathlib fixed_point), on the reflexive object of the '
            'computable category (the crossing realized in ZP-R). A program that prints its own code '
            'takes one further s-m-n step, not in this declaration. The fixed point is machine-checked '
            'here; that it is an instance of Lawvere\'s theorem is cited: Yanofsky (2003), Theorem 5, '
            'and Bauer (2017), Theorem 5.2 and Corollary 5.3, a version of Lawvere\'s theorem for '
            'multi-valued maps, in synthetic computability.',
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
        'Rice (Rice.lean) &#8212; a fixed point beside an undecidable property',
        [
            'quine_exists_yet_rice is a conjunction: for computable f, a fixed point of f up to eval '
            'EXISTS (recursion theorem), AND membership in any non-trivial extensional set C of codes '
            'is UNDECIDABLE (rice_face, which cites Mathlib\'s ComputablePred.rice&#8322;, Rice\'s '
            'theorem in its form over program codes; Rice 1953 states it for classes of recursively '
            'enumerable sets). The undecidability is of C '
            'over all codes; the second conjunct does not mention f, so nothing is stated about '
            'membership at f\'s fixed point. The standard recursion-theorem proof of Rice\'s theorem '
            '(Yanofsky 2003, p. 19; Mathlib\'s ComputablePred.rice, via fixed_point&#8322;) turns on the '
            'fixed point of a different map, built from the assumed decider for C. Rice\'s 1953 proof '
            'takes another route: his undecidability result, the Corollary B that follows his Theorem '
            '6, rests on his Theorems 4 and 6, and Theorem 6 reduces from Theorem 5, that the unit '
            'class of the empty set is not completely recursively enumerable. rice_face_has_bottom states '
            'the first conjunct alone; reading that fixed point as the face\'s floor is the family\'s '
            'criterion, not the theorem.',
            'halting_undecidable: whether a program halts on input n is not decidable, the concrete '
            'Rice instance (Mathlib\'s halting_problem, proved by rice).',
            'Reading: the pivot face. The fixed point is not refuted (as on the wall) but present '
            '(&#957;), and undecidability sits beside it; no theorem here makes one depend on the other.',
            'Lean purity: [propext, Classical.choice, Quot.sound] &#8212; Mathlib recursion theory. ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section IV: The Formalized Faces ---------------------------------------------
    print('[build_zpr_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: The Formalized Faces', S['h1']),
        hr(),
    ]

    E.append(body(
        'The faces formalized here, in one table. G&#246;del\'s first incompleteness (G &#8596; '
        '&#172;Prov(G)) sits between the columns and is not formalized here: a first-incompleteness '
        'declaration was not located as of 2026-10-06 (searched ZeroParadox/**/*.lean for '
        'first-incompleteness and G&#246;del-sentence declarations, by name and by statement shape), '
        'and lawvere_fixedpoint says nothing about provability. Every row except the G&#246;del-first row is a machine-checked Lean witness.'))

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
             'not formalized here'],
            ['Quine atom', '&#957;', '&#8869; = {&#8869;}: &#8869; of a ZPSemilattice, in the Quine-atom role',
             't_exec / t_exec_iff (SetTheoryAFA.lean)'],
            ['Kleene quine', '&#957;', 'every computable self-map on codes has a fixed point up to eval',
             'computability_face_fixedPoint (Lawvere.lean)'],
            ['L&#246;b / G&#246;del 2nd', '&#957;', 'the provability diagonal closes; consistency unprovable',
             'loeb, godel_two (Loeb.lean)'],
            ['Rice', '&#957;', 'a fixed point exists; every non-trivial semantic property is '
             'undecidable over all codes',
             'rice_face_has_bottom, quine_exists_yet_rice, halting_undecidable (Rice.lean)'],
        ],
        col_widths=[TW * 0.16, TW * 0.10, TW * 0.34, TW * 0.40],
    ))
    E.append(sp(6))

    E.append(callout(
        'The map is a placement, not a new theorem. The unification of the diagonal family is Lawvere '
        '(1969) and Yanofsky (2003); each face is a classical result (each wall face a direct instance '
        'of the engine), formalized here axiom-free where the logic is pure and choice-carrying where it '
        'inherits Mathlib\'s recursion theory. What the framework adds is the tie to the '
        'self-application role, for the faces formalized here.',
        bg=BLUE_LITE, border=BLUE
    ))
    E.append(sp(6))

    E.append(def_box(
        'Fence: the cross-face identity is a type boundary',
        [
            'The faces are the same <i>relationship</i>, not the same <i>object</i>. The Quine atom (a '
            'set), the Kleene quine (a code), the L&#246;b sentence &#8212; these are terms of different '
            'types in different categories; "x = y" across them is not false, it is not well-formed '
            '(ZP-P hard fence; ZP-R F2). What is claimed is that each face formalized here forks at its '
            'own self-referential contact point, and that the self-application fixed point is a '
            '<i>role</i> filled per face by that face\'s own occupant: in the fork / AFA face, &#8869; of '
            'the ZPSemilattice, by the AbstractSelfApp class fields fixed_bot and unique_fp (a commitment; '
            'Lawvere\'s premise is false in any ZPSemilattice with an element other than &#8869;, '
            'nontrivial_lattice_no_witness, which unlike t_exec carries Classical.choice); in the '
            'computability face, a Kleene '
            'code, a fixed point up to eval (that it is a Lawvere instance is cited, Rogers\' form); in '
            'the L&#246;b face, the sentence a hypothesized L&#246;b diagonal supplies. On the wall faces '
            'the role has no occupant. No occupant is identified with another. How the wall, fork / AFA '
            'and computability faces relate to Lawvere\'s theorem is collected in ZP-R, Section III, '
            'in the box "Lawvere\'s theorem, face by face"; ZP-R conjectures nothing global.',
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
        'Cartesian Closed Categories," LNM 92 (1969) 134&#8211;145, read in its reprint, Reprints in '
        'Theory and Applications of Categories 15 (2006); and Yanofsky, "A Universal Approach to '
        'Self-Referential Paradoxes, Incompleteness and Fixed Points," Bull. Symbolic Logic 9(3) (2003), '
        'read as arXiv:math/0305282v1. Lawvere\'s paper treats Cantor, Russell, Tarski\'s '
        'undefinability of truth and an incompleteness theorem; Yanofsky adds, among others, Turing\'s '
        'halting problem, the recursion theorem (his Theorem 5) and Rice\'s theorem. Bauer, "On '
        'fixed-point theorems in synthetic computability," Tbilisi Math. J. 10(3) (2017), proves a '
        'version of Lawvere\'s theorem for multi-valued maps, in synthetic computability, and derives '
        'the Kleene&#8211;Rogers recursion theorem from it (Theorem 5.2, Corollary 5.3). The '
        'individual faces are classical: Cantor; Russell (1901); G&#246;del (1931); Turing\'s halting '
        'problem; Tarski (1936); Curry (1942); L&#246;b (1955); Kleene\'s recursion theorem; and '
        'Rice, "Classes of recursively enumerable sets and their decision problems," Trans. Amer. '
        'Math. Soc. 74(2) (1953) 358&#8211;366. The '
        'point-surjective theorem is in Mathlib (Function.exists_fixed_point_of_surjective); the '
        'framework\'s engine re-derives it axiom-free for a self-contained family. The contribution of '
        'this addendum is the formalization of the faces formalized here (the engine, the wall faces, and the Quine-atom and '
        'L&#246;b / G&#246;del-2 floor faces choice-free; the computability floor faces choice-carrying) and its tie to the self-application role &#8212; a placement, not an extension.'))

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
            'the Quine-atom and L&#246;b / G&#246;del-2 floor faces (t_exec; L&#246;b, godel_two) are choice-free &#8212; the '
            'faces listed here need no Axiom of Choice.',
            'The computability floor faces (Kleene: computability_face_fixedPoint; Rice: '
            'rice_face_has_bottom, quine_exists_yet_rice, halting_undecidable) carry [propext, '
            'Classical.choice, Quot.sound], '
            'inherited from Mathlib\'s classical recursion theory &#8212; disclosed, not claimed '
            'otherwise.',
            'Core choice-free, computability realization choice-carrying &#8212; the framework\'s '
            'standing pattern. Zero sorry. Verified: lake build, October 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-R Addendum | The Diagonal Family | wall faces &#956; (Cantor, Russell, '
            'Turing, Tarski, Curry), each the contrapositive of one engine (negation has no fixed '
            'point) | floor faces &#957; (Quine atom, Kleene, L&#246;b / G&#246;del 2, Rice), each '
            'fixed point supplied per face | the faces formalized here, Lean-witnessed '
            'except G&#246;del 1st | cross-face identity a type boundary | the map is a placement, not a new '
            'theorem.</i>',
            S['endnote']),
    ]

    print('[build_zpr_addendum] Building document...')
    doc.build(E)
    print(f'[build_zpr_addendum] Done: {out_path} ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
