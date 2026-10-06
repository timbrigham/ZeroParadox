"""
Zero Paradox — ZP-R: A Cross-Category Account of the Self-Referential Fixed Point — PDF Builder
Version 1.13 | October 2026
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.13'
FIRST_RELEASED = 'July 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-R_Cross_Category_Fixed_Point.pdf')
    print(f'[build_zpr] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-R: A Cross-Category Account of the Self-Referential Fixed Point',
                   'ZP-R: A Cross-Category Account of the Self-Referential Fixed Point',
                   'Version ' + VERSION)
    E = []

    print('[build_zpr] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-R: A Cross-Category Account of the Self-Referential Fixed Point', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Synthesis / placement layer. The framework\'s self-application fixed point is a '
            '<b>role</b>, filled per face: in the fork / AFA face by &#8869; of the ZPSemilattice (the '
            'order-bottom, a fixed point and the only one by the class fields of AbstractSelfApp), in the '
            'computability face by a Kleene code, a term of another type. This document asks where the role is filled by a Lawvere fixed point, '
            'across three categories ("faces"): refuted in '
            '<b>Set</b> on every carrier except a one-element one (Cantor), obstruction-free with no reflexive object built here in the '
            '<b>monotone / domain</b> regime (Knaster&#8211;Tarski; a genuine reflexive object there '
            'needs Scott\'s D<sub>&#8734;</sub>), and realized in the <b>computability</b> face '
            '(Rogers / Kleene). Every theorem used is classical. Each result box (R1&#8211;R4) and each '
            'F1 property is backed by a machine-checked Lean 4 theorem, except one marked cited: that '
            'the computability fixed point is an instance of Lawvere\'s theorem. The rest is cited '
            'background or marked Reading. The contribution is the per-face placement of the '
            'framework\'s self-application role and the scope result. How the faces formalized here '
            'relate to Lawvere\'s theorem is collected in Section III, in the box "Lawvere\'s theorem, '
            'face by face"; ZP-R conjectures nothing global.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'A recurring role in this framework is a fixed point of self-application &#8212; '
        '"self-referential" in the sense of being defined by pointing at itself. Its occupants differ '
        'by face: a self-containing set (&#8869; of an AFA lattice, &#8869; = {&#8869;}) and a '
        'program equal to its own transform up to evaluation (a Kleene code). This document asks one checkable question: is a fixed point in that role an '
        'instance of <b>Lawvere\'s fixed-point theorem</b> (Lawvere 1969) &#8212; the '
        'categorical statement behind the diagonal arguments of Cantor, Russell, G&#246;del and Tarski, '
        'carried to the halting problem and the recursion theorem by Yanofsky (2003) &#8212; and if so, '
        'in which category? Lawvere states the theorem for cartesian closed categories (Theorem 1.1) '
        'and notes that it holds in any category with finite products (&#167;2, Theorem 2.2), with '
        'weak point-surjectivity phrased as a map A &#215; A &#8594; B that represents every map '
        'A &#8594; B. It yields a fixed point only where such a map exists (in the closed case, a '
        'weakly point-surjective A &#8594; B<sup>A</sup>; the reflexive case is B = A). So the honest '
        'form of the question is not "is it Lawvere" but "<b>where</b> is it Lawvere."'))
    E.append(body(
        'The answer is: <b>yes in one adequate category, and not globally.</b> We locate precisely '
        'where the realization fails and where it succeeds. The mathematics is classical and is invoked, not '
        'extended; the contribution is (i) the per-face placement of <i>this framework\'s own</i> '
        'self-application role relative to the Lawvere fixed point &#8212; its Lawvere realization '
        'refuted in Set on every carrier except a one-element one, the obstruction absent in the monotone / domain face with no reflexive object '
        'built there, the realization achieved in the computability face &#8212; and (ii) a '
        'scope result: the realization is category-relative &#8212; an existence statement in one face '
        'rather than a global identification. The general link between self-reference and Lawvere\'s '
        'theorem is Lawvere\'s (1969) and Yanofsky\'s (2003), not ours, and so is the obstruction the '
        'placement uses: that a fixed-point-free endomap rules out every point-surjection onto a '
        'function space is Lawvere\'s Corollary 1.2 (p. 5 of the 2006 TAC reprint). ZP-R does not '
        'address the suggestion of Soto-Andrade and Varela (1984), as Bj&#246;rner (1985) reports, that '
        'every structure with the fixed point property is a retract of a reflexive domain.'))
    E.append(hr())

    # -- Section I: The Fork and the Engine -------------------------------------------
    print('[build_zpr] Building Section I...')
    E += [
        Paragraph('Section I: The Fork and the Engine', S['h1']),
        hr(),
    ]

    E.append(body(
        'Begin in order theory, where the picture is cleanest and constructive. Over a complete '
        'lattice, a monotone self-map f has a least fixed point (lfp f) and a greatest fixed point '
        '(gfp f) &#8212; Knaster&#8211;Tarski (Tarski 1955). Existence of a fixed point is therefore '
        '<i>free</i>: it is never in question. What can vary is <i>uniqueness</i>, and there is a clean '
        'equivalence, the &#956;/&#957; <b>fork</b>: a specification pins a unique object exactly when '
        'the fork collapses. When the fork is open, the specification is met by more than one object; '
        'one can then only characterize, not single out. This is the order-theoretic form of a '
        'distinction the framework meets repeatedly &#8212; between an object and a property that '
        'characterizes it. It renames Knaster&#8211;Tarski; it is not a new theorem, and it is '
        'constructively choice-free.'))

    E.append(result_box(
        'R1 &#8212; the fork (fork_collapse_iff)',
        [
            'lfp f = gfp f  &#10234;  &#8707;! x, f x = x',
            'A monotone self-map on a complete lattice has a unique fixed point if and only if its '
            'fixed-point interval [lfp f, gfp f] collapses to a point.',
            'Witnesses: instance_pinnable_iff_fork_collapse (RequirementsGap.lean), '
            'instance_always_exists (MetaFork.lean).',
            'Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'Lawvere\'s theorem, in curried form, says: if a map e : A &#8594; (A &#8594; B) is '
        '<i>point-surjective</i> (every g : A &#8594; B equals e a for some a), then every f : B &#8594; '
        'B has a fixed point. The fixed point it produces has a specific shape &#8212; it is e a a, the '
        'value of e at a diagonal point applied to that same point: <b>self-application</b>. Reading: '
        'the framework\'s selfApp names this operation abstractly; no declaration connects Lawvere\'s e '
        'to selfApp.'))

    E.append(result_box(
        'R2a &#8212; Lawvere\'s engine yields its fixed point in the shape e a a',
        [
            'Given a surjection e : A &#8594; (A &#8594; B), every f : B &#8594; B has a fixed point of '
            'the form e a a &#8212; e applied to a diagonal point, at that same point. The statement '
            'mentions no ZPSemilattice, no selfApp and no &#8869;: it is a claim about shape only.',
            'Witness: lawvere_fixedpoint_selfApp (LawvereBridge.lean). Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'R2b &#8212; in the fork / AFA face, existence and uniqueness are class fields, not engine output',
        [
            'In the fork / AFA face, that &#8869; of the ZPSemilattice is a fixed point of selfApp is '
            'the class field fixed_bot of AbstractSelfApp, and that it is the only one is the class '
            'field unique_fp. Both are commitments of the class; neither is supplied by Lawvere\'s '
            'engine. selfApp_pinnable packages the two fields as &#8707;! x, selfApp x = x.',
            'On a ZPSemilattice with two or more points, some map has a fixed point and not a unique '
            'one (existence_without_uniqueness). On a ZPSemilattice with a point '
            'other than &#8869;, the engine\'s hypothesis fails outright: no surjection A &#8594; '
            '(A &#8594; L) exists (nontrivial_lattice_no_witness).',
            'Witnesses: selfApp_pinnable, existence_without_uniqueness (LawvereBridge.lean); '
            'nontrivial_lattice_no_witness (Lawvere.lean). Lean purity: choice-free (selfApp_pinnable, '
            'existence_without_uniqueness). ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section II: Locating the Obstruction, and the Crossing -----------------------
    print('[build_zpr] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: Locating the Obstruction, and the Crossing', S['h1']),
        hr(),
    ]

    E.append(body(
        'To fill the self-application role with a Lawvere fixed point in a given face &#8212; to '
        'source the occupant from the engine rather than posit it &#8212; one needs Lawvere\'s '
        'hypothesis there: a weakly point-surjective map onto a function space (Theorem 1.1; the '
        'reflexive case is a map A &#8594; A<sup>A</sup>). Whether one exists is the entire question, '
        'and one condition rules it out cleanly: the '
        '<b>presence of a fixed-point-free endomap</b>.'))

    E.append(result_box(
        'R3-neg &#8212; in Set, no reflexive object on a carrier with a fixed-point-free endomap (Cantor); the obstruction is non-monotone',
        [
            'A point-surjection e : A &#8594; (A &#8594; B) would, by Lawvere, force <i>every</i> '
            'f : B &#8594; B to have a fixed point. For B two-valued, negation is fixed-point-free '
            '&#8212; a contradiction. This is Cantor\'s theorem, read as the contrapositive of '
            'Lawvere\'s own engine.',
            'The obstruction witness &#8212; negation &#8212; has a structural property worth '
            'isolating: it is <i>not monotone</i> (it reverses the order False &#8804; True). This is '
            'what separates the faces.',
            'Witnesses: reflexive_object_refuted, not_monotone_not (LawvereBridge.lean). Lean purity: '
            'choice-free. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'Absence of a fixed-point-free endomap is <i>necessary</i> for a reflexive object &#8212; it '
        'removes Lawvere\'s contradiction (his Corollary 1.2). Whether it is also sufficient depends on '
        'the face. In Set it is: a set with no fixed-point-free endomap has exactly one element and '
        'carries a surjection onto its endomaps, so it is a reflexive object. In the monotone face it '
        'is not: on the two-element chain false &#8804; true every monotone self-map has a fixed point '
        '(Knaster&#8211;Tarski), yet no map from its two points onto its monotone self-maps is '
        'surjective. Both statements are anonymous Lean examples in '
        'ZeroParadox/Settheory/LawvereBridge.lean. A weaker question, about retracts rather than '
        'reflexive objects, is the suggestion of Soto-Andrade and Varela (1984), as Bj&#246;rner (1985) '
        'reports, that every structure with the fixed point property is a retract of a reflexive '
        'domain; ZP-R does not address it. Two categories '
        'are free of the obstruction, and only one of '
        'them is shown here to furnish a reflexive object. The reasons are <i>not</i> the same, and the '
        'difference is the point: the monotone regime is free of it <i>literally</i> &#8212; on a '
        '<i>complete lattice</i>, Knaster&#8211;Tarski bans a fixed-point-free monotone endomap, and the '
        'completeness hypothesis is load-bearing, since Nat.succ is a monotone endomap with no fixed '
        'point at all, and by Davis (1955, Theorem 2, p. 313) a lattice on which every increasing function has a '
        'fixpoint is complete &#8212; while the computable regime is free of it only '
        '<i>up to eval</i> &#8212; literally fixed-point-free total computable endomaps do exist.'))

    E.append(result_box(
        'R3-pos (monotone / domain) &#8212; obstruction absent; no reflexive object built here',
        [
            'On a complete lattice every monotone self-map has least and greatest fixed points '
            '(Knaster&#8211;Tarski), so fixed-point-free monotone endomaps are structurally banned '
            '&#8212; the obstruction is absent. Existence is thereby guaranteed; uniqueness is not '
            '(the interval [lfp, gfp] need not collapse).',
            'No reflexive object is built in this face here: obtaining one in the '
            'order / domain world is the business of Scott\'s D<sub>&#8734;</sub> (Scott-continuous '
            'maps on a directed-complete order, by inverse limits) &#8212; a construction we do not '
            'carry out and do not need, since the computability face below already realizes the '
            'crossing. What this face provides here is the <i>fork</i>.',
            'Witness: monotone_regime_derives_pinned (LawvereBridge.lean). Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'R3-pos (computability) &#8212; the reflexive object is realized: the crossing',
        [
            'The category of numbered sets carries a canonical reflexive object: the universal '
            'machine. The evaluation map eval is point-surjective onto the partial computable functions '
            '&#8212; every partial computable function has an index (Rogers 1967). And Rogers\' fixed-point theorem '
            'gives every total computable endomap of codes a fixed point <i>up to eval</i> &#8212; two '
            'codes computing the same function.',
            'That is weaker than "no fixed-point-free endomap", and the strong form is false: '
            'c &#8614; pair(c, c) is total and computable and returns its own input for no c (stated '
            'in the Lean docstrings, not formalized as a declaration). The '
            'obstruction is absent at the level of <i>eval</i>, which is where the reflexive object '
            'lives &#8212; and the reason is that the effective category admits fewer <i>maps</i>, '
            'not that eval lands in a different type: no computable self-map on codes is '
            'eval-fixed-point-free, so the diagonal the Set refutation runs has no computable '
            'representative.',
            'So the reflexive structure is present and the self-referential fixed point exists there: '
            'in Rogers\' form, for computable g : Code &#8594; Code a code c with eval (g c) = eval c; '
            'and in Kleene\'s two-place form (the second recursion theorem), for partial computable F a '
            'code c with eval c = F c.',
            'Witnesses: eval_point_surjective, computable_fixedpoint_up_to_eval, '
            'selfref_fixedpoint_exists_computable (ComputableCrossing.lean). Lean purity: '
            'choice-carrying (Mathlib computability). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'That the recursion theorem, in Rogers\' form (a total computable h has an n with '
        '&#966;<sub>h(n)</sub> = &#966;<sub>n</sub>), is an instance of Lawvere\'s scheme is standard: '
        'the derivation is Yanofsky (2003) Theorem 5 (p. 18 of arXiv:math/0305282v1), within his '
        'unified treatment. Bauer (2017) proves a version of Lawvere\'s theorem for multi-valued maps, '
        'in synthetic computability, and derives the Kleene&#8211;Rogers theorem from it (Theorem 5.2, '
        'Corollary 5.3). The Lean here checks the classical fixed point and the point-surjectivity of '
        'eval; the Lawvere-form derivation is cited, and this is the citation the later sections point '
        'to. Lawvere (1969) supplies the engine and raises the recursive case as an open question '
        'rather than deriving it (his &#167;2, p. 9 of the 2006 TAC reprint); the '
        'reflexive structure of the computable category is the subject of the Turing-category / '
        'partial-combinatory-algebra literature (Cockett&#8211;Hofstra 2008; Longley 1995). Collecting the '
        'three faces:'))

    E.append(data_table(
        headers=['Face', 'Reflexive object', 'Mechanism', 'Status'],
        rows_data=[
            ['Set',
             'refuted on every carrier except a one-element one, the empty set included (a '
             'one-element set is reflexive)',
             'a fixed-point-free map (negation) blocks it &#8212; Cantor; the obstruction is '
             'non-monotone',
             'the wall'],
            ['Monotone / domain',
             'not furnished here (route: Scott D<sub>&#8734;</sub>, unbuilt)',
             'obstruction absent (Knaster&#8211;Tarski); existence via the fork, uniqueness = fork '
             'collapse',
             'fork story; no Lawvere realization built here'],
            ['Computability',
             'realized',
             'universal machine point-surjective; Rogers / Kleene',
             'crossed'],
        ],
        col_widths=[TW * 0.15, TW * 0.20, TW * 0.42, TW * 0.23],
    ))
    E.append(sp(6))

    E.append(result_box(
        'R4 &#8212; in the computability face, the self-application role is filled by a Lawvere fixed point (cited)',
        [
            'In the computability face the self-application fixed-point role is filled by a Kleene '
            'code, and that fixed point is a Lawvere fixed point (cited). The code is a term of another '
            'type than &#8869; of the ZPSemilattice. Existence is '
            'machine-checked in Rogers\' form, eval (g c) = eval c for computable g : Code &#8594; Code '
            '(computable_fixedpoint_up_to_eval), which is the form Yanofsky and Bauer state, and in the '
            'two-place form, eval c = F c for partial computable F (selfref_fixedpoint_exists_computable). '
            'That it is an instance of Lawvere\'s theorem is cited (Section II). Since Lawvere\'s theorem '
            'holds in any category with finite products (his &#167;2), nothing obliges the realization '
            'to be in Set or in a Scott domain.',
            'What is proved about the framework\'s two structural regimes is that a self-loop rules out '
            'well-foundedness (mu_nu_branch_exclusion).',
            'Witnesses: the computability fixed point is proved in R3-pos above '
            '(computable_fixedpoint_up_to_eval, selfref_fixedpoint_exists_computable, '
            'ComputableCrossing.lean; choice-carrying); mu_nu_branch_exclusion (LawvereBridge.lean; '
            'choice-free). ✓',
        ]
    ))
    E.append(sp(6))

    # -- Section III: Scope and Fences ------------------------------------------------
    print('[build_zpr] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: Scope and Fences', S['h1']),
        hr(),
    ]

    E.append(body(
        'The result is deliberately narrow, and its limits are structural &#8212; part of the '
        'statement rather than caveats to it. The sharpest way to state them is to track <i>which face '
        'carries which property</i>.'))

    E.append(def_box(
        'F1 &#8212; what is measured, per face',
        [
            '&#8226; <b>Set / fork face.</b> On a ZPSemilattice L with a point a &#8800; &#8869;, no '
            'surjection A &#8594; (A &#8594; L) exists (nontrivial_lattice_no_witness : a &#8800; '
            '&#8869; &#8594; &#172;HasLawvereWitness L). That &#8869; of the ZPSemilattice is the '
            'unique fixed point of selfApp follows from the class fields fixed_bot and unique_fp '
            '(selfApp_pinnable); every Quine atom equals it (t_exec, from the AFAStructure class '
            'fields).',
            '&#8226; <b>Computability face.</b> For computable g : Code &#8594; Code, some code c has '
            'eval (g c) = eval c (computable_fixedpoint_up_to_eval). For partial computable F, the '
            'codes c with eval c = F c form an infinite set (fixed_points_infinite). This does not '
            'exclude a selfApp on Code with a literally unique fixed point.',
            '&#8226; <b>Monotone / domain face.</b> No claim is made here.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'F2 &#8212; representation is not transfer; the self-application role carries its face',
        [
            'The crossing is face-local. That a Kleene code fills the self-application role as a '
            'Lawvere fixed point in the computability face does not make a Lawvere fixed point '
            'available in Set on the same carrier, which has two or more elements and where the same '
            'construction remains a contradiction (Cantor; '
            'reflexive_object_refuted). What does not transfer is the Lawvere realization, not '
            'definability: the least fixed point of a monotone map on a powerset lattice, for '
            'instance, is definable in ZFC.',
            'Reading: the framework treats the self-application fixed point as a role carried with its '
            'face, characterized rather than constructed as one global object. Its choice of a '
            'non-well-founded foundation (ZF + AFA rather than ZFC; Aczel 1988; Barwise &amp; Moss 1996) '
            'is a separate commitment, which this face-locality does not by itself require. A theorem stated for every suitable category can be '
            '<i>witnessed</i> in whichever category has Lawvere\'s hypothesis; the <i>occupant</i> it '
            'produces is defined only relative to that category.',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        '<b>Lawvere\'s theorem, face by face.</b><br/>'
        'The fences are not hedging. Each per-face result &#8212; the Set wall, the fork, the '
        'computability crossing &#8212; is a full theorem on its own side of them. '
        '<b>Lawvere\'s theorem is the translation key between the faces formalized here, not a '
        'mechanism each face instantiates:</b> each face is read against its one arrow, a '
        'point-surjection onto a function space implies that every endomap has a fixed point, and the '
        'faces differ in which way, if either, they run it. A <b>wall</b> face runs it by the '
        'contrapositive, which is Lawvere\'s own reading ("The famed &#8216;diagonal argument&#8217; '
        'is of course just the contrapositive of our theorem," p. 5 of the 2006 TAC reprint): a '
        'fixed-point-free endomap rules out every point-surjection (his Corollary 1.2), and Cantor is '
        'the two-valued case. In Set every carrier except a one-element one has such an endomap, the '
        'empty set included, where the identity is vacuously fixed-point-free; a one-element set has '
        'none and is the trivial forward case (Section II). The '
        '<b>computability</b> face runs it forward, up to eval: eval is point-surjective onto the '
        'partial computable functions, and every total computable endomap of codes has a fixed point '
        'up to eval (R3-pos); that this is a Lawvere instance is cited (Yanofsky 2003; Bauer 2017). In '
        'the <b>fork / AFA</b> face the self-application fixed point, &#8869; of the ZPSemilattice, is '
        'supplied by the class fields fixed_bot and unique_fp (selfApp_pinnable), not by the engine, '
        'whose hypothesis fails on every ZPSemilattice with an element other than &#8869; '
        '(nontrivial_lattice_no_witness). On every ZPSemilattice with an element other than &#8869;, '
        'that face\'s only link to the computability face is the KleeneStructure commitment: it '
        'nominates a code meeting a periodicity condition (one that constant codes also meet) as the '
        'computational witness of the bottom role, a commitment of the class and not a theorem '
        '(ZeroParadox/Computability/Kleene.lean &#167;II). On the one-element ZPSemilattice, as for '
        'the one-element set, the forward case holds trivially. The '
        '<b>monotone</b> face runs it in neither direction on the two-element chain: on a complete lattice no monotone '
        'endomap is fixed-point-free (Knaster&#8211;Tarski), so the contrapositive has no monotone '
        'input, and on the two-element chain no map onto the monotone endomaps is surjective (Section '
        'II). No occupant is identified with another: an equation between an element of a '
        'ZPSemilattice and a code is ill-typed (MC-1). ZP-R conjectures nothing global.',
        bg=BLUE_LITE, border=BLUE
    ))
    E.append(sp(6))

    # -- Relation to Prior Work -------------------------------------------------------
    print('[build_zpr] Building prior work...')
    E += [
        hr(),
        Paragraph('Relation to Prior Work', S['h1']),
        hr(),
    ]

    E.append(body(
        'The mathematics used here is classical and is invoked, not extended. Lawvere\'s fixed-point '
        'theorem and the unification of the diagonal arguments: Lawvere, "Diagonal Arguments and '
        'Cartesian Closed Categories," LNM 92 (1969) 134&#8211;145, cited by page in its reprint, '
        'Reprints in Theory and Applications of Categories 15 (2006); Yanofsky, Bull. Symbolic Logic '
        '9(3) (2003), cited by page in arXiv:math/0305282v1. '
        'Lattice fixed points: Tarski, "A lattice-theoretical fixpoint theorem and its applications," '
        'Pacific J. Math. 5(2) (1955) 285&#8211;309; Davis, "A characterization of complete lattices," '
        'Pacific J. Math. 5(2) (1955) 311&#8211;319. The computability fixed points: Rogers, <i>Theory of Recursive Functions and '
        'Effective Computability</i> (1967); Kleene\'s second recursion theorem; a version of '
        'Lawvere\'s theorem for multi-valued maps, in synthetic computability, from which the '
        'recursion theorem follows: Bauer, "On fixed-point theorems in synthetic computability," '
        'Tbilisi Math. J. 10(3) (2017). The reflexive '
        'structure of the computable category: Cockett &amp; Hofstra, "Introduction to Turing '
        'categories," Annals of Pure and Applied Logic 156 (2008) 183&#8211;209; Longley, <i>Realizability Toposes and Language Semantics</i>, PhD '
        'thesis, University of Edinburgh, 1995 (ECS-LFCS-95-332). '
        'Fixed points and reflexive domains: Soto-Andrade and Varela, "Self-reference and fixed '
        'points: a discussion and an extension of Lawvere\'s theorem," Acta Applicandae Mathematicae '
        '2(1) (1984) 1&#8211;19, doi:10.1007/BF01405490, which, as Bj&#246;rner reports, draws '
        'attention to the fact that a retract of a reflexive domain in a suitable category has the '
        'fixed point property and suggests the converse, that every structure with the fixed point '
        'property is such a retract; and Bj&#246;rner, "Reflexive domains and fixed points," Acta '
        'Applicandae Mathematicae 4(1) (1985) 99&#8211;100, doi:10.1007/BF02293493, which shows that if R '
        'is a retract of a reflexive domain then R<sup>R</sup> has the fixed point property. The '
        'apophatic, characterize-not-construct treatment of self-referential objects: Aczel, '
        '<i>Non-Well-Founded Sets</i> (1988); Barwise &amp; Moss, <i>Vicious Circles</i> (1996).'))
    E.append(body(
        'Against this, the contribution of ZP-R is not a theorem but a <i>placement</i>: the '
        'per-face placement of the framework\'s self-application role relative to the Lawvere fixed '
        'point (its Lawvere realization refuted in Set on every carrier except a one-element one, the '
        'obstruction absent in the monotone / domain '
        'face, the realization achieved in the computability face), and the scope result of Section '
        'III. That Kleene\'s recursion theorem is a Lawvere instance is due to the sources above, not '
        'to this document, and so is the obstruction the placement uses (Lawvere\'s Corollary 1.2). '
        'The retract question, as Bj&#246;rner reports Soto-Andrade and Varela\'s suggestion, sits '
        'beside the placement and is not addressed here.'))

    # -- What Remains Open ------------------------------------------------------------
    E += [
        hr(),
        Paragraph('What Remains Open', S['h1']),
        hr(),
    ]

    E.append(remark_box(
        'Open items',
        [
            'ZP-R holds <b>no global conjecture</b>: how the faces formalized here relate to '
            'Lawvere\'s theorem is collected in Section III, in the box "Lawvere\'s theorem, face by '
            'face".',
            'The <b>domain-face route</b> &#8212; a Scott D<sub>&#8734;</sub> reflexive object &#8212; '
            'is not carried out; the computability face suffices for the existence claim, so it is not '
            'needed, but it would be a second realization.',
            '<b>Location and uniqueness</b> (that selfApp\'s fixed point is &#8869; of the '
            'ZPSemilattice, and unique) are '
            'established &#8212; in the fork / AFA face, from class fields (fixed_bot; unique_fp) &#8212; '
            'not open.',
        ]
    ))
    E.append(sp(6))

    # -- Machine-checked backing ------------------------------------------------------
    print('[build_zpr] Building backing table...')
    E += [
        hr(),
        Paragraph('Machine-Checked Backing', S['h1']),
        hr(),
    ]

    E.append(body(
        'Each result box (R1&#8211;R4) and each F1 property is backed by a compiling Lean 4 (+ Mathlib) '
        'theorem, sorry-free, except the one marked cited: that the computability fixed point is an '
        'instance of Lawvere\'s theorem (Section II). F2\'s first mathematical sentence rests on '
        'reflexive_object_refuted (the R3-neg row), and its second, on the least fixed point of a '
        'monotone map, on Knaster&#8211;Tarski (Tarski 1955, cited); sentences marked Reading are interpretation and '
        'have no row. The order / '
        'fork material is constructively choice-free; the computability material inherits '
        'Classical.choice from Mathlib\'s computability library (Kleene\'s and Rogers\' theorems use '
        'it), which is disclosed and not claimed otherwise.'))

    E.append(data_table(
        headers=['Claim', 'Lean witness (file)'],
        rows_data=[
            ['R1 (the fork)',
             'instance_pinnable_iff_fork_collapse (ZeroParadox/Settheory/RequirementsGap.lean); '
             'instance_always_exists (ZeroParadox/Settheory/MetaFork.lean)'],
            ['R2a / R2b (the shape e a a; existence and uniqueness as class fields)',
             'lawvere_fixedpoint_selfApp, selfApp_pinnable, existence_without_uniqueness '
             '(ZeroParadox/Settheory/LawvereBridge.lean); nontrivial_lattice_no_witness '
             '(ZeroParadox/Category/Lawvere.lean)'],
            ['R3-neg (Set, every carrier except a one-element one: refuted; obstruction non-monotone)',
             'reflexive_object_refuted, not_monotone_not (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['R3-pos monotone',
             'monotone_regime_derives_pinned (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['R3-pos computability (the crossing)',
             'eval_point_surjective, computable_fixedpoint_up_to_eval, '
             'selfref_fixedpoint_exists_computable (ZeroParadox/Computability/ComputableCrossing.lean)'],
            ['R4 (a self-loop rules out well-foundedness)',
             'mu_nu_branch_exclusion (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['F1 location (fixed point = &#8869; of the ZPSemilattice)',
             't_exec, t_exec_iff (ZeroParadox/Settheory/SetTheoryAFA.lean)'],
            ['F1 uniqueness (&#8869; of the ZPSemilattice the only fixed point)',
             'quine_atom_unique (ZeroParadox/Settheory/SetTheoryAFA.lean); '
             'AbstractSelfApp.unique_fp (ZeroParadox/Computability/SelfApp.lean)'],
            ['F1 computability face (infinitely many eval-fixed points of F)',
             'fixed_points_infinite (ZeroParadox/Computability/Kleene.lean)'],
            ['F1 Set / fork face (no surjection onto L&#8594;L when a &#8800; &#8869;)',
             'nontrivial_lattice_no_witness (ZeroParadox/Category/Lawvere.lean)'],
        ],
        col_widths=[TW * 0.34, TW * 0.66],
    ))
    E.append(sp(6))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Order / fork spine: choice-free. instance_pinnable_iff_fork_collapse, '
            'instance_always_exists, monotone_regime_derives_pinned: [propext, Quot.sound]; '
            'not_monotone_not: [propext]; lawvere_fixedpoint_selfApp, selfApp_pinnable, '
            'existence_without_uniqueness, reflexive_object_refuted, mu_nu_branch_exclusion: no axioms.',
            'Set-theoretic location / uniqueness (SetTheoryAFA: t_exec, quine_atom_unique): choice-free '
            '&#8212; derived from the ZPSemilattice / AFAStructure class fields alone.',
            'nontrivial_lattice_no_witness (Lawvere.lean) carries [propext, Classical.choice, '
            'Quot.sound], from the classical construction of a fixed-point-free map.',
            'Computability face (ComputableCrossing, Kleene): [propext, Classical.choice, Quot.sound] '
            '&#8212; Classical.choice inherited from Mathlib\'s classical recursion theory (Kleene / '
            'Rogers), disclosed and not claimed otherwise.',
            'Core choice-free, realization choice-carrying &#8212; the framework\'s standing pattern. '
            'Zero sorry. Verified: lake build, October 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-R | A Cross-Category Account of the Self-Referential Fixed Point | '
            'the fork (choice-free) | Set, every carrier except a one-element one: refuted (Cantor) | monotone / domain: '
            'fork, no reflexive object built (Scott D<sub>&#8734;</sub> unbuilt) | computability: crossed '
            '(Rogers / Kleene) | F1: per face, what is measured | F2: the self-application role carries '
            'its face | Lawvere the translation key between the faces (Section III) | no global '
            'conjecture.</i>',
            S['endnote']),
    ]

    print('[build_zpr] Building document...')
    doc.build(E)
    print(f'[build_zpr] Done: {out_path} ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
