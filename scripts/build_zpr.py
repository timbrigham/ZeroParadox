"""
Zero Paradox — ZP-R: A Cross-Category Account of the Self-Referential Fixed Point — PDF Builder
Version 1.6 | August 2026
v1.6: BEDROCK, and the correction is to a MECHANISM rather than to a wording. The rendered text said the escape from the Cantor obstruction is that eval lands in the partial functions "not in the codes, so the Set refutation never applied to it". That is false, and one line refutes it: the partial-function type is itself nontrivial, so no_witness_of_nontrivial forbids the Lawvere witness there exactly as it does on Code - example : not (HasLawvereWitness (Nat ->. Nat)) elaborates. Changing the codomain buys nothing. The real escape is a restriction on which MAPS exist: no computable self-map on codes is eval-fixed-point-free (no_computable_evalFixedPointFree), so the diagonal the Set refutation runs has no computable representative and the obstruction cannot fire. That theorem, with this mechanism spelled out in its own docstring, was already in the corpus - the prose asserted a different reason beside it. Found by the adversary gate at FAIL-BEDROCK, round 3, and confirmed by elaboration before the fix. Corrected at five sites across three surfaces in one sweep rather than at the one named.
v1.0: Initial release. Synthesis / placement layer. Locates and realizes the framework's
self-application fixed point as a Lawvere fixed point across three categories (faces): refuted in Set
(Cantor), obstruction-free but not itself a reflexive object in the monotone/domain regime
(Knaster-Tarski; a genuine reflexive object needs Scott D-infinity), and realized in the computability
face (Rogers / Kleene). All theorems classical and Lean-witnessed; the contribution is the placement,
the cross-face location, and the scope result. The global identification is held as a fenced conjecture.
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.6'
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
            '<i>Synthesis / placement layer. It locates and realizes the framework\'s self-application '
            'fixed point &#8869; as a Lawvere fixed point across three categories ("faces"): refuted in '
            '<b>Set</b> (Cantor), obstruction-free but not itself a reflexive object in the '
            '<b>monotone / domain</b> regime (Knaster&#8211;Tarski; a genuine reflexive object there '
            'needs Scott\'s D<sub>&#8734;</sub>), and realized in the <b>computability</b> face '
            '(Rogers / Kleene). Every theorem used is classical and every claim is backed by a '
            'machine-checked Lean 4 theorem; the contribution is the placement, the cross-face location '
            'under a single discriminator, and the scope result. The global identification &#8212; that '
            'the keystone is Lawvere across all its faces &#8212; is held as a fenced conjecture '
            'throughout.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'A recurring object in this framework is a bottom element &#8869; that is a fixed point of '
        'self-application &#8212; "self-referential" in the sense of being defined by pointing at '
        'itself: a self-containing set (&#8869; = {&#8869;}), a self-reproducing program, the bottom of '
        'a monotone operator\'s fixed-point lattice. This document asks one checkable question: is that '
        'fixed point an instance of <b>Lawvere\'s fixed-point theorem</b> (Lawvere 1969) &#8212; the '
        'categorical statement behind the diagonal arguments of Cantor, Russell, G&#246;del, Turing and '
        'Tarski, unified by Yanofsky (2003) &#8212; and if so, in which category? Lawvere\'s theorem is '
        'category-relative: it holds wherever a suitable <i>reflexive object</i> exists. So the honest '
        'form of the question is not "is it Lawvere" but "<b>where</b> is it Lawvere."'))
    E.append(body(
        'The answer is: <b>yes in one adequate category, and not globally.</b> We locate precisely '
        'where the realization fails and where it succeeds, organized by a single discriminator &#8212; '
        'the presence of a fixed-point-free endomap. The mathematics is classical and is invoked, not '
        'extended; the contribution is (i) the placement of <i>this framework\'s own</i> &#8869; within '
        'the Lawvere fixed point (the general link between self-reference and Lawvere is Yanofsky\'s, '
        'not ours), (ii) the cross-face location of where realization fails and succeeds, and (iii) a '
        'scope result: the realization is category-relative &#8212; an existence statement in one face '
        'rather than a global identification.'))
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
        'value of e at a diagonal point applied to that same point: <b>self-application</b>. The '
        'framework\'s selfApp is the abstract form of exactly this operation.'))

    E.append(result_box(
        'R2a &#8212; Lawvere\'s engine yields its fixed point as a self-application',
        [
            'Lawvere\'s theorem produces its fixed point in the form e a a &#8212; e applied to a '
            'diagonal point, at that same point.',
            'The abstract shadow of e a a is the framework\'s selfApp; its fixed point &#8869; is '
            'exactly a self-application fixed point.',
            'Witness: lawvere_fixedpoint_selfApp (LawvereBridge.lean). Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'R2b &#8212; existence is not uniqueness; the framework\'s pinning is extra',
        [
            'Lawvere\'s theorem gives <i>existence</i> of a fixed point; it does not give uniqueness. '
            'Existence never forces uniqueness &#8212; the identity map has a fixed point but not a '
            'unique one.',
            'So selfApp\'s &#8869; = Lawvere-existence + the framework\'s pinning (uniqueness). The '
            'pinning is the fork-collapse condition of R1, genuinely additional content on top of the '
            'engine.',
            'Witnesses: selfApp_pinnable, existence_without_uniqueness (LawvereBridge.lean). Lean '
            'purity: choice-free. ✓',
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
        'To realize &#8869; <i>as</i> a Lawvere fixed point &#8212; to source it from the engine '
        'rather than posit it &#8212; one needs a reflexive object: a point-surjection onto a function '
        'space. Whether one exists is the entire question, and it has a clean discriminator: the '
        '<b>presence of a fixed-point-free endomap</b>.'))

    E.append(result_box(
        'R3-neg &#8212; in Set, no reflexive object (Cantor); the obstruction is non-monotone',
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
        'removes Lawvere\'s contradiction &#8212; but not by itself <i>sufficient</i>. Two categories '
        'are free of the obstruction, and the framework\'s &#8869; lives in both; but only one of '
        'them furnishes a genuine reflexive object. The reasons are <i>not</i> the same, and the '
        'difference is the point: the monotone regime is free of it <i>literally</i> &#8212; on a '
        '<i>complete lattice</i>, Knaster&#8211;Tarski bans a fixed-point-free monotone endomap, and the '
        'completeness hypothesis is load-bearing, since Nat.succ is a monotone endomap with no fixed '
        'point at all &#8212; while the computable regime is free of it only '
        '<i>up to eval</i> &#8212; literally fixed-point-free total computable endomaps do exist.'))

    E.append(result_box(
        'R3-pos (monotone / domain) &#8212; obstruction absent, but no reflexive object here',
        [
            'On a complete lattice every monotone self-map has least and greatest fixed points '
            '(Knaster&#8211;Tarski), so fixed-point-free monotone endomaps are structurally banned '
            '&#8212; the obstruction is absent. Existence is thereby guaranteed; uniqueness is not '
            '(the interval [lfp, gfp] need not collapse).',
            'This face does <i>not</i> itself furnish a reflexive object: obtaining one in the '
            'order / domain world is the business of Scott\'s D<sub>&#8734;</sub> (Scott-continuous '
            'maps on a directed-complete order, by inverse limits) &#8212; a construction we do not '
            'carry out and do not need, since the computability face below already realizes the '
            'crossing. What this face provides is the <i>fork</i>, not a reflexive object.',
            'Witness: monotone_regime_derives_pinned (LawvereBridge.lean). Lean purity: choice-free. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'R3-pos (computability) &#8212; the reflexive object is realized: the crossing',
        [
            'The category of numbered sets carries a canonical reflexive object: the universal '
            'machine. The evaluation map eval is point-surjective onto the computable functions &#8212; '
            'every computable function has an index (Rogers 1967). And Rogers\' fixed-point theorem '
            'gives every total computable endomap of codes a fixed point <i>up to eval</i> &#8212; two '
            'codes computing the same function.',
            'That is weaker than "no fixed-point-free endomap", and the strong form is false: '
            'c &#8614; pair(c, c) is total, computable, and returns its own input for no c. The '
            'obstruction is absent at the level of <i>eval</i>, which is where the reflexive object '
            'lives &#8212; and the reason is that the effective category admits fewer <i>maps</i>, '
            'not that eval lands in a different type: no computable self-map on codes is '
            'eval-fixed-point-free, so the diagonal the Set refutation runs has no computable '
            'representative.',
            'So the reflexive object is present and the self-referential '
            'fixed point exists there &#8212; Kleene\'s second recursion theorem: for a computable map '
            'f, a code c with eval c = f c.',
            'Witnesses: eval_point_surjective, computable_fixedpoint_up_to_eval, '
            'selfref_fixedpoint_exists_computable (ComputableCrossing.lean). Lean purity: '
            'choice-carrying (Mathlib computability). ✓',
        ]
    ))
    E.append(sp(6))

    E.append(body(
        'That Kleene\'s recursion theorem is an instance of Lawvere\'s theorem is standard: the '
        'derivation is Yanofsky (2003) Theorem 5, p. 18, within his unified treatment. Lawvere '
        '(1969) supplies the engine and raises the recursive case as an open question rather '
        'than deriving it (his &#167;2, p. 9); the '
        'reflexive structure of the computable category is the subject of the Turing-category / '
        'partial-combinatory-algebra literature (Cockett&#8211;Hofstra 2008; Longley). Collecting the '
        'three faces:'))

    E.append(data_table(
        headers=['Face', 'Reflexive object', 'Mechanism', 'Status'],
        rows_data=[
            ['Set',
             'refuted',
             'a fixed-point-free map (negation) blocks it &#8212; Cantor; the obstruction is '
             'non-monotone',
             'the wall'],
            ['Monotone / domain',
             'not furnished here (route: Scott D<sub>&#8734;</sub>, unbuilt)',
             'obstruction absent (Knaster&#8211;Tarski); existence via the fork, uniqueness = fork '
             'collapse',
             'fork story, not a Lawvere realization'],
            ['Computability',
             'realized',
             'universal machine point-surjective; Rogers / Kleene',
             'crossed'],
        ],
        col_widths=[TW * 0.15, TW * 0.20, TW * 0.42, TW * 0.23],
    ))
    E.append(sp(6))

    E.append(result_box(
        'R4 &#8212; the framework\'s fixed point is a Lawvere fixed point, in the computability face',
        [
            'The framework\'s self-reference fixed point <b>is</b> a Lawvere fixed point, realized in '
            'the computability face &#8212; a complete proof of that existential statement, Lawvere\'s '
            'theorem being category-independent, with no obligation to Set or to a Scott domain.',
            'The framework\'s two structural regimes &#8212; the well-founded "wall" and the '
            'non-well-founded "self-referential object" &#8212; are the two regimes of Lawvere\'s '
            'engine: a fixed point refuted versus realized, discriminated by the self-loop.',
            'Witnesses: the computability realization is proved in R3-pos above '
            '(selfref_fixedpoint_exists_computable, ComputableCrossing.lean; choice-carrying); the '
            '&#956;/&#957; discrimination is mu_nu_branch_exclusion (LawvereBridge.lean; '
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
        'F1 &#8212; existence, uniqueness, and location are each proved, but no single face carries all three',
        [
            'Three properties are in play, and it is tempting to read them as one package on a single '
            'object. They are not. Each is established, and each in a <i>different</i> face:',
            '&#8226; <b>Existence as a Lawvere fixed point</b> &#8212; the computability face: Kleene\'s '
            'recursion theorem produces a code c with eval c = f c, genuinely sourced from the '
            'reflexive object (the crossing).',
            '&#8226; <b>Uniqueness</b> (&#8869; is the <i>only</i> fixed point of selfApp) &#8212; the '
            'fork / AFA face: AbstractSelfApp.unique_fp; quine_atom_unique; equivalently the '
            'fork-collapse lfp = gfp of R1.',
            '&#8226; <b>Location</b> (the fixed point is the order-bottom &#8869;) &#8212; also the '
            'fork / AFA face: every Quine atom <i>is</i> &#8869; (T-EXEC, t_exec / t_exec_iff: '
            'IsQuineAtom q &#8596; q = &#8869;), a statement that only has meaning where there is a '
            'canonical bottom to locate it at.',
            'The three do not compose, and the reason is exact: the computability face &#8212; the one '
            'place existence-as-Lawvere is genuinely realized &#8212; is <i>precisely</i> where '
            'uniqueness fails. Kleene\'s theorem gives there not one fixed point but infinitely many '
            '(infinite_quine_family). And "location at &#8869;" is not even <i>expressible</i> in that '
            'face: the category of numbered sets carries no canonical order-bottom.',
            'This is not a gap in the result. The honest statement is not "the framework lacks location '
            'and uniqueness," but "the framework has all three, proved, and no single category can '
            'carry them together." It is the same phenomenon as F2, one level up.',
        ]
    ))
    E.append(sp(6))

    E.append(def_box(
        'F2 &#8212; representation is not transfer; &#8869; carries its face',
        [
            'The crossing is face-local. Realizing &#8869; as a Lawvere fixed point in the '
            'computability face does not make it available in Set, where the same construction remains '
            'a contradiction (Cantor). Consequently &#8869; cannot be <i>globally</i> defined over '
            'standard set-theoretic foundations; it must carry its categorical context &#8212; the face '
            'it lives in &#8212; as part of its definition.',
            'This is not an external limitation imposed on the framework; it is the reason the framework '
            'is stated over a non-well-founded foundation (ZF + AFA rather than ZFC) and treats &#8869; '
            'apophatically &#8212; characterized by its role rather than constructed as a set (Aczel '
            '1988; Barwise &amp; Moss 1996). A face-independent theorem can be <i>witnessed</i> in '
            'whichever category has the reflexive object; the <i>object</i> it produces is defined only '
            'relative to that category.',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'The fences are not hedging. Each per-face result &#8212; the Set wall, the fork, the '
        'computability crossing &#8212; is a full theorem on its own side of them. What the fences '
        'scope is only the global identification: that the keystone is Lawvere across all its '
        'faces. That remains a conjecture; ZP-R is the first concrete progress on it (one face '
        'realized, the obstruction located), not its proof.',
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
        'Cartesian Closed Categories," LNM 92 (1969); Yanofsky, Bull. Symbolic Logic 9(3) (2003). '
        'Lattice fixed points: Tarski, "A lattice-theoretical fixpoint theorem," Pacific J. Math 5 '
        '(1955). The computability fixed points: Rogers, <i>Theory of Recursive Functions and '
        'Effective Computability</i> (1967); Kleene\'s second recursion theorem. The reflexive '
        'structure of the computable category: Cockett &amp; Hofstra, "Introduction to Turing '
        'categories," APAL 156 (2008); Longley (partial combinatory algebras / realizability). The '
        'apophatic, characterize-not-construct treatment of self-referential objects: Aczel, '
        '<i>Non-Well-Founded Sets</i> (1988); Barwise &amp; Moss, <i>Vicious Circles</i> (1996).'))
    E.append(body(
        'Against this, the contribution of ZP-R is not a theorem but a <i>placement</i>: the '
        'identification of the framework\'s &#8869; with the Lawvere fixed point, the cross-face '
        'location of where that realization fails and succeeds under a single discriminator, and the '
        'scope result of Section III. That Kleene\'s recursion theorem is a Lawvere instance is due to '
        'the sources above, not to this document.'))

    # -- What Remains Open ------------------------------------------------------------
    E += [
        hr(),
        Paragraph('What Remains Open', S['h1']),
        hr(),
    ]

    E.append(remark_box(
        'Open items',
        [
            'The <b>global identification</b> &#8212; that the framework\'s keystone <i>is</i> Lawvere '
            'across all its faces &#8212; remains a conjecture, not resolved here. ZP-R is the first '
            'concrete progress on it (one face realized, the obstruction located), not its proof.',
            'The <b>domain-face route</b> &#8212; a Scott D<sub>&#8734;</sub> reflexive object &#8212; '
            'is not carried out; the computability face suffices for the existence claim, so it is not '
            'needed, but it would be a second realization.',
            '<b>Location and uniqueness</b> (that the fixed point is &#8869;, and unique) are '
            '<i>proved</i> &#8212; in the fork / AFA face (T-EXEC; unique_fp) &#8212; not open. What is '
            'structural is that they are not composable with existence-as-Lawvere, which lives in the '
            'computability face where the fixed point is non-unique (infinite_quine_family). That '
            'non-composability is the F1 / F2 result, not a missing piece.',
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
        'Every claim above is backed by a compiling Lean 4 (+ Mathlib) theorem, sorry-free. The order / '
        'fork material is constructively choice-free; the computability material inherits '
        'Classical.choice from Mathlib\'s computability library (Kleene\'s and Rogers\' theorems use '
        'it), which is disclosed and not claimed otherwise.'))

    E.append(data_table(
        headers=['Claim', 'Lean witness (file)'],
        rows_data=[
            ['R1 (the fork)',
             'instance_pinnable_iff_fork_collapse (ZeroParadox/Settheory/RequirementsGap.lean); '
             'instance_always_exists (ZeroParadox/Settheory/MetaFork.lean)'],
            ['R2a / R2b (existence as self-application; uniqueness extra)',
             'lawvere_fixedpoint_selfApp, selfApp_pinnable, existence_without_uniqueness '
             '(ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['R3-neg (Set refuted; obstruction non-monotone)',
             'reflexive_object_refuted, not_monotone_not (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['R3-pos monotone',
             'monotone_regime_derives_pinned (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['R3-pos computability (the crossing)',
             'eval_point_surjective, computable_fixedpoint_up_to_eval, '
             'selfref_fixedpoint_exists_computable (ZeroParadox/Computability/ComputableCrossing.lean)'],
            ['R4 (&#956;/&#957; = Lawvere regimes)',
             'mu_nu_branch_exclusion (ZeroParadox/Settheory/LawvereBridge.lean)'],
            ['F1 location (fixed point = &#8869;)',
             't_exec, t_exec_iff (ZeroParadox/Settheory/SetTheoryAFA.lean)'],
            ['F1 uniqueness (&#8869; the only fixed point)',
             'quine_atom_unique (ZeroParadox/Settheory/SetTheoryAFA.lean); '
             'AbstractSelfApp.unique_fp (ZeroParadox/Computability/SelfApp.lean)'],
            ['F1 non-uniqueness in the computability face',
             'infinite_quine_family (ZeroParadox/Computability/Kleene.lean)'],
        ],
        col_widths=[TW * 0.34, TW * 0.66],
    ))
    E.append(sp(6))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Order / fork spine (RequirementsGap, MetaFork, LawvereBridge order results): choice-free '
            '&#8212; [propext, Quot.sound]. The engine and the fork need no Axiom of Choice.',
            'Set-theoretic location / uniqueness (SetTheoryAFA: t_exec, quine_atom_unique): choice-free '
            '&#8212; derived from the ZPSemilattice / AFAStructure class fields alone.',
            'Computability face (ComputableCrossing, Kleene): [propext, Classical.choice, Quot.sound] '
            '&#8212; Classical.choice inherited from Mathlib\'s classical recursion theory (Kleene / '
            'Rogers), disclosed and not claimed otherwise.',
            'Core choice-free, realization choice-carrying &#8212; the framework\'s standing pattern. '
            'Zero sorry. Verified: lake build, July 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-R | A Cross-Category Account of the Self-Referential Fixed Point | '
            'the fork (choice-free) | Set refuted (Cantor) | monotone / domain: fork, not a reflexive '
            'object (Scott D<sub>&#8734;</sub> unbuilt) | computability: crossed (Rogers / Kleene) | '
            'F1: existence, uniqueness, location each proved, none composable | F2: &#8869; carries its '
            'face | global identification held as a fenced conjecture.</i>',
            S['endnote']),
    ]

    print('[build_zpr] Building document...')
    doc.build(E)
    print(f'[build_zpr] Done: {out_path} ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
