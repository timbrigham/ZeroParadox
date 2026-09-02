"""
Zero Paradox — ZP-J AFA Addendum: Decoration Uniqueness from Valuation Structure
Version 1.11 | September 2026
v1.11: THE v1.10 REMEDY WAS APPLIED TO ONE BOX AND THE OTHERS KEPT THE DEFECT (adversary FAIL-BEDROCK, 4 bedrock; editorial STOP-ORDINARY concurring on the first). v1.10 established that "a box that paraphrases is prose wearing a code block" and fixed toAFAStructure only. Corrected here: (1) page 1 credited "val_bot and val_scale" with giving finiteness for x != bot - val_finite_of_ne_bot is `fun h => hx (val_unique x h)`, the contrapositive of val_unique ALONE, which Scale.lean's module doc and LEAN_CUSTOM_REGISTRY.md already recorded with a Bool counterexample; "the four axioms are minimal" went with it, since an axiom consumed nowhere on the argument is what minimality would deny. (2) Section IV.1 said the decoration equation iterated k times gives d(v) = scale^k(d(v)); collect reduces to scale only through collect_singleton, i.e. only at single-child vertices, and cyclic_decoration_eq_bot does not do this - it chains collect_val_ge and path_val_chain as INEQUALITIES and never forms scale^[k]. The preamble restated the same overclaim and was swept with it. (3) The source-files box called ScaleBridge.lean "Z2 as ValuationStructure instance"; it declares instZ2ValBridge : ValBridge Z_[2], and that file says twice that Z_[2] is not a ValuationStructure. (4) AddValuation.top_iff was cited as the standard name for the val_bot + val_unique pair beside a sentence about Z_[2]; top_iff is stated over a [DivisionRing K] and Z_[2] is a DVR, so it does not apply - the stock route is emultiplicity_eq_top with FiniteMultiplicity.of_prime_left. Both prose gates found (4) independently and one compiled the failure. Also: the ValuationStructure and DecorationUniverse boxes rendered Lean's top as infinity and restated binders, so they did not typecheck as displayed, and are transcribed literally now; the set image `d '' children v` was encoded as U+201C followed by U+2032 at five sites, invisible as a defect in the source and visibly broken on the page; every box header and four rendered citations moved to full repository paths per R-LEANPDF; and the v1.9 changelog entry here still carried the "both rendered into a deposited PDF" overclaim that register.md corrected the same day.
v1.10: THE RENDERED BOX PARAPHRASED THE LEAN IT CLAIMED TO SHOW, and the page contradicted its own vocabulary. Found by the adversary gate reading the EXTRACTED PDF rather than the builder source. Three bindings in the toAFAStructure box were paraphrases - selfMem rendered as an anonymous lambda in Lean 3 comma syntax inside a Lean 4 corpus, bot_self_mem as "fixed_bot", quine_unique as "derived from unique_fp" - so a reader could not resolve the def selfMemDerived citation this document had just added against a box that never names it. Transcribed literally now, with each field marked DATA or LAW. Separately: the prose called bot_self_mem "supplied", a word this section reserves for data, two paragraphs after drawing that distinction; bot_self_mem is a law discharged by a theorem and now says so.
v1.9: CITE BY DECLARATION, NOT BY LINE. Both Lean citations in this file were line numbers and BOTH had drifted: SelfApp.lean:83 pointed at AbstractSelfApp.fixed_bot and :113 at a proof body, neither at the definition being cited. CORRECTED 2026-09-01: this entry originally added "and both rendered into a deposited PDF". Only :113 did - :83 lived in this module docstring, which reaches no rendered page, since no builder renders its own changelog and the extracted v1.9 text carries none. register.md's copy of this entry was corrected the same day and THIS one was missed, which is the half-applied duplicate (DC-28) the correction was itself about. A line number is a copy of a location, so it goes stale silently while reading as precise - the same defect one level down from the field-discipline claim it was citing. Now cited as ZeroParadox/Computability/SelfApp.lean, def selfMemDerived, which the reader can resolve and which cannot drift with an edit above it.
v1.8: FIELD-DISCIPLINE CORRECTION (bedrock). The abstraction-chain prose said "at each step, the fields of the target typeclass are proved as theorems from the source" and "inherits the full AFAStructure as a chain of theorems". False at BOTH steps: a Lean typeclass field is either a LAW you discharge with a proof or DATA you supply, and this chain supplies data at each step - selfApp := scale is an assignment (the box six lines below prints it), and selfMem is supplied by def selfMemDerived. TWO of AFAStructure's three fields become theorems, not three. This was the THIRD ZP-J surface carrying the claim; the other two were corrected in ZP-J v2.6 and comp v1.30 and this one was missed because its sentence contains no numeral. Found by editorial round 5 and now covered mechanically by tools/verify/check_fields.py, which tests the Lean binding rather than the wording.
v1.7: Lean Source Files box now lists SetTheoryAFA.lean (the AFAStructure typeclass home, cited by the def_box); "seven"→"eight" source files; stripped the "as of May 2026" dated qualifier from the endnote.
v1.6: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v1.5: rendered Lean-file citations synced to post-reorg basenames (namespace de-scar); docstring changelog above kept as the historical record.
v1.3: Rendered self-version ref removed from endnote ("Version 1.0 covers…") (C1 sweep). Fixed 2 null glyphs: scaleᵏ (&#7503; modifier-k → <sup>k</sup>).
v1.2: Version changelog removed from preamble.
v1.1: Add COMP_BLUE header banner matching companion template.
v1.0: Initial release. Presents the formal derivation chain from ValuationStructure
      to AFA decoration uniqueness for finite Accessible Pointed Graphs.
      All theorems proved sorry-free in Lean 4.
      Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.
      Lean sources: ZPJ_Scale.lean, ZPJ_SelfApp.lean, ZPJ_AczelConn.lean,
      ZPJ_OntBridge.lean, ZPJ_Model.lean, ZPJ_ScaleBridge.lean, ZPJ_APG.lean.
Reads after ZP-J Self-Reference.
"""

import os
from zp_utils import *

VERSION = '1.11'
FIRST_RELEASED = 'May 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_AFA_Addendum.pdf')
    print(f'[build_zpj_afa_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-J AFA Addendum',
                   'ZP-J AFA Addendum', 'Version ' + VERSION)
    E = []

    # ── Header banner (matches companion template) ─────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-J AFA Addendum',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    print('[build_zpj_afa_addendum] Building title block...')
    E += [
        sp(4),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-J AFA Addendum', S['title']),
        Paragraph('Decoration Uniqueness from Valuation Structure', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble ────────────────────────────────────────────────────────────────
    print('[build_zpj_afa_addendum] Building preamble...')
    E.append(body(
        'This document presents the formal consequences of ZP-J\'s valuation framework '
        'for the central uniqueness theorem of Aczel\'s Anti-Foundation Axiom (AFA). '
        'The main result is decoration_unique '
        '(ZeroParadox/Settheory/APG.lean &#167; IX): for any finite '
        'Accessible Pointed Graph, any two valid decorations must agree at every vertex. '
        'The proof does not import set-theoretic AFA axioms. It derives the uniqueness '
        'property from a chain of abstract typeclasses whose root is ValuationStructure, '
        'established in ZP-J.'))
    E.append(body(
        # ⚠ "The same argument, iterated k times" was the § IV.1 overclaim restated in the
        #   preamble, and the v1.11 sweep of § IV.1 would have left it standing. Swept by the
        #   CLAIM rather than the site the gate named, which is the only thing that reaches
        #   a second copy in a different register.
        'Readers of ZP-J Self-Reference will recognise the key move: &#8869; is the '
        'unique fixed point of scale because any non-&#8869; element has finite depth, '
        'and scale increases depth by 1. Depth is what settles the cyclic case too, '
        'though by bounding rather than by iterating: going once around a cycle forces '
        'a vertex&#8217;s depth to exceed itself, which only infinite depth &#8212; that '
        'is, &#8869; &#8212; can do. Acyclic vertices are handled by strong induction on '
        'the size of the reachable set. Both cases together give decoration_unique.'))
    E.append(hr())

    # ── Section I: ValuationStructure ──────────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section I...')
    E += [
        Paragraph('Section I: ValuationStructure and its Unique Fixed Point', S['h1']),
        hr(),
    ]

    E.append(body(
        'ValuationStructure is the root typeclass of the derivation chain. It abstracts '
        'the depth-measure argument that drives every uniqueness result in this document. '
        'A type L carries a ValuationStructure when it has a ZPSemilattice structure, '
        'a self-application operation scale, and a depth measure val taking values in '
        '&#8469;&#8734; (the natural numbers extended with a point at infinity).'))

    E.append(def_box(
        'Typeclass: ValuationStructure (ZeroParadox/Valuation/Scale.lean)',
        [
            'class ValuationStructure (L : Type*) [ZPSemilattice L] where',
            '  scale : L &#8594; L',
            '  val        : L &#8594; &#8469;&#8734;',
            '  scale_bot  : scale bot = bot',
            '  val_bot    : val bot = &#8868;',
            '  val_unique : &#8704; x : L, val x = &#8868; &#8594; x = bot',
            '  val_scale  : &#8704; x : L, x &#8800; bot &#8594; val (scale x) = val x + 1',
            '',
            'Transcribed from ZeroParadox/Valuation/Scale.lean. &#8868; is the top of '
            '&#8469;&#8734;, written &#8734; in the prose above; bot is ZPSemilattice&#8217;s '
            '&#8869;. Read: scale fixes the bottom, the bottom has infinite depth, only the '
            'bottom does, and scale adds one everywhere else.',
        ]
    ))
    E.append(sp(4))

    # ⚠ THE ATTRIBUTION HERE WAS WRONG UNTIL v1.11 AND THE CORPUS ALREADY SAID SO. This read
    #   "val_bot and val_scale together give the key consequence". `val_finite_of_ne_bot` is
    #   `fun h => hx (ValuationStructure.val_unique x h)` - the one-line contrapositive of
    #   val_unique ALONE, with val_bot in none of the three proof terms on that chain.
    #   Scale.lean's module doc and LEAN_CUSTOM_REGISTRY.md:51 both record this, measured
    #   2026-08-30 with a Bool counterexample (val everywhere top: scale_bot, val_bot and
    #   val_scale all hold and `true` is a non-bottom fixed point). "Minimal" went with it:
    #   an axiom consumed nowhere on the argument is exactly what minimality would deny.
    E.append(body(
        'val_unique and val_scale carry this section&#8217;s argument: val_unique gives, for '
        'any x &#8800; &#8869;, that val(x) is finite &#8212; it is the contrapositive of '
        '&#8220;infinite depth identifies &#8869;&#8221; &#8212; and val_scale makes scale '
        'strictly increase it. No element of finite depth can therefore satisfy scale(x) = x. '
        'val_bot is consumed nowhere on that chain (measured 2026-08-30); it fixes the depth '
        'of &#8869; itself, which the fixed-point argument never reads.'))

    E.append(result_box(
        'Theorem: scale_unique_fp (ZeroParadox/Valuation/Scale.lean)',
        [
            '&#8704; x : L,  scale x = x  &#8594;  x = &#8869;',
            '&#8869; is the only fixed point of scale.',
            'Proof: suppose scale x = x and x &#8800; &#8869;. By val_scale, '
            'val(scale x) = val(x) + 1. But scale x = x gives val(x) = val(x) + 1, '
            'which is impossible in &#8469;&#8734; for any finite value. Contradiction.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Section II: The Derivation Chain ───────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Derivation Chain', S['h1']),
        hr(),
    ]

    E.append(body(
        'ValuationStructure generates two further typeclasses by successive derivation. '
        'AbstractSelfApp extracts the fixed-point structure from ValuationStructure, '
        'replacing scale with an abstract selfApp operation. AFAStructure &#8212; '
        'the three-field typeclass encoding the Quine atom properties &#8212; '
        'is then derived from AbstractSelfApp. At each step the LAWS of the target typeclass are '
        'proved as theorems from the source, and the DATA fields are supplied by definition: '
        'the selfApp field of AbstractSelfApp is assigned (selfApp := scale), and the selfMem '
        'field of AFAStructure is supplied by def selfMemDerived. TWO of the three AFAStructure '
        'fields become theorems, not three (ZeroParadox/Computability/SelfApp.lean, '
        'def selfMemDerived). No new axioms are introduced. '
        'The relationship to Aczel\'s theorem in ZF+AFA is discussed in Remark R-J.A (§V).'))

    E.append(def_box(
        'Typeclass: AbstractSelfApp (ZeroParadox/Computability/SelfApp.lean)',
        [
            'class AbstractSelfApp (L : Type*) [ZPSemilattice L] where',
            '  selfApp   : L &#8594; L',
            '  fixed_bot : selfApp &#8869; = &#8869;',
            '  unique_fp : &#8704; x : L, selfApp x = x &#8594; x = &#8869;',
            '',
            'Instance toAbstractSelfApp (ZeroParadox/Valuation/Scale.lean):',
            '  selfApp   := scale',
            '  fixed_bot := scale_bot         (direct from ValuationStructure)',
            '  unique_fp := scale_unique_fp   (proved in §I above)',
            'No new axioms.',
        ]
    ))
    E.append(sp(4))

    E.append(body(
        'AFAStructure is the lattice-level encoding of the three structural facts that '
        'ZF+AFA provides set-theoretically: that &#8869; contains itself, that it is '
        'the only self-containing element, and the self-membership predicate itself. '
        'In ZF+AFA, the existence of a self-containing set follows from AFA\'s existence '
        'clause applied to the one-node self-loop graph; uniqueness follows from AFA\'s '
        'uniqueness clause. In the ZP encoding, the existence field '
        # ⚠ "supplied" is reserved on this page for DATA. bot_self_mem is a LAW - a Prop-valued
        #   field discharged by a theorem - so saying it is "supplied" collapses the very
        #   distinction the section is drawing two paragraphs above.
        '(<i>bot_self_mem</i>) is a LAW, discharged by a theorem built from <i>fixed_bot</i> '
        'in AbstractSelfApp. The uniqueness field (<i>quine_unique</i>) is likewise a law, '
        'proved from <i>unique_fp</i>. Only <i>selfMem</i> is data, and only it is supplied '
        '&#8212; no new axioms are introduced at this step.'))

    E.append(def_box(
        'Typeclass: AFAStructure (ZeroParadox/Settheory/SetTheoryAFA.lean)',
        [
            'class AFAStructure (L : Type*) [ZPSemilattice L] where',
            '  selfMem      : L &#8594; Prop',
            '  quine_unique : &#8704; x y : L, selfMem x &#8594; selfMem y &#8594; x = y',
            '  bot_self_mem : selfMem &#8869;',
            '',
            # ⚠ TRANSCRIBED LITERALLY from ZeroParadox/Computability/SelfApp.lean, instance
            #   toAFAStructure. The previous rendering PARAPHRASED all three bindings and wrote
            #   the lambda in Lean 3 comma syntax inside a Lean 4 corpus, so a reader could not
            #   resolve the `def selfMemDerived` citation against a box that bound selfMem to an
            #   anonymous function. A box that paraphrases is prose wearing a code block.
            'Instance toAFAStructure (ZeroParadox/Computability/SelfApp.lean):',
            '  selfMem      := selfMemDerived          (DATA - supplied, a def)',
            '  bot_self_mem := derived_bot_self_mem    (LAW - discharged by a theorem)',
            '  quine_unique := derived_quine_unique    (LAW - discharged by a theorem)',
            'No new axioms. Two of the three fields are laws and become theorems;',
            'selfMem is data and is supplied.',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Proposition: Derivation Chain '
        '(ZeroParadox/Valuation/Scale.lean, ZeroParadox/Computability/SelfApp.lean)',
        [
            'ValuationStructure L  &#8658;  AbstractSelfApp L  &#8658;  AFAStructure L',
            'Each arrow is a Lean instance derivation proved without new axioms.',
            'Any type satisfying ValuationStructure inherits the two AFAStructure LAWS as theorems; '
            'its data field selfMem is supplied by definition, not proved.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(remark_box(
        'Remark: Scope of the Chain',
        [
            'The derivation chain shows that ValuationStructure is sufficient to satisfy '
            'AFAStructure\'s three fields within the ZP typeclass hierarchy. It does not '
            'show that AFA is derivable from ZF: Foundation and AFA remain mutually '
            'exclusive set-theoretic frameworks. The chain is internal to the ZP lattice '
            'abstraction and says nothing about which set-theoretic axioms hold. '
            'The precise relationship to Aczel\'s decoration theorem is discussed in '
            'Remark R-J.A (§V).',
        ]
    ))
    E.append(sp(6))

    # ── Section III: APGs and Decorations ──────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: Accessible Pointed Graphs and Decorations', S['h1']),
        hr(),
    ]

    E.append(body(
        'An Accessible Pointed Graph (APG) is the combinatorial setting for AFA\'s '
        'central theorem. The decoration uniqueness theorem asserts that any two valid '
        'labellings of an APG\'s vertices must agree. This section defines both notions '
        'in the abstract setting of ZP\'s DecorationUniverse typeclass.'))

    E.append(def_box(
        'Definition: Accessible Pointed Graph (ZeroParadox/Settheory/APG.lean §I)',
        [
            'An APG over vertex type V (a Quiver) is a structure APG V with:',
            '  root       : V',
            '  accessible : &#8704; v : V, Reachable root v',
            '',
            'Every vertex is reachable from root by following directed edges.',
            '',
            'children(v) = { w : V | v &#8594; w }   (immediate successors)',
            'Reach(v)    = { w : V | Reachable v w }  (all vertices reachable from v)',
            '',
            'In a finite APG (Fintype V), every Reach(v) is a finite set. '
            '|Reach(v)| is the cardinality used in the induction of §IV.',
        ]
    ))
    E.append(sp(4))

    E.append(body(
        'A decoration assigns labels from a DecorationUniverse to each vertex, '
        'subject to a local consistency condition: the label at v is assembled from '
        'the labels of its immediate successors via the collect operation.'))

    E.append(def_box(
        'Typeclass: DecorationUniverse (ZeroParadox/Settheory/APG.lean §II)',
        [
            'class DecorationUniverse (U : Type*) [ZPSemilattice U] '
            '[ValuationStructure U] where',
            '  collect : Set U &#8594; U',
            '  collect_singleton : &#8704; x : U, collect {x} = ValuationStructure.scale x',
            '  collect_val_ge : &#8704; (S : Set U) (x : U), x &#8712; S &#8594;',
            '      ValuationStructure.val (collect S) &#8805; ValuationStructure.val x + 1',
            '',
            'Transcribed from ZeroParadox/Settheory/APG.lean. IsDecoration d means '
            '&#8704; v, d v = collect (d &#39;&#39; apg_children v), where d &#39;&#39; S is '
            'Lean&#8217;s set image &#8212; { d w | w &#8712; S }. &#8942; The two axioms pin '
            'only the SINGLETON case and a lower bound; they do not require collect to assemble '
            'a parent&#8217;s value from its children&#8217;s.',
        ]
    ))
    E.append(sp(6))

    # ── Section IV: Decoration Uniqueness ──────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Decoration Uniqueness', S['h1']),
        hr(),
    ]

    E.append(body(
        'The main theorem asserts that any finite APG admits at most one valid '
        'decoration. The proof splits on whether a vertex lies on a directed cycle.'))

    E.append(result_box(
        'Theorem: decoration_unique (ZeroParadox/Settheory/APG.lean §IX)',
        [
            '&#8704; {V : Type*} [Quiver V] [Fintype V]',
            '  {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]',
            '  (G : APG V) (d&#8321; d&#8322; : V &#8594; U),',
            '  IsDecoration d&#8321; &#8594; IsDecoration d&#8322; &#8594; d&#8321; = d&#8322;',
            '',
            'For any finite APG, any two valid decorations into a DecorationUniverse agree '
            'at every vertex.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(Paragraph('IV.1 — Cyclic Vertices', S['h2']))
    E.append(body(
        'A vertex v is cyclic if there exists a directed path from v back to itself. '
        'The valuation argument forces any valid decoration to assign &#8869; to every '
        'cyclic vertex, independent of which decoration is used. Both d&#8321; and '
        'd&#8322; must therefore assign &#8869; to every cyclic vertex, and they '
        'agree trivially on this case.'))
    # ⚠⚠ THIS PARAGRAPH DESCRIBED A DIFFERENT PROOF UNTIL v1.11, and the one it described does
    #   not go through. It read: "the decoration equation applied k times around the cycle gives
    #   d(v) = scale^k(d(v))". A decoration sends v to `collect (d '' apg_children v)`, and
    #   `collect` reduces to `scale` ONLY through `collect_singleton`, i.e. only where the vertex
    #   has exactly one child - so the iterated-scale equation needs a hypothesis the theorem
    #   never assumes. And it is not what `cyclic_decoration_eq_bot` (APG.lean:383) does: that
    #   proof chains two INEQUALITIES and never forms scale^[k] at all. Described as proved now.
    E.append(body(
        'The argument is a chain of two inequalities, not an iterated equation. Let w be the '
        'next vertex on the cycle. Because w is a child of v and d(v) collects over d of v&#8217;s '
        'children, collect_val_ge gives val(d(v)) &#8805; val(d(w)) + 1. Following the cycle back '
        'from w to v, path_val_chain gives val(d(w)) &#8805; val(d(v)) + length(p). Together these '
        'force val(d(v)) to exceed itself, which no finite value in &#8469;&#8734; can do, so '
        'val(d(v)) = &#8734; and therefore d(v) = &#8869;.'))

    E.append(result_box(
        'Lemma: val_iterate (ZeroParadox/Settheory/APG.lean &#167; III)',
        [
            '&#8704; (x : U) (hx : x &#8800; &#8869;) (k : &#8469;),',
            '  val (scale^[k] x) = val x + k',
            'For any x &#8800; &#8869;, applying scale k times increases depth by exactly k.',
            'Proof: induction on k; val_scale applies at each step because '
            'scale^[n](x) &#8800; &#8869; follows from the induction hypothesis '
            'and finiteness of val(x).',
            '&#8942; This is a genuine lemma of &#167; III and it drives '
            'scale_iterate_unique_fp below. It is NOT what the cyclic case above uses: '
            'cyclic_decoration_eq_bot never forms scale^[k].',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: scale_iterate_unique_fp (ZeroParadox/Settheory/APG.lean §IV)',
        [
            '&#8704; (k : &#8469;) (hk : 0 < k) (x : U),  scale^[k] x = x  &#8594;  x = &#8869;',
            '&#8869; is the only element fixed by any k-fold iteration of scale (k &#8805; 1).',
            'Proof: if scale^[k] x = x and x &#8800; &#8869;, then val_iterate gives '
            'val(x) = val(x) + k with k &#8805; 1 &#8212; contradiction.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: cyclic_decoration_eq_bot '
        '(ZeroParadox/Settheory/APG.lean &#167; VII&#8242;)',
        [
            '&#8704; (d : V &#8594; U) (hd : IsDecoration d) (v : V),',
            '  HasSelfCycle v &#8594; d v = &#8869;',
            'Consequence: d&#8321; v = d&#8322; v = &#8869; for every cyclic vertex v.',
            'Proof route, as written: collect_val_ge across one edge gives '
            'val(d v) &#8805; val(d w) + 1, path_val_chain around the cycle gives '
            'val(d w) &#8805; val(d v) + length(p), and the two together are '
            'unsatisfiable for finite val. It consumes val_unique through '
            'val_finite_of_ne_bot, and assumes nothing about how many children a '
            'vertex has.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(Paragraph('IV.2 — Acyclic Vertices', S['h2']))
    E.append(body(
        'A vertex v is acyclic if no directed cycle passes through it. The argument '
        'uses strong induction on |Reach(v)|. Every vertex reaches itself via the '
        'empty path, so |Reach(v)| &#8805; 1 for every v; the n = 0 branch is vacuous. '
        'All actual vertices fall into the inductive step.'))
    E.append(body(
        '<b>Inductive step.</b> Suppose d&#8321; and d&#8322; agree on every vertex w '
        'with |Reach(w)| &lt; n, and suppose |Reach(v)| = n with v acyclic. '
        'For each successor w &#8712; children(v): since v is acyclic, v is not '
        'reachable from w, so Reach(w) &#8842; Reach(v), giving |Reach(w)| &lt; n. '
        'By the induction hypothesis, d&#8321;(w) = d&#8322;(w) for every '
        'w &#8712; children(v). When children(v) = &#8709; this hypothesis is '
        'vacuously satisfied: collect is a function, the image of &#8709; under any '
        'decoration is &#8709;, so both d&#8321;(v) and d&#8322;(v) equal collect(&#8709;) '
        'and agree. When children(v) &#8800; &#8709;, the induction hypothesis gives '
        'd&#8321; &#39;&#39; children(v) = d&#8322; &#39;&#39; children(v), and '
        'the decoration equation then gives '
        'd&#8321;(v) = collect(d&#8321; &#39;&#39; children(v)) = '
        'collect(d&#8322; &#39;&#39; children(v)) = d&#8322;(v). '
        'In both sub-cases, acyclic_induction_step formalises the argument.'))

    E.append(result_box(
        'Lemma: acyclic_induction_step (ZeroParadox/Settheory/APG.lean §VIII)',
        [
            'If d&#8321; and d&#8322; agree on every successor of an acyclic vertex v,',
            'then d&#8321; v = d&#8322; v.',
            'Proof: collect is the same operation for both; d&#8321; and d&#8322; agree '
            'pointwise on children(v) by hypothesis; therefore the assembled labels agree.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(Paragraph('IV.3 — Combining the Cases', S['h2']))
    E.append(body(
        'Every vertex in a finite APG is either cyclic or acyclic. The two cases are '
        'exhaustive and jointly establish d&#8321;(v) = d&#8322;(v) for every vertex v. '
        'Since V is a Fintype, funext closes the global equality d&#8321; = d&#8322;.'))
    E.append(sp(6))

    # ── Section V: Scope and Purity ─────────────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Scope, Purity, and Open Questions', S['h1']),
        hr(),
    ]

    E.append(body(
        'decoration_unique establishes the <i>uniqueness</i> half of AFA\'s central '
        'theorem for abstract DecorationUniverses over finite graphs. Two scope '
        'boundaries are worth stating explicitly.'))

    E.append(body(
        '<b>Existence.</b> This document does not prove that every finite APG admits '
        'a valid decoration. Uniqueness and existence are independent: one can show '
        'that no two decorations can differ without showing that any decoration exists. '
        'The existence half is not formalised here for abstract DecorationUniverses '
        'and remains an open question.'))

    E.append(body(
        '<b>Finite graphs.</b> decoration_unique requires Fintype V. The strong '
        'induction on |Reach(v)| terminates because V is finite. Extending the result '
        'to infinite APGs would require an ordinal induction or a well-foundedness '
        'argument on the reachability relation, and is not addressed here.'))

    E.append(body(
        '<b>Commented-out stub.</b> ZeroParadox/Settheory/APG.lean contains a '
        'commented-out theorem '
        '<i>acyclic_decoration_unique</i> with a sorry placeholder. That stub is not '
        'used by the proof of decoration_unique: the final proof proceeds by direct '
        'strong induction using acyclic_induction_step, without using the stub. '
        'All active (non-commented-out) theorems in the eight source files are '
        'sorry-free.'))

    # ⚠ TWO CORRECTIONS AT v1.11, both in this one box.
    #   (1) The ScaleBridge row said "ℤ₂ as ValuationStructure instance". It declares
    #       `instZ2ValBridge : ValBridge ℤ_[2]` (ScaleBridge.lean:116), and that file's own
    #       [ZP-CUSTOM] tag one line above says ℤ_[2] does NOT satisfy ValuationStructure,
    #       because no ZPSemilattice ℤ_[2] is defined. The parenthetical "(via ValBridge
    #       typeclass)" hedged the mechanism while the head of the sentence still asserted
    #       the membership the corpus denies twice.
    #   (2) R-LEANPDF: a CHECKABLE surface carries the FULL repository path. All eight
    #       basenames resolve today; the exposure is the next file move, and a bare basename
    #       fails SILENT - plausible and pointing nowhere - where a full path fails LOUD.
    #       Also ℤ₂ -> ℤ_[2]: ℤ₂ reads as the integers mod 2, which is a different object.
    E.append(label_box(
        'Lean Source Files',
        [
            'ZeroParadox/Valuation/Scale.lean &#8212; ValuationStructure, '
            'scale_unique_fp, toAbstractSelfApp',
            'ZeroParadox/Computability/SelfApp.lean &#8212; AbstractSelfApp, '
            'selfMemDerived, derived_bot_self_mem, derived_quine_unique, toAFAStructure',
            'ZeroParadox/Settheory/SetTheoryAFA.lean &#8212; AFAStructure typeclass '
            '(selfMem, quine_unique, bot_self_mem), IsQuineAtom',
            'ZeroParadox/Settheory/AczelConn.lean &#8212; J_self, '
            'selfMem_determines_singleton, DC-free identification theorems',
            'ZeroParadox/Settheory/OntBridge.lean &#8212; OntologicalStates as '
            'AbstractSelfApp instance',
            'ZeroParadox/Settheory/Model.lean &#8212; instNatInfZPS and instNatInfVal, '
            '&#8469;&#8734; as a ValuationStructure instance',
            'ZeroParadox/Valuation/ScaleBridge.lean &#8212; instZ2ValBridge : '
            'ValBridge &#8484;_[2]. Note &#8484;_[2] is NOT a ValuationStructure instance: '
            'no ZPSemilattice &#8484;_[2] is defined, and ValBridge is the variant that '
            'drops that requirement while keeping the same four axioms.',
            'ZeroParadox/Settheory/APG.lean &#8212; APG, DecorationUniverse, val_iterate, '
            'scale_iterate_unique_fp, cyclic_decoration_eq_bot, '
            'acyclic_induction_step, decoration_unique',
            'All paths are repository-relative, in the public repository.',
        ]
    ))
    E.append(sp(4))

    E.append(label_box(
        'Axiom Footprint (all results in this document)',
        [
            '[propext, Classical.choice, Quot.sound]',
            'propext          &#8212; propositional extensionality (standard in Lean 4)',
            'Classical.choice &#8212; choice principle (Mathlib Finset and Fintype '
            'machinery)',
            'Quot.sound       &#8212; quotient soundness (standard in Lean 4)',
            'No ZP-specific axioms beyond [propext, Classical.choice, Quot.sound].',
            'No Dependent Choice. No additional set-theoretic assumptions.',
        ]
    ))
    E.append(sp(4))

    E.append(remark_box(
        'Remark R-J.A &#8212; Relationship to Aczel\'s Theorem',
        [
            'Aczel\'s decoration theorem (Non-Well-Founded Sets, CSLI 1988) states that '
            'every APG has a unique decoration into the universe of non-well-founded sets. '
            'The result here is not a re-proof of Aczel\'s theorem by different methods. '
            'The objects are different: Aczel\'s target is a specific set-theoretic '
            'universe; the target here is any type carrying ValuationStructure and a '
            'collect operation, with no set-membership semantics required. '
            'The contribution is the generalisation: decoration uniqueness holds for any '
            'abstract DecorationUniverse satisfying the depth-measure axioms, independently '
            'of set-theoretic content. Whether the existence half of Aczel\'s theorem '
            'generalises to abstract DecorationUniverses is an open question.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after '
        'it. The derivation chain (ValuationStructure &#8594; AbstractSelfApp &#8594; '
        'AFAStructure) is established in ZP-J; this document applies it to the APG '
        'decoration problem. It covers the uniqueness result for finite graphs. '
        'All active theorems are sorry-free in Lean 4 '
        '(one commented-out stub; see §V).',
        S['endnote']))

    print(f'[build_zpj_afa_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
