"""
Zero Paradox — ZP-J AFA Addendum: Decoration Uniqueness from Valuation Structure
Version 1.16 | September 2026
v1.16: THE v1.15 FIX INTRODUCED A REGRESSION INTO THE BOX IT WAS FIXING (editorial FAIL-BEDROCK, round 5). v1.15 restored the underscore in the decoration_unique binder by ADDING a line reading (_G : APG V) and never removing the old (G : APG V), so the rendered box declared TWO APG binders where the theorem has one, and placed the survivor BEFORE the {U} block instead of after it. Elaborated this round with lake env lean: @ZeroParadox.decoration_unique takes exactly one, (_G : APG V), following [DecorationUniverse U], with [Fintype V] ahead of the {U} block. The box is transcribed from the elaborated signature now rather than edited toward it. Every mechanical gate passed and check_codebox reported 0, because that checker resolves IDENTIFIERS and a duplicated binder is a well-formed identifier used twice - the defect is in the SHAPE, which nothing mechanical reads. Also: "AFA's central theorem" survived at two further sites in this document, the section IV preamble and the scope note after the theorem box. Aczel ch.1 p.6 states AFA as an AXIOM - "The Anti-Foundation Axiom, AFA: Every graph has a unique decoration" - and this document's own Remark R-J.A said so on page 8 while these two contradicted it; both now point at the Remark rather than restating the claim a third time. And v1.15's "sites five and six" is SCOPED, not closed: it counted within this document, and a four-axis sweep of the rendered text on 2026-09-02 found the class live at five further sites across three deposited PDFs, filed as ZPJ-AFA-THM. That sweep ran over the delta domain, 33 files and 6 rendered PDFs; --full was not taken, so five is a FLOOR and not a total. v1.15: THE v1.14 FIX OVER-CORRECTED, AND BOTH PROSE GATES CAUGHT IT (editorial FAIL-BEDROCK, adversary concurring as ordinary). Editorial's sentence is the finding: v1.13 made a REMOVABLE cost look UNAVOIDABLE, v1.14 makes an UNMEASURED one look REMOVABLE. Same conflation, opposite sign, and v1.14's was the flattering direction. The class-level measurement was true and both gates reproduced it; what was wrong is the SCOPE, because the box was headed "all results in this document". Measured this round: decoration_unique reports [propext, Classical.choice, Quot.sound]; Set.ncard_lt_ncard and Set.ncard_pos are each independently tainted; and Nonempty.some unfolds to `fun h => Classical.choice h`, so the proof does not inherit choice through packaging, it CALLS it. Fintype is not absent either - this PDF prints [Fintype V] in the decoration_unique box and says decoration_unique requires it, one page before v1.14's line denied it. The box now names three routes, scopes ACCIDENTAL to the class where _VScast exhibits the clean proof, and states the theorem's removability as UNMEASURED - R-REVALIDATE: accidental is earned by exhibiting a clean proof or not at all. The exclusion is now MEASURED rather than asserted, which is the adversary's improvement: Finset and Fintype each report [propext, Quot.sound], so neither has any choice to supply. Also: the Remark's own TITLE still said "Relationship to Aczel's Theorem" three words above its body's "an axiom, not a theorem", and the preamble called the unique-decoration content a theorem - sites five and six of that claim within this document; the decoration_unique box dropped the underscore from (_G : APG V), erasing the signal that accessibility is never consumed; and Scale.lean's "val_bot is consumed nowhere" is true of section I and false three rendered pages later at val_iterate, so it is scoped now. 
v1.14: TWO BEDROCK ON PAGE 8, BOTH UNTOUCHED BY EVERY ROUND SINCE v1.9 (adversary round 5, FAIL-BEDROCK 2). (1) The axiom-footprint box attributed Classical.choice to "Mathlib Finset and Fintype machinery". Measured with lake env lean: ValuationStructure - a BARE TYPECLASS mentioning neither - reports [propext, Classical.choice, Quot.sound], and so does instAddMonoidWithOneENat, the instance the numeral 1 in val_scale reaches for. Scale.lean's _VSlit/_VScast pair proves that numeral is THE route rather than one of several: respelling it as ((1 : N) : Ninf) and nothing else makes the class report no axioms. This mattered beyond a citation slip because the next line read "No ZP-specific axioms beyond", so naming a library turned a REMOVABLE cost into an UNAVOIDABLE one - the exact conflation AxiomProfile.lean section 0 warns about, PROVENANCE and NECESSITY being independent axes. The corrected text keeps them apart: the tainted INSTANCE is Mathlib's, the SPELLING that reaches for it is this framework's, and the dependence is accidental. (2) Remark R-J.A called AFA "Aczel's decoration theorem ... every APG ... universe of non-well-founded sets". Three errors: it is an AXIOM (ch.1 p.6, the book is in this repository and was opened), over every GRAPH not every APG, into the universe of SETS - the book's own example decorates with 0, {0} and 3, all well-founded. The decoration THEOREM is Mostowski's Collapsing Lemma, for WELL-FOUNDED graphs. CLAIMS.md and APG.lean already said this correctly and this document's preamble calls it an axiom eight pages earlier. The claim was swept, not the site: FOUR sites, and the fourth said "Aczel's theorem" with no "decoration", so a source grep for the longer phrase never reached it - only the rendered check did. Also closes E5-1: the four Lean-statement lines that printed the bottom as a glyph with no global notation now spell it as the Lean does, and tools/verify/check_codebox.py - written this session because R-NOCONV says a loop that will not settle changes SHAPE - reports 0 where it reported 4. Fifth consecutive version to touch this class, and the first whose fix is MEASURED rather than believed. 
v1.13: BEDROCK, AND THE v1.12 SWEEP MISSED IT BY THREE LINES. The APG box defined Reach(v) = { w : V | Reachable v w }. `Reachable` is NOT LOCATED in APG.lean as of 2026-09-02 - zero occurrences, searched by identifier - and the only resolution located that day, over ZeroParadox/**/*.lean and the tracked build scripts, was SimpleGraph.Reachable, which is SYMMETRIC - and section IV.2's induction terminates ONLY because reachability here runs one way: from an acyclic v to a child w, v is not reachable back, so Reach(w) is a STRICT subset and the cardinality decreases. Under a symmetric relation the two sets are equal, the descent never shrinks, and the proof this document narrates does not terminate. A false definition carrying the main theorem's termination argument. v1.12 changed the `accessible` line directly above it FOR THIS EXACT REASON and left this one - the half-applied sweep at its smallest possible radius, inside the version whose subject was half-applied sweeps. Found by the adversary gate running the rendered BOX as a unit; a source reader sees a diff touching the line the changelog names and reads it as done. Also: two inherited counts in register.md replaced by pointers - "four sites" stood over an enumeration of five, and "all fifteen corrections" was v1.11's numeral carried into v1.12 over six of its own (R-ADJACENT: never enumerate in prose what an artifact defines). 
v1.12: ROUND 4 — the v1.11 sweep was applied to two code boxes of four, and its own write-up claimed more than it did. Adversary FAIL-BEDROCK (2, both in OTHER ZP-J documents and filed, not touched here) + 5 ordinary; editorial STOP-ORDINARY 0/4; all four v1.11 remediations HELD under both gates, and the AddValuation.top_iff replacement was settled by ELABORATION in both directions - the emultiplicity_eq_top + FiniteMultiplicity.of_prime_left route compiles on Z_[2], and the control AddValuation.top_iff fails to elaborate there, as it must. Corrected in this version: the AbstractSelfApp and AFAStructure boxes still rendered Lean's `bot` as the bottom glyph, and there is no global notation for ZPSemilattice.bot - only a LOCAL one in Lattice.lean - so compiling either box as displayed gave 'failed to synthesize Bot L'; the APG box showed `Reachable root v` where the field is `Nonempty (Quiver.Path root v)`, and Reachable is SimpleGraph's, not a quiver notion; 'Z_[2] is NOT a ValuationStructure instance' shipped bare while three sources changed in the same commit hedge exactly that sentence, so it now says no such instance is REGISTERED, which is the checkable claim; funext was credited to Fintype, where function extensionality needs no finiteness at all and finiteness is consumed earlier by the acyclic descent (DC-32); and the note marker U+22EE, which means elided material, became the house U+2022.
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

VERSION = '1.16'
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
        'for the central uniqueness CLAUSE of Aczel\'s Anti-Foundation Axiom (AFA). '
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
            '&#8704; x : L, scale x = x &#8594; x = bot',
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
        # ⚠ FOURTH SITE, and my source grep for "Aczel's decoration theorem" did not reach it —
        #   this one says "Aczel's theorem" with no "decoration". Found only because the RENDERED
        #   check swept the shorter form. Grepping the phrase I happened to have written is the
        #   narrower-probe defect R-NOTINLIB names; the claim is what recurs, not the wording.
        'The relationship to Aczel\'s Anti-Foundation Axiom in ZF+AFA is discussed in '
        'Remark R-J.A (§V).'))

    E.append(def_box(
        'Typeclass: AbstractSelfApp (ZeroParadox/Computability/SelfApp.lean)',
        [
            'class AbstractSelfApp (L : Type*) [ZPSemilattice L] where',
            '  selfApp : L &#8594; L',
            '  fixed_bot : selfApp bot = bot',
            '  unique_fp : &#8704; x : L, selfApp x = x &#8594; x = bot',
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
            '  selfMem : L &#8594; Prop',
            '  quine_unique : &#8704; x y : L, selfMem x &#8594; selfMem y &#8594; x = y',
            '  bot_self_mem : selfMem bot',
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
            'The precise relationship to Aczel\'s Anti-Foundation Axiom is discussed in '
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
        'An Accessible Pointed Graph (APG) is the combinatorial setting for the '
        'unique-decoration property AFA asserts — an AXIOM, not a theorem; see Remark '
        'R-J.A. The decoration uniqueness theorem asserts that any two valid '
        'labellings of an APG\'s vertices must agree. This section defines both notions '
        'in the abstract setting of ZP\'s DecorationUniverse typeclass.'))

    E.append(def_box(
        'Definition: Accessible Pointed Graph (ZeroParadox/Settheory/APG.lean §I)',
        [
            'An APG over vertex type V (a Quiver) is a structure APG V with:',
            '  root       : V',
            '  accessible : &#8704; v : V, Nonempty (Quiver.Path root v)',
            '',
            'Every vertex is reachable from root by following directed edges.',
            '',
            # ⚠⚠ `Reachable` DOES NOT EXIST IN APG.lean — zero occurrences — and the only symbol
            #   that name could resolve to is `SimpleGraph.Reachable`, which is SYMMETRIC. That is
            #   not a naming nit: § IV.2's induction terminates ONLY because reachability here runs
            #   ONE WAY. From an acyclic v to a child w, v is not reachable back from w, so
            #   Reach(w) is a STRICT subset of Reach(v) and |Reach| decreases. Under a symmetric
            #   relation the two sets are EQUAL, the descent never shrinks, and the proof this
            #   document narrates does not terminate. A false definition carrying the main
            #   theorem's termination argument.
            #   ⚠ AND IT SURVIVED THE v1.12 SWEEP BY THREE LINES: that round changed `accessible`
            #   on the line above FOR THIS EXACT REASON and left this one. Same box, same defect,
            #   one line apart — the half-applied sweep at its smallest possible radius.
            'children(v) = { w : V | v &#8594; w }   (immediate successors)',
            'Reach(v)    = { w : V | Nonempty (Quiver.Path v w) }  (reachable from v)',
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
            'Lean&#8217;s set image &#8212; { d w | w &#8712; S }. &#8226; The two axioms pin '
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
            '  (_G : APG V) (d&#8321; d&#8322; : V &#8594; U),',
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
            '&#8704; (x : U) (hx : x &#8800; bot) (k : &#8469;),',
            '  val (scale^[k] x) = val x + k',
            'For any x &#8800; &#8869;, applying scale k times increases depth by exactly k.',
            'Proof: induction on k; val_scale applies at each step because '
            'scale^[n](x) &#8800; &#8869; follows from the induction hypothesis '
            'and finiteness of val(x).',
            '&#8226; This is a genuine lemma of &#167; III and it drives '
            'scale_iterate_unique_fp below. It is NOT what the cyclic case above uses: '
            'cyclic_decoration_eq_bot never forms scale^[k].',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: scale_iterate_unique_fp (ZeroParadox/Settheory/APG.lean §IV)',
        [
            '&#8704; (k : &#8469;) (hk : 0 < k) (x : U), scale^[k] x = x &#8594; x = bot',
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
            '  HasSelfCycle v &#8594; d v = bot',
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
        # ⚠ "Since V is a Fintype, funext closes..." credited the wrong hypothesis. `funext` is
        #   function extensionality - pointwise equality gives equality of the functions - and it
        #   needs nothing about finiteness. Finiteness is what the ACYCLIC case needs, for the
        #   descent on |Reach(v)|, which this page says two paragraphs earlier. Attaching it to
        #   funext credits the enabling hypothesis to the step that does not consume it (DC-32).
        'Every vertex in a finite APG is either cyclic or acyclic. The two cases are '
        'exhaustive and jointly establish d&#8321;(v) = d&#8322;(v) for every vertex v. '
        'Function extensionality then closes the global equality d&#8321; = d&#8322; from that '
        'pointwise agreement; finiteness is consumed earlier, by the acyclic case&#8217;s '
        'descent on |Reach(v)|, and plays no part in this last step.'))
    E.append(sp(6))

    # ── Section V: Scope and Purity ─────────────────────────────────────────────
    print('[build_zpj_afa_addendum] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Scope, Purity, and Open Questions', S['h1']),
        hr(),
    ]

    E.append(body(
        'decoration_unique establishes the <i>uniqueness</i> half of the property AFA '
        'asserts (an axiom — Remark R-J.A) for abstract DecorationUniverses over finite '
        'graphs. Two scope '
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
            # ⚠ BOTH clauses are modal, and the first fix reached only the first clause. Saying
            #   "no ZPSemilattice ℤ_[2] is DEFINED" one clause after correcting the sibling to
            #   REGISTERED is the half-applied sweep inside a single sentence — and § V's closing
            #   example builds exactly such a semilattice and discharges all four axioms over it,
            #   so `defined` is false on the modal reading the corpus fences twice.
            'ValBridge &#8484;_[2]. Note no ValuationStructure &#8484;_[2] is REGISTERED, nor '
            'any ZPSemilattice &#8484;_[2] &#8212; which is a fact about what is declared, not '
            'about what is possible: ZeroParadox/Valuation/Scale.lean &#167; V builds one and discharges all four axioms over it. '
            'ValBridge is the variant that drops the semilattice requirement while keeping the '
            'same four axioms.',
            'ZeroParadox/Settheory/APG.lean &#8212; APG, DecorationUniverse, val_iterate, '
            'scale_iterate_unique_fp, cyclic_decoration_eq_bot, '
            'acyclic_induction_step, decoration_unique',
            'All paths are repository-relative, in the public repository.',
        ]
    ))
    E.append(sp(4))

    E.append(label_box(
        'Axiom Footprint &#8212; measured per declaration, not asserted document-wide',
        [
            '[propext, Classical.choice, Quot.sound]',
            'propext          &#8212; propositional extensionality (standard in Lean 4)',
            # ⚠⚠ THIS LINE NAMED THE WRONG SOURCE AND THEREFORE THE WRONG MODALITY. It read
            #   "(Mathlib Finset and Fintype machinery)". Measured 2026-09-02 with
            #   `lake env lean`: `ValuationStructure` — a BARE TYPECLASS mentioning neither —
            #   carries [propext, Classical.choice, Quot.sound], and so does
            #   `instAddMonoidWithOneENat`, the instance the numeral `1` in `val x + 1` reaches
            #   for. The route is that numeral, and Scale.lean's `_VSlit`/`_VScast` pair proves
            #   it is THE route rather than one of several: respelling the successor as
            #   `((1 : ℕ) : ℕ∞)` and changing nothing else makes the class report no axioms.
            #   ⚠ WHY IT MATTERED MORE THAN A CITATION SLIP: the line below says "No ZP-specific
            #   axioms beyond", so attributing the cost to a library turned something REMOVABLE
            #   into something UNAVOIDABLE. `AxiomProfile.lean` § 0 warns about exactly this —
            #   *"PROVENANCE and NECESSITY are independent axes, and the first version of this
            #   heading conflated them"* — and the corrected text keeps them apart: the tainted
            #   INSTANCE is Mathlib's, the SPELLING that reaches for it is this framework's, and
            #   the dependence is accidental because a respelling clears it.
            'Classical.choice &#8212; AT LEAST THREE ROUTES, and they are not the same '
            'claim. (a) THE CLASS: the numeral `1` in val_scale needs Mathlib&#8217;s '
            'AddMonoidWithOne &#8469;&#8734; instance, choice-tainted at the INSTANCE '
            'level, so ValuationStructure carries the axiom as a bare typeclass before any '
            'theorem. (b) A DIRECT CALL: decoration_unique&#8217;s proof takes an edge out '
            'of a Nonempty via hw.some, and Nonempty.some IS Classical.choice &#8212; not '
            'inherited through packaging, invoked. (c) CARDINALITY: the termination measure '
            'runs on Set.ncard, and Set.ncard_lt_ncard and Set.ncard_pos are each '
            'independently choice-tainted. &#8212; And the OLD attribution could not have been right for a reason stronger than absence: Finset and Fintype each report [propext, Quot.sound], so neither has any choice to supply. Fintype IS a hypothesis of decoration_unique, printed in its own box above; what it buys is the termination measure, not the axiom.',
            'Quot.sound       &#8212; quotient soundness (standard in Lean 4)',
            '&#8226; ACCIDENTAL FOR THE CLASS, UNMEASURED FOR THE THEOREM &#8212; and the '
            'difference is the whole claim. Scale.lean&#8217;s _VSlit / _VScast pair '
            'respells route (a)&#8217;s numeral as ((1 : &#8469;) : &#8469;&#8734;) and '
            'nothing else, and the class then reports no axioms at all: that EXHIBITS a '
            'clean proof, which is the only thing that earns the word accidental. No such '
            'witness exists for decoration_unique, whose routes (b) and (c) are untouched by '
            'any respelling, and whose STATEMENT mentions ValuationStructure &#8212; so its '
            'type would carry the axiom even with a pristine proof. Its removability is '
            'therefore UNMEASURED, not established either way.',
            'No ZP-specific AXIOM is declared anywhere in this chain; the footprint above is '
            'what the Lean reports, not a commitment the framework makes.',
            'No Dependent Choice. No additional set-theoretic assumptions.',
        ]
    ))
    E.append(sp(4))

    E.append(remark_box(
        'Remark R-J.A &#8212; Relationship to Aczel\'s Anti-Foundation Axiom',
        [
            # ⚠⚠ THREE ERRORS IN ONE SENTENCE, and the corpus disagreed with it in three
            #   places. It read: "Aczel's decoration THEOREM ... states that every APG has a
            #   unique decoration into the universe of NON-WELL-FOUNDED sets."
            #   (1) It is an AXIOM. Aczel, ch. 1 p. 6: "The Anti-Foundation Axiom, AFA: Every
            #       graph has a unique decoration." The book's decoration THEOREM is Mostowski's
            #       Collapsing Lemma, and that one is about WELL-FOUNDED graphs.
            #   (2) Every GRAPH, not every APG. Accessibility and a point make a graph a
            #       *picture*; they are not hypotheses of AFA.
            #   (3) The universe of SETS, not of non-well-founded sets — the book's own worked
            #       example on pp.4-5 decorates with 0, {0} and 3, all well-founded.
            #   `CLAIMS.md:195` and `ZeroParadox/Settheory/APG.lean` already carried the correct
            #   statement with the same page numbers, and this document's own preamble calls it
            #   the Anti-Foundation AXIOM eight pages earlier. Ledger, Lean and book agreed with
            #   each other and disagreed with the rendered page.
            'Aczel&#8217;s ANTI-FOUNDATION AXIOM (Non-Well-Founded Sets, CSLI 1988, ch. 1 '
            'p. 6) states that every GRAPH has a unique decoration into the universe of sets '
            '&#8212; an axiom, not a theorem, and quantified over graphs rather than over '
            'accessible pointed ones. (The book&#8217;s decoration THEOREM is Mostowski&#8217;s '
            'Collapsing Lemma, for WELL-FOUNDED graphs.) '
            'The result here is not a re-proof of Aczel\'s axiom by different methods. '
            'The objects are different: Aczel\'s target is a specific set-theoretic '
            'universe; the target here is any type carrying ValuationStructure and a '
            'collect operation, with no set-membership semantics required. '
            'The contribution is the generalisation: decoration uniqueness holds for any '
            'abstract DecorationUniverse satisfying the depth-measure axioms, independently '
            'of set-theoretic content. Whether the existence half of Aczel\'s axiom '
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
