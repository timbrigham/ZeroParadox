"""
Zero Paradox — ZP-J: Executability of Self-Reference PDF Builder
Version 2.8 | September 2026
v2.8: CC-1 STATUS SYNC (Tim, 2026-09-13: everything in one arc). "CC-1 derived / closed / no longer a freestanding commitment" collapsed two readings: cc1_derived proves the CONDITIONAL (a state sequence starting at a Quine atom starts at bottom), and with t_exec_iff the converse holds, so the starting-point choice is RESTATED through the Quine-atom role, not forced; every ZP-A lattice carries AFAStructure trivially. Every site now keeps both halves, matching ZP-J v2.7. Here: the Open Items row 'ZP-A CC-1 cross-check' is RESOLVED (ZP-A v1.22 matches), and the result box is titled 'Theorem CC-1, Conditional Form' rather than 'Theorem CC-1 (Derived)'. ROUND 1 (editorial + claim-review + adversary FAIL-BEDROCK; prior-art PASS): the sync first gave the wrong REASON for "not forced" ("every ZP-A lattice carries AFAStructure trivially, so ..."), which does not follow; the reason is that a valid state sequence can start above bottom (T2 fixes only bottom <= S0; an example on OntologicalStates in OntBridge.lean). Also 'T-EXEC, J1, CC-1: proved axiom-free' collapsed CC-1 to its proved half and now reads 'CC-1 in conditional form'; the traceability row reads 'CC-1, conditional form'; the result box is a Corollary (a one-step rewrite of T-EXEC, R-NAMING), not a Theorem. GATE ROUND 2 (ordinary, carried): the 'not forced' reason needs its scope - on a ONE-point lattice every sequence starts at bottom, so the countermodel is stated for a lattice with a second point, and the OntBridge.lean example now also shows the start is not a Quine atom. The p1, section I and callout reasons now state that scope.
v2.7: THREE BEDROCK REMEDIATED IN ONE ROUND (ZPJ-ITER, ZPJ-AXFREE, ZPJ-AFA-THM) - closure is the gates' verdict, not this entry's. (1) Section X.II said composing the decoration equation around a cycle gives d(v) = scale^k(d(v)); collect reduces to scale only through collect_singleton, i.e. only at single-child vertices, and cyclic_decoration_eq_bot never forms scale^[k] - it chains collect_val_ge and path_val_chain as INEQUALITIES (read off the elaborated proof term, which also consumes val_finite_of_ne_bot and neither val_iterate nor scale_iterate_unique_fp). The traceability register grounded it in exactly those two unused lemmas; both now name what the proof consumes, wording copied from ZP-J AFA Addendum IV.1. kCycle_node_eq_bot is marked as taking its cycle equation as a hypothesis. Section X.III's "the valuation argument closes the equation" (Tim's approved minimal fix) now says the valuation bound forces the bottom. (2) Six traceability cells said "axiom-free" and each was measured false with lake env lean on 2026-09-13: scale_unique_fp, toAbstractSelfApp, instNatInfZPS, instNatInfVal and cyclic_decoration_eq_bot report [propext, Classical.choice, Quot.sound], and singleton_from_unique_witness reports [propext, Quot.sound] - the last sat beside its own "Set extensionality (propext)" grounding. The other axiom-free cells were re-measured and hold (t_exec, j1_quine_join_identity, cc1_derived, bot_is_quine_atom, t_exec_iff, bot_unique, instOntSelfApp). (3) AFA was called a theorem about APGs. Aczel ch. 1 p. 6 (opened): "The Anti-Foundation Axiom, AFA: Every graph has a unique decoration", with "every apg is a picture of a unique set" listed as a consequence. Section II and Section X.I now state the axiom; the Section VI chain summary and the Section X preamble, which both said this document proves "the full AFA decoration uniqueness theorem" and were found by reading the RENDERED text after the first rebuild, now say it proves the uniqueness clause over abstract DecorationUniverses; and the Section X callout calls decoration_unique the analogue of that clause. EDITORIAL ROUND 1 (FAIL-BEDROCK, 1 bedrock + ordinaries) folded into the same version: B-1, "ZP-J's version of this theorem" survived one sentence after the rewrite and now named either AFA or Mostowski as a theorem ZP-J restates - it names ZP-J's uniqueness result; Mostowski's Collapsing Lemma is cited at p. 4 in Aczel's own wording, not as "the decoration theorem"; "only when every vertex has exactly one child" (this version's own overstatement) is now the sufficient condition - a singleton child image; the callout named collect_singleton, which decoration_unique never consumes, and said "characterises" where only sufficiency is proved; "Z_[2] cannot be a formal instance because it is a ring" is refuted by Scale.lean section V's elaborated existence proof and now says no instance is REGISTERED, with the Open Items row restated to match; field counting in Section VIII names the two laws; X.II introduces p and marks path_val_chain private. EDITORIAL ROUND 2 (FAIL-BEDROCK in the companion; ordinaries here): "the uniqueness clause of AFA" at Sections VI and X identified ZP-J's result with AFA's own clause and is now an analogue; Remark R-J.1 and the T-EXEC traceability row credited quine_unique, which t_exec does not use - it uses bot_self_mem and the uniqueness half of IsQuineAtom q; "bottom in bottom, i.e. bottom = {bottom}" reversed to the true direction; decoration uniqueness scoped to DecorationUniverses in the page-1 summary and the endnote. EDITORIAL ROUND 3 (FAIL-BEDROCK, claim-revalidation round): Sections III.II, III.III and VI argued that AFAStructure is an obligation a lattice might fail - "if it cannot, it is not genuinely AFA-grounded", "concrete lattices must earn their AFA status", the content of bottom = {bottom} "now lives in bot_self_mem". Measured false: every ZPSemilattice carries AFAStructure (trivialSelfApp via abstractSelfApp_always_inhabited, then toAFAStructure; the reviewer also built selfMem := (. = bot) directly, axiom-free). Restated to the corpus's CC-2 convention (Wheel.lean, 2026-08-02; Tim: "bot is a role not a fixed value"): the literal set identity is a ZF+AFA statement and is never asserted of a carrier, because on a carrier it is a cross-type equality; the Lean carries the ROLE, as a hypothesis, and T-EXEC identifies its occupant. The true half of III.III is kept - a class field adds nothing to the purity report where a freestanding axiom would. Also CC-1's starting-point hypothesis restored at the abstract, Section I, V.II and the Open Items rows. ADVERSARY ROUND 4 (FAIL-BEDROCK, fix authored by the adversary, D1): (A-1) the abstract, Section VII and the Open Items row said ZP-J shows Aczel's use of Dependent Choice is unnecessary "for the self-membership case" and marked the question CLOSED. Measured false as a premise: J_self is defined by comprehension on selfMem, no set-continuous operator is defined, and J_self_is_largest is the instance of S subset {x | P x} for an arbitrary predicate, elaborated axiom-free with no uniqueness; Aczel's DC step (printed pp. 76-77, proof of 6.5(2)) passes from a class to a set and has no counterpart in the encoding. Section VII now states what the Lean measures (no Classical.choice) and that it does not reach Aczel's question; the Open Items status is NOT ADDRESSED; the "DC-free" labels on Lean results now say "no Classical.choice". Aczel's Theorem 6.5 is quoted as stated (largest fixed point; part (2) for classes X subset PhiX), and the Phi/Sigma glyph mix is gone. (B-1, corroborating editorial round 4) Section III.II located an instance's content in "a witness that its selfMem differs from equality with bottom"; in every AFAStructure selfMem x iff x = bot, axiom-free, so it now points to selfMem_determines_singleton and to the map selfMem is defined from. TIM'S CALLS ON ROUND 4 (carrier): (1) A-1 retraction accepted as authored. (2) CC-1 restated as an equivalence (editorial O-4, adversary routing): given AFAStructure, "a state sequence starts at a Quine atom" and "it starts at bottom" are the same condition - cc1_derived one way, t_exec_iff the other, the adversary measured the biconditional axiom-free - so CC-1's starting point is restated through the role, not forced; "CLOSED" became "RESTATED - not forced" at the abstract, Section I and its callout, Section V, VI.III, the traceability row, the Open Items rows and the endnote. Also the Section IV.III box now cites t_exec_triple_iff for the three-way statement (both reviewers). ROUND-4 ORDINARY RESIDUE FOLDED IN BEFORE THE LAST BEDROCK ROUND (same CC-2 role class the gates graded bedrock twice): Section II.III no longer says a lattice "grounded in ZF+AFA" satisfies the fields - every ZPSemilattice does; R-J.0 no longer says CIC lacks membership - the statement is ill-typed on a carrier and Mathlib's ZFSet satisfies Foundation (ZFSet.mem_irrefl); R-J.1 "purely order-theoretic" -> uses neither order nor join (t_exec is (hq.2 bot bot_self_mem).symm); the Quine-atom condition is "the self-containment role", not "set-theoretic"; Section VI.II names ZP-A's CC-2 box rather than "a narrative comment"; full path for SelfApp.lean in Section VIII; the Section X.III zero-side/infinity-side reading DELETED (unmeasured, and cyclic vertices receive bottom, whose valuation is top, so it pointed the opposite way). ADVERSARY ROUND 5 (FAIL-BEDROCK, D1): Sections VI.III and VIII said the abstraction chain "reduces the axiom load of AFAStructure" and asked for "something more primitive". The arrows run the other way: toAbstractSelfApp and toAFAStructure are instances, so ValuationStructure is the STRONGEST hypothesis in the chain; every ZPSemilattice carries AbstractSelfApp and AFAStructure, while valuationStructure_forces_infinite makes any nontrivial ValuationStructure carrier infinite (a scratchpad probe also proved no ValuationStructure on OntologicalStates). Both sites now say the chain derives the laws from stronger structures, VIII.I no longer says AbstractSelfApp "proves" its own unique_fp field, VIII.IV states the direction with the theorem, and IX no longer attributes the two-element obstruction to val_scale alone (OntBridge.lean: the obstruction is joint). TWO-POLE AUDIT RESTORATIONS (fresh read-only auditor after R-TWOPOLE was re-keyed; Tim: restore all): eight fixes in this arc and the wheel arc had kept one chart of a two-chart reading. Here: (L1) the Section X.III sentence from Tim's APG.lean Engineer's Take is back as a coincidence of two charts - a cyclic vertex receives the order-theoretic zero bottom AND its valuation is top (cyclic_decoration_eq_bot with val_bot, now also an example in APG.lean) - one-way, and fenced from AFA sets by Aczel Ex. 1.5; round 4's deletion reason read bottom in the valuation chart only. (L2) CC-2 is ZP-A's FORCED Metatheoretic Commitment with its proved half (quineHost_not_wellFounded, zfSet_no_quine_bottom) and its argued half, not just "argued". (L3) Section VI.II no longer merges the ZF+AFA theorem Q = {Q} (Aczel Ex. 1.3) into the commitment that the framework's bottom is that set (Wheel.lean's "do not retire the equation"). (L4) the Section IV.III three-language box keeps the set-theory chart. Also: the AFAStructure box glossed selfMem as "contains itself as a member"; under AFA 0* = {empty, 0*} is self-membered and is not Q (Aczel Ex. 1.5), so the set-level reading is x = {x}; R-J.0's "never" (a Membership L L instance can be declared) is now "none in scope"; the kCycle_node_eq_bot row carries k >= 1.
v2.6: PHANTOM AXIOM REMOVED (bedrock). The rendered DecorationUniverse box published THREE laws; APG.lean declares exactly TWO. The middle one, collect_ext ("collect respects set equality"), does not exist anywhere in the corpus, and §X cited it as the MECHANISM for acyclic_induction_step. The real proof shows the two child image sets equal (Set.ext) and rewrites — ordinary congruence, free from equality itself, consuming no class axiom; an interface law would instead be a premise every implementer must supply, so the text billed the proof for a cost it never pays. Also struck the side condition "x != bot" from collect_val_ge, which the Lean statement does not carry (a published axiom with an extra premise is weaker in print than what is proved). The box is now copied verbatim from build_zpj_afa_addendum.py, which already transcribes the Lean literally rather than glossing it.
v2.5: Rendered Lean citations synced to post-reorg files/namespaces the v2.4 pass missed: ZPJ.lean -> SetTheoryAFA.lean; ZeroParadox.ZPJ.* -> ZeroParadox.* (per-layer namespaces flattened); ZPE.da2_bottom_characterization -> da2_bottom_characterization (now in Snap.lean).
v2.4: Rendered Lean-file citations synced to post-reorg basenames (ZPJ_AczelConn.lean -> AczelConn.lean, etc.). Docstring changelog above kept as the historical record.
v2.2: Remaining rendered self-version refs removed — §VII preamble "Version 2.0 extends", v2.0/v1.0 register cells, validation "v2.0:" line (C1 sweep). Fixed null glyphs: scaleᵏ (&#7503; modifier-k → <sup>k</sup>) and a garbled ≤ subscript.
v2.1: Version changelog removed from preamble; version stripped from section headers and endnote.
v2.0: Four new sections added — Section VII (Aczel DC-free connection),
      Section VIII (abstraction chain: ValuationStructure → AbstractSelfApp →
      AFAStructure), Section IX (concrete instances: ℕ∞ and OntologicalStates),
      Section X (APG decoration uniqueness). All new content proved sorry-free in
      Lean 4 across ZPJ_AczelConn.lean, ZPJ_SelfApp.lean, ZPJ_Scale.lean,
      ZPJ_Model.lean, ZPJ_OntBridge.lean, ZPJ_APG.lean.
v1.2: Minor wording fix — "not an asserted coincidence" removed from preamble.
v1.1: Remark R-J.0 added — CIC encoding scope. AFAStructure concrete instances
      item CLOSED — ZP-K provides machinePhaseAFA.
v1.0: Initial release — Theorem T-EXEC; all ZPJ.lean theorems axiom-free.
"""

import os
from zp_utils import *

VERSION = '2.8'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_Self_Reference.pdf')
    doc = make_doc(out_path,
                   'ZP-J: Executability of Self-Reference',
                   'ZP-J: Executability of Self-Reference',
                   'Version ' + VERSION)
    E = []

    print('[build_zpj] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-J: Executability of Self-Reference', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document establishes Theorem T-EXEC (Executability of Self-Reference): in any '
        'ZP-A join-semilattice carrying the AFAStructure typeclass, whatever fills the Quine-atom '
        'role &#8212; the lattice-level encoding of the set Q = {Q} of ZF+AFA (Anti-Foundation '
        'Axiom) &#8212; is provably the bottom element &#8869;. This bridges the set-theoretic and '
        'order-theoretic layers of the framework at the level of that role; the set identity '
        'itself stays in ZF+AFA. CC-1 from ZP-A, which stated "S&#8320; = &#8869;" as a modelling '
        'commitment, is restated: given the typeclass, starting at a Quine atom and starting at &#8869; '
        'are the same condition. It is not forced: on a carrier with a second point a valid state '
        'sequence can start elsewhere (ZeroParadox/Settheory/OntBridge.lean).'))
    E.append(body(
        'This layer extends the core T-EXEC result in four directions: it identifies the set of '
        'self-containing elements as {&#8869;} with no Classical.choice, and states why that does not '
        'bear on Aczel\'s question about Dependent Choice (Section VII); '
        'it generalises the AFAStructure typeclass into an abstraction chain reaching down to '
        'a pure valuation structure (Section VIII); it instantiates that chain on two concrete '
        'types (Section IX); and it proves global decoration uniqueness, into abstract '
        'DecorationUniverses, for finite accessible '
        'pointed graphs (Section X). All results are sorry-free in Lean 4.',
        style='bodyI'))
    E.append(hr())

    print('[build_zpj] Building Section I...')
    E += [
        Paragraph('Section I: The Open Question &#8212; CC-1 as a Modelling Commitment', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. CC-1 in ZP-A', S['h2']))
    E.append(body(
        'ZP-A Conditional Claim CC-1 states: if the state sequence is initialised at &#8869;, '
        'then &#8869; &#8804; S(n) for all n. This follows trivially from T2 (&#8869; is the '
        'global minimum), so its formal content is essentially: we are choosing &#8869; as the '
        'initial state S&#8320;.'))
    E.append(body(
        'The label "Conditional Claim" (CC) marks this as a modelling commitment &#8212; an '
        'explicit choice not derivable from the axioms A1&#8211;A4 alone. ZP-A\'s axioms give us '
        'a semilattice with a bottom element. They do not say which instantiation of the '
        'semilattice should start at that bottom. CC-1 asserts: ours does. This is '
        'well-motivated, but it is a choice.'))
    E.append(body(
        'The question ZP-J investigates: is this choice forced? Is there a structural reason &#8212; '
        'derivable from the framework\'s foundational commitments &#8212; that any well-grounded '
        'instantiation of ZP-A must begin at &#8869;? The answer is that the choice is restated: if the '
        'lattice carries AFAStructure, a sequence starts at a Quine atom exactly when it starts at &#8869; '
        '(Section V). It is not forced: on a carrier with a second point a valid state sequence starts '
        'above &#8869;, at a point that is not a Quine atom (ZeroParadox/Settheory/OntBridge.lean). The commitment to start there remains; it is now '
        'expressed through the Quine-atom role rather than as a bare choice of element.'))

    E.append(Paragraph('II. The Implicit Identification', S['h2']))
    E.append(body(
        'ZP-E\'s DA-1 Path 1 already states: &#8869; = {&#8869;} (Quine atom, ZF+AFA). This '
        'identification &#8212; the bottom element is the unique self-containing set under AFA &#8212; '
        'was present informally but never formally bridged to CC-1. It appeared as motivation for '
        'why &#8869; is the right starting point, not as a derivation of it.'))
    E.append(body(
        'The gap: ZP-A\'s lattice order is abstract (defined by axioms A1&#8211;A4). AFA is a '
        'set-theoretic axiom. There is no automatic connection between "x is self-containing" '
        'and "x is the lattice bottom." Connecting them requires a bridge &#8212; and that bridge '
        'was the missing piece. ZP-J provides it.'))

    E.append(callout(
        'Open question entering ZP-J: Is CC-1 (S&#8320; = &#8869;) forced by the framework\'s '
        'foundational structure, or is it an independent modelling choice? '
        'If forced, what is the structural reason? '
        'Answer: restated (ZP-J t_exec_iff), and not forced (a countermodel). Given an AFAStructure, "starts at a Quine '
        'atom" and "starts at &#8869;" are equivalent (t_exec_iff), so the starting point is named '
        'by its role; the choice to start there remains, since on a carrier with a second point a valid sequence starts elsewhere. The AFA identification &#8869; = {&#8869;} is the ZF+AFA reading of the '
        'Quine-atom role the typeclass encodes; the Lean states the role, not the set identity.',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: AFA Machinery &#8212; Self-Membership and the Quine Atom', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The Anti-Foundation Axiom', S['h2']))
    E.append(body(
        'Standard set theory (ZF) includes the Foundation Axiom: every non-empty set S contains '
        'an element disjoint from S. A consequence is that no set can contain itself: x &#8712; x '
        'is impossible in ZF. This rules out self-referential sets by fiat.'))
    E.append(body(
        'The Anti-Foundation Axiom (AFA, Aczel 1988, ch. 1 p. 6) replaces Foundation with an '
        'axiom asserting existence and uniqueness: every graph has a unique decoration. As a '
        'consequence, every accessible pointed graph (APG) is a picture of a unique set. '
        'Under AFA, self-containing sets are not only possible but '
        'uniquely characterised. The resulting theory ZF+AFA is consistent and expressive &#8212; '
        'it is the natural set-theoretic home for fixed-point and self-referential structures.'))

    E.append(Paragraph('II. The Quine Atom', S['h2']))
    E.append(body(
        'Under AFA, the equation x = {x} has a unique solution. This solution is called the '
        '<i>Quine atom</i>, denoted Q. Q is the unique set that contains itself as its sole member: '
        'Q = {Q}. It is not the empty set (&#8709; = {} contains nothing); it is not any '
        'well-founded set (those cannot contain themselves). Q is the minimal non-trivial AFA '
        'set &#8212; it contains exactly one thing, and that thing is itself.'))
    E.append(body(
        'The AFA uniqueness guarantee is the key property: there is at most one Quine atom. '
        'Any two self-containing elements are equal. This means the self-membership property '
        'uniquely identifies an element &#8212; a fingerprint that belongs to exactly one object '
        'in the universe.'))

    E.append(axiom_box(
        'AFA Uniqueness (AFAStructure.quine_unique)',
        [
            'For any type L with AFA structure: if x, y &#8712; L both satisfy selfMem(x) and '
            'selfMem(y), then x = y.',
            'Informally: the Quine atom is unique. Self-containment is a property held by at '
            'most one element of any AFA-structured type.',
            'Lean: AFAStructure.quine_unique &#8212; encoded as a typeclass field, not a theorem, '
            'because AFA is a foundational axiom and cannot be derived from type-theoretic '
            'principles alone for an arbitrary selfMem. It is a hypothesis every theorem here '
            'carries, and (Section III.II) any lattice can meet it by a trivial choice of selfMem.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. Self-Membership as a Lattice Predicate', S['h2']))
    E.append(body(
        'In ZP-J, the AFA machinery is abstracted minimally. We do not need the full apparatus '
        'of accessible pointed graphs, bisimulation, or set decoration. We need only two things: '
        'a predicate <i>selfMem</i> on the lattice elements, and the guarantee that it is held '
        'by at most one element (quine_unique). The third structural field &#8212; bot_self_mem &#8212; '
        'is where the bridge is built.'))
    E.append(body(
        'The AFAStructure typeclass in SetTheoryAFA.lean captures exactly this. Its three fields are '
        'sufficient to derive T-EXEC with no additional axioms. The full AFA machinery '
        '(APGs, bisimulation, decoration) motivates the fields; the formal derivation requires '
        'only the fields themselves, and every ZPSemilattice supplies them (Section III.II).'))

    print('[build_zpj] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: AFAStructure &#8212; The Structural Bridge', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The Three Fields', S['h2']))
    E.append(body(
        'The AFAStructure typeclass for a ZP-A semilattice L has three fields. The first two '
        'encode standard AFA properties. The third is the bridge.'))

    E.append(def_box(
        'AFAStructure Typeclass (SetTheoryAFA.lean &#167; I)',
        [
            'class AFAStructure (L : Type*) [ZPSemilattice L] with:',
            '(1) selfMem : L &#8594; Prop  '
            '&#8212; the self-containment predicate. Read in ZF+AFA, selfMem(x) is x = {x} (x is its '
            'own sole member), not bare membership x &#8712; x: under AFA the set 0* = {&#8709;, 0*} '
            'contains itself and is not Q (Aczel 1988, Example 1.5), so the uniqueness below would '
            'fail for membership.',
            '(2) quine_unique : &#8704; x y : L, selfMem(x) &#8594; selfMem(y) &#8594; x = y  '
            '&#8212; AFA uniqueness. At most one element of L plays the self-containment role.',
            '(3) bot_self_mem : selfMem(&#8869;)  '
            '&#8212; the bridge field. The bottom element of the lattice is self-containing. '
            'This encodes the ROLE that &#8869; = {&#8869;} describes in ZF+AFA; the set identity '
            'itself compares an element of L with a set of elements of L, so it is not stated here.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. What bot_self_mem Says', S['h2']))
    E.append(body(
        'bot_self_mem is the single structural claim that connects the order-theoretic world '
        '(ZP-A\'s lattice) to the set-theoretic world (AFA). It says: the bottom element &#8869; '
        'of the lattice is self-containing &#8212; it satisfies selfMem(&#8869;).'))
    E.append(body(
        'In set-theoretic terms, within ZF+AFA: &#8869; = {&#8869;}, so in particular '
        '&#8869; &#8712; &#8869;. This is the identification that ZP-E\'s DA-1 Path 1 invokes '
        'informally. ZP-J encodes the role it describes as a typeclass field, so every result '
        'that uses it states it as a hypothesis rather than leaving it as narrative motivation.'))
    E.append(body(
        'Supplying the field is not a test a lattice can fail. Every ZPSemilattice carries an '
        'AFAStructure: take the constant-bottom self-application trivialSelfApp '
        '(abstractSelfApp_always_inhabited, ZeroParadox/Computability/SelfApp.lean &#167; V) and pass it '
        'through the instance toAFAStructure, so that selfMem(x) holds exactly when x = &#8869;. '
        'Carrying the structure therefore says nothing about a particular lattice. The class '
        'encodes a ROLE, and T-EXEC identifies that role\'s occupant. The selfMem field is itself '
        'forced in every instance: selfMem_determines_singleton (Section VII.III) gives '
        '{x : L | selfMem(x)} = {&#8869;} for any AFAStructure lattice L. Where a concrete instance '
        'carries content, it is in the map selfMem is defined from (a self-application or a scale, '
        'Section VIII.IV), never in selfMem.'))
    E.append(remark_box(
        'Remark R-J.0 &#8212; CIC Encoding and the AFA Distinction',
        [
            'In the MachinePhase concrete instance (ZP-K), selfMem is defined as '
            'selfMem x := x = &#8869;. With this definition, bot_self_mem is proved by rfl: '
            '&#8869; = &#8869; holds by reflexivity.',
            'This is the CIC-compatible encoding of AFA self-containment. In Lean 4 (based on '
            'the Calculus of Inductive Constructions), the set-theoretic statement &#8869; &#8712; &#8869; '
            '&#8212; meaning &#8869; literally contains itself as a member under ZF+AFA &#8212; is not '
            'well-typed on a carrier: x : L is a member of a Set L, and no membership relation between '
            'two elements of L is in scope, so &#8869; &#8712; &#8869; does not elaborate. '
            'Mathlib\'s own model of ZF sets satisfies Foundation (ZFSet.mem_irrefl: no set is a member '
            'of itself). The '
            'encoding selfMem x := x = &#8869; captures the structural role: "self-containing" '
            'means "equals the bottom element." The Lean proof compiles by rfl because '
            'self-containing is defined as equality with &#8869;.',
            'This is a structural analogy, not a set-theoretic derivation from ZF+AFA. The '
            'full set-theoretic content of AFA &#8212; that &#8869; literally contains itself as a '
            'member of the AFA universe &#8212; is not present in the Lean proof. What the typeclass '
            'encodes is the structural consequence: there is a unique element playing the Quine '
            'role, and &#8869; is that element.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. Why a Typeclass Field Rather than a Freestanding Axiom', S['h2']))
    E.append(body(
        'In the stub version of SetTheoryAFA.lean, the bridge was a freestanding axiom: '
        'ax_j1_quine_join_identity. It stated directly that the Quine atom satisfies the '
        'join-identity. This compiled, but the purity check showed T-EXEC depending on '
        'ax_j1_quine_join_identity &#8212; a named axiom floating outside any typeclass.'))
    E.append(body(
        'A freestanding axiom is a global assertion the kernel accepts without proof, and it '
        'appears in the purity report of every theorem that uses it. A typeclass field adds '
        'nothing to that report: T-EXEC depends on no axioms. What the field buys is honesty of '
        'scope, not content &#8212; it is a hypothesis each theorem carries, and (Section III.II) '
        'every lattice can supply it trivially.'))
    E.append(callout(
        'The distinction: a freestanding axiom says "trust me, this is true," and the purity check '
        'records it. A typeclass field says "given this structure," and every theorem is '
        'conditional on it. ZP-J uses the second. The literal set identity (&#8869; = {&#8869;}) '
        'stays in ZF+AFA; the Lean carries only the role it describes.',
        bg=SLATE_LITE, border=SLATE
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Theorem T-EXEC &#8212; The Quine Atom is Bottom', S['h1']),
        hr(),
    ]

    E.append(result_box(
        'Theorem T-EXEC &#8212; Executability of Self-Reference',
        [
            'Statement: Let L be a ZP-A semilattice with AFAStructure. '
            'If q : L is a Quine atom (selfMem(q) and q is unique among self-containing '
            'elements), then q = &#8869;.',
            'Lean: ZeroParadox.t_exec &#8212; proved in SetTheoryAFA.lean. '
            'Purity: does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('I. The Proof', S['h2']))
    E.append(body(
        'The proof of T-EXEC is immediate from the typeclass fields. It has three steps:'))
    E += [
        li('hq.2 states: every self-containing element of L equals q. '
           '(This is the uniqueness half of IsQuineAtom q.)'),
        li('AFAStructure.bot_self_mem states: &#8869; is self-containing. '
           '(This is the bridge field &#8212; the role &#8869; = {&#8869;} describes in ZF+AFA.)'),
        li('Applying hq.2 to &#8869; using bot_self_mem gives: &#8869; = q. '
           'By symmetry: q = &#8869;. QED.'),
        sp(4),
    ]
    E.append(body(
        'The entire proof is one line in Lean 4: '
        '<i>(hq.2 bot AFAStructure.bot_self_mem).symm</i>. '
        'No appeal to the join operation. No bridge axiom. No DA-2. '
        'Just AFA uniqueness applied at &#8869;.'))
    E.append(remark_box(
        'Remark R-J.1',
        [
            'The proof does not use da2_bottom_characterization (from ZP-E). '
            'That result &#8212; "(&#8704; x, join S x = x) &#8596; S = &#8869;" &#8212; is used in '
            'the derived theorem J1 (Section V), but T-EXEC itself uses neither the order nor the join: '
            'it uses only bot_self_mem and the uniqueness half of its own hypothesis '
            'IsQuineAtom q (not the quine_unique field).',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. IsQuineAtom bot', S['h2']))
    E.append(body(
        'A corollary of T-EXEC is that &#8869; itself is a Quine atom. This is the converse '
        'direction: not only does the Quine atom equal &#8869; (T-EXEC), but &#8869; equals '
        'the Quine atom (bot_is_quine_atom).'))
    E.append(result_box(
        'Proposition &#8212; bot_is_quine_atom',
        [
            'In any AFAStructure lattice L: IsQuineAtom(&#8869;).',
            'Proof: &#8869; is self-containing by bot_self_mem. Any other self-containing '
            'x satisfies x = &#8869; by quine_unique(x, &#8869;, selfMem(x), bot_self_mem).',
            'Lean: ZeroParadox.bot_is_quine_atom &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. The Full Biconditional', S['h2']))
    E.append(body(
        'Combining T-EXEC and bot_is_quine_atom yields the full biconditional: '
        'IsQuineAtom(q) &#8596; q = &#8869;. Being the Quine atom and being the bottom element '
        'are the same property, stated as a self-containment role (the lattice encoding of the ZF+AFA set '
        'Q = {Q}) and in order-theoretic language respectively.'))
    E.append(result_box(
        'Theorems t_exec_iff and t_exec_triple_iff &#8212; Full Equivalence',
        [
            'For any q : L in an AFAStructure lattice:',
            't_exec_iff: IsQuineAtom(q) &#8596; q = &#8869;.',
            't_exec_triple_iff: IsQuineAtom(q) &#8596; (q = &#8869; &#8743; &#8704; x : L, join q x = x).',
            'The three conditions are mutually equivalent: Quine atom (the self-containment role, '
            'encoding the set-theoretic Q = {Q}), '
            'bottom element (order-theoretic), and join-identity element (algebraic). '
            'They are three formulations of one structural role.',
            'Lean: ZeroParadox.t_exec_iff, ZeroParadox.t_exec_triple_iff &#8212; do not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Derived Results &#8212; J1, and CC-1 Restated', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. J1 &#8212; QuineJoinIdentity (Derived)', S['h2']))
    E.append(body(
        'In the initial stub of SetTheoryAFA.lean, the claim "the Quine atom satisfies the join-identity" '
        'was stated as a freestanding axiom (ax_j1_quine_join_identity). ZP-J replaces it with '
        'a theorem.'))
    E.append(result_box(
        'Theorem J1 &#8212; QuineJoinIdentity (formerly Axiom AX-J1)',
        [
            'In any AFAStructure lattice L, if q is the Quine atom, then &#8704; x : L, join q x = x.',
            'Proof: q = &#8869; by T-EXEC. Then join q x = join &#8869; x = x by A4 (bot_join, ZP-A). &#10003;',
            'Status: DERIVED THEOREM. Was axiom ax_j1_quine_join_identity in the stub &#8212; '
            'now proved from T-EXEC + ZP-A A4. No freestanding axiom remains.',
            'Lean: ZeroParadox.j1_quine_join_identity &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. CC-1 Restated', S['h2']))
    E.append(body(
        'cc1_derived proves: if the initial state S&#8320; of a state sequence is a Quine atom Q, '
        'then S&#8320; = &#8869;. By t_exec_iff the converse holds as well, since &#8869; is a Quine '
        'atom. So "starts at a Quine atom" and "starts at &#8869;" are the same condition, and '
        'CC-1\'s choice of starting point is restated in terms of the Quine-atom role, not '
        'eliminated.'))
    E.append(result_box(
        'Corollary CC-1, Conditional Form &#8212; cc1_derived',
        [
            'Let L be an AFAStructure lattice. Let S : &#8469; &#8594; L be a state sequence '
            '(ZP-A D3) and Q : L a Quine atom. If S(0) = Q, then S(0) = &#8869;.',
            'Proof: S(0) = Q (hypothesis). Q = &#8869; by T-EXEC. Therefore S(0) = &#8869;.',
            'Starting at Q and starting at &#8869; are not two choices &#8212; with t_exec_iff they '
            'are the same condition. The commitment to start there is not removed; it is stated as '
            'starting in the Quine-atom role.',
            'Lean: ZeroParadox.cc1_derived &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. Uniqueness of the Bottom Role', S['h2']))
    E.append(body(
        'A further consequence is algebraic uniqueness: in any ZP-A semilattice (without even '
        'requiring AFA structure), at most one element can satisfy the join-identity. '
        'This is a clean corollary of da2_bottom_characterization (ZP-E).'))
    E.append(result_box(
        'Theorem &#8212; bot_unique',
        [
            'For any ZP-A semilattice L (no AFA required): if x, y : L both satisfy '
            '&#8704; z, join x z = z and &#8704; z, join y z = z, then x = y.',
            'Proof: da2_bottom_characterization gives x = &#8869; and y = &#8869;. Therefore x = y.',
            'Lean: ZeroParadox.bot_unique &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section VI...')
    E += [
        hr(),
        Paragraph('Section VI: Implications &#8212; What Was the Commitment?', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. The Remaining Foundation', S['h2']))
    E.append(body(
        'T-EXEC and its corollaries carry zero freestanding axioms in the Lean 4 purity check. '
        'The entire derivation traces to the fields of two typeclasses: ZPSemilattice (from ZP-A) '
        'and AFAStructure (new in ZP-J). No standalone axiom statement appears anywhere in the '
        'SetTheoryAFA.lean proof obligations.'))
    E.append(body(
        'The foundational commitments are the typeclass fields themselves. In ZPSemilattice: '
        'A1&#8211;A4 (the semilattice axioms). In AFAStructure: selfMem (a predicate), '
        'quine_unique (AFA uniqueness), and bot_self_mem (the bridge). They are not axioms '
        'floating in the ambient theory &#8212; they are hypotheses every theorem here carries. '
        'They are not facts about any particular lattice: every ZPSemilattice supplies them '
        'trivially (Section III.II).'))

    E.append(Paragraph('II. Where the Philosophy Lives Now', S['h2']))
    E.append(body(
        'The philosophical content of &#8869; = {&#8869;} is not in the Lean. It lives in ZP-A as '
        'CC-2 (Self-Containment of &#8869;), a Forced Metatheoretic Commitment with two halves: that '
        'any host of a self-membered bottom is not well-founded is proved (quineHost_not_wellFounded, '
        'zfSet_no_quine_bottom, ZeroParadox/Settheory/QuineHost.lean), and that a unique Quine atom is '
        'the right requirement is argued. It lives too in ZP-E\'s DA-1 Path 1 (one '
        'of three informal arguments for instantiation as execution), and in ZF+AFA it remains a '
        'set-theoretic identity. What ZP-J adds is the ROLE that identity describes, stated as the '
        'field bot_self_mem, and a proof (T-EXEC) that whatever fills that role is &#8869;.'))
    E.append(body(
        'Because every lattice can fill the role trivially, carrying AFAStructure is not evidence '
        'that &#8869; = {&#8869;} holds of a lattice. In ZF+AFA the set Q = {Q} exists and is unique, '
        'a consequence of the axiom (Aczel 1988, Example 1.3); identifying the framework\'s &#8869; with '
        'that set is the commitment (ZP-E, Remark R-AFA). The role, stated as a hypothesis '
        'where any reader can see it, is what the Lean checks.'))

    E.append(Paragraph('III. The Formal Chain', S['h2']))
    E.append(body(
        'The derivation chain entering ZP-J had one remaining gap: CC-1 was a committed '
        'starting point, not a derived one. Sections I&#8211;VI restate that commitment in terms '
        'of the Quine-atom role, where it becomes an equivalence rather than a bare choice. '
        'Sections VII&#8211;X extend the chain further: they derive AFAStructure\'s laws from '
        'stronger structures, provide concrete models, and prove decoration uniqueness for finite '
        'graphs over abstract DecorationUniverses &#8212; an analogue of the uniqueness clause of '
        'what AFA asserts as an axiom. Every node is either a proved theorem or a typeclass field:'))
    E += [
        li('ZP-A axioms A1&#8211;A4: semilattice structure (ZPSemilattice fields).'),
        li('ZP-B: 2-adic topology and irreversibility (proved from Mathlib).'),
        li('ZP-C: information theory, L-INF, L-RUN (proved axiom-free or from Mathlib).'),
        li('ZP-D: state layer, orthogonality (proved from ZP-A and ZP-B).'),
        li('ZP-E: T-SNAP, DA-1, DA-2 (T-SNAP and DA-2 proved axiom-free; DA-1 Path 3 outside Lean scope).'),
        li('ZP-J: AFAStructure fields (selfMem, quine_unique, bot_self_mem). '
           'T-EXEC, J1, and CC-1 in conditional form: proved axiom-free. '
           'Sections VII&#8211;X (Aczel connection, abstraction chain, concrete instances, '
           'decoration uniqueness): all sorry-free. &#10003;'),
        sp(4),
    ]
    E.append(body(
        'DA-1 Path 3 (the AIT/Kolmogorov complexity argument in ZP-E) remains outside Lean '
        'scope for the same reason it always has: Kolmogorov complexity is uncomputable and '
        'absent from Mathlib. ZP-J does not affect DA-1\'s status.'))
    E.append(sp(6))

    print('[build_zpj] Building Section VII...')
    E += [
        hr(),
        Paragraph('Section VII: The Aczel Connection &#8212; What the Encoding Does Not Settle', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Formalised in AczelConn.lean as an extension of the T-EXEC typeclass encoding. The '
        'results are choice-free statements about a lattice predicate; they do not reach Aczel\'s '
        'set-theoretic question.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. Aczel\'s Use of Dependent Choice', S['h2']))
    E.append(body(
        'Aczel (Non-Well-Founded Sets, 1988, ch. 6, Theorem 6.5) proves that for a set-continuous '
        'operator &#934;, J&#934; = &#8899;{x | x &#8838; &#934;x} is the largest fixed point of '
        '&#934;, and that every class X with X &#8838; &#934;X is contained in J&#934; (part 2). In '
        'the proof of part (2) he uses the axiom of Dependent Choice (DC) to build an infinite '
        'sequence of subsets of X, and notes: "I do not know if this use of the axiom of dependent '
        'choices was essential."'))
    E.append(body(
        'The step that uses DC passes from an element a of a CLASS X with X &#8838; &#934;X to a '
        'SET x with a &#8712; x &#8838; &#934;x, which is needed because J&#934; is a union of sets. '
        'That step is where Aczel\'s question lives, and it is a question about a proof in set '
        'theory.'))

    E.append(Paragraph('II. The J_self Set and Its Structure', S['h2']))
    E.append(body(
        'In ZP\'s encoding the lattice-level counterpart is J_self = {x : L | selfMem(x)}, the set '
        'of self-containing elements, defined directly by comprehension on the predicate selfMem. '
        'No set-continuous operator is defined and J_self is not built as a union of sets, so the '
        'step that uses DC in Aczel\'s proof has no counterpart here. The results about J_self '
        'follow immediately from AFAStructure (Lean: AczelConn.lean &#167; I):'))
    E.append(result_box(
        'J_self Theorems (AczelConn.lean &#167; I)',
        [
            'bot &#8712; J_self: the bottom element is self-containing. (AFAStructure.bot_self_mem.)',
            'J_self_eq_bot: every x &#8712; J_self satisfies x = &#8869;. '
            '(One step: quine_unique x &#8869; hx bot_self_mem.)',
            'J_self_eq_singleton_bot: J_self = {&#8869;}. No Classical.choice '
            '([propext, Quot.sound]). &#10003;',
            'J_self_is_largest: for any set S of self-containing elements, S &#8838; J_self. '
            'This holds by the definition of J_self, for any predicate, and uses no uniqueness: '
            'it has the shape of Aczel 6.5 part (2) and is not an instance of it. &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(body(
        'quine_unique is used once, to identify the only element of J_self as &#8869;. That '
        'identification corresponds to no clause of Theorem 6.5, and J_self_is_largest does not '
        'use it. The absence of Classical.choice is a measured fact about these Lean terms. It '
        'does not show that DC is inessential in Aczel\'s proof, for this or any operator.'))

    E.append(Paragraph('III. The Abstract Principle: A Unique Witness Determines Its Set', S['h2']))
    E.append(body(
        'The identification is not specific to self-membership. It holds for any predicate with a '
        'unique witness. AczelConn.lean makes this explicit:'))
    E.append(result_box(
        'Theorem singleton_from_unique_witness (AczelConn.lean &#167; II)',
        [
            'For any type &#945; and predicate P : &#945; &#8594; Prop: '
            'if w satisfies P(w) and &#8704; x, P(x) &#8594; x = w, '
            'then {x | P(x)} = {w}.',
            'Proof: pure set extensionality. No Classical.choice ([propext, Quot.sound]). &#10003;',
            'Application: selfMem_determines_singleton &#8212; {x : L | selfMem(x)} = {&#8869;} '
            'for any AFAStructure lattice L.',
        ]
    ))
    E.append(sp(6))
    E.append(callout(
        'Scope note: ZP-J does not answer Aczel\'s question, for the self-membership case or any '
        'other. His question concerns a use of DC inside a proof in set theory; the results here '
        'are choice-free statements about a lattice predicate and do not reach that proof. This '
        'document takes no position on whether that use of DC is essential.',
        bg=SLATE_LITE, border=SLATE
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section VIII...')
    E += [
        hr(),
        Paragraph('Section VIII: The Abstraction Chain &#8212; '
                  'ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Developed in SelfApp.lean and Scale.lean after T-EXEC was established; '
        'the abstraction chain derives AFAStructure\'s laws from stronger structures: a '
        'fixed-point structure and, beneath it, a valuation structure.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. The Question: Can AFAStructure\'s Fields Be Derived?', S['h2']))
    E.append(body(
        'AFAStructure has three fields: selfMem (a predicate), quine_unique (AFA uniqueness), '
        'and bot_self_mem (the bridge). These appear as structural prerequisites &#8212; '
        'typeclass fields rather than freestanding axioms, but still commitments that any '
        'instance must supply &#8212; two to PROVE, and selfMem to DEFINE, since it is data rather than a law. The abstraction chain asks: can the two laws '
        'themselves be derived from other structure?'))
    E.append(body(
        'The answer is yes, in two steps, with selfMem supplied by a definition along the way. First, AbstractSelfApp provides a self-application '
        'operation with unique_fp as a law, from which the two AFAStructure LAWS become '
        'derived theorems. Then ValuationStructure explains <i>why</i> &#8869; is the unique '
        'fixed point, making even unique_fp a theorem rather than a field.'))

    E.append(Paragraph('II. AbstractSelfApp &#8212; The Minimal Fixed-Point Structure', S['h2']))
    E.append(body(
        'AbstractSelfApp encodes the abstract pattern common to both the set-theoretic and '
        '2-adic domains: a self-application operation whose unique fixed point is &#8869;.'))
    E.append(def_box(
        'AbstractSelfApp Typeclass (SelfApp.lean &#167; I)',
        [
            'class AbstractSelfApp (L : Type*) [ZPSemilattice L] with:',
            '(1) selfApp : L &#8594; L  &#8212; the self-application operation.',
            '(2) fixed_bot : selfApp(&#8869;) = &#8869;  &#8212; &#8869; is a fixed point.',
            '(3) unique_fp : &#8704; x : L, selfApp(x) = x &#8594; x = &#8869;  '
            '&#8212; &#8869; is the ONLY fixed point.',
        ]
    ))
    E.append(sp(6))
    E.append(body(
        'From the two laws fixed_bot and unique_fp (selfApp is data), the two AFAStructure LAWS become derived theorems, and selfMem is supplied as a definition (selfMemDerived) rather than proved &#8212; it is data:'))
    E.append(result_box(
        'Derived Results from AbstractSelfApp (SelfApp.lean &#167; II&#8211;III)',
        [
            'selfMemDerived x := selfApp(x) = x  &#8212; self-containment as fixed-point property.',
            'derived_bot_self_mem: selfMemDerived(&#8869;) &#8212; from fixed_bot. &#10003;',
            'derived_quine_unique: any two self-containing elements are equal &#8212; '
            'each equals &#8869; by unique_fp, so equal to each other. &#10003;',
            'selfMem_eq_singleton_bot: {x | selfMemDerived(x)} = {&#8869;} &#8212; '
            'via singleton_from_unique_witness. No Classical.choice. &#10003;',
            'instance toAFAStructure: any AbstractSelfApp gives an AFAStructure. '
            'The two laws are theorems, not additional commitments; selfMem is a supplied definition. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. ValuationStructure &#8212; Why &#8869; is the Unique Fixed Point', S['h2']))
    E.append(body(
        'AbstractSelfApp assumes unique_fp. ValuationStructure derives it. The key insight '
        'is the 2-adic argument: if scale increases valuation by 1 at every non-&#8869; element, '
        'then scale(x) = x implies val(x) = val(x) + 1 &#8212; impossible for any finite '
        'valuation. Only &#8869;, which has infinite valuation (val(&#8869;) = &#8868;), '
        'can be a fixed point.'))
    E.append(def_box(
        'ValuationStructure Typeclass (Scale.lean &#167; I)',
        [
            'class ValuationStructure (L : Type*) [ZPSemilattice L] with:',
            '(1) scale : L &#8594; L  &#8212; the self-application (scaling) operation.',
            '(2) val : L &#8594; &#8469;&#8734;  &#8212; valuation into the extended naturals.',
            '(3) scale_bot : scale(&#8869;) = &#8869;  &#8212; &#8869; is a fixed point of scale.',
            '(4) val_bot : val(&#8869;) = &#8868;  &#8212; &#8869; has infinite valuation.',
            '(5) val_unique : &#8704; x, val(x) = &#8868; &#8594; x = &#8869;  '
            '&#8212; only &#8869; has infinite valuation.',
            '(6) val_scale : &#8704; x &#8800; &#8869;, val(scale(x)) = val(x) + 1  '
            '&#8212; scale strictly increases valuation at non-&#8869; elements.',
        ]
    ))
    E.append(sp(6))
    E.append(result_box(
        'Derived Results from ValuationStructure (Scale.lean &#167; II&#8211;IV)',
        [
            'val_finite_of_ne_bot: x &#8800; &#8869; &#8658; val(x) &#8800; &#8868;  '
            '&#8212; contrapositive of val_unique. &#10003;',
            'scale_ne_fixed: x &#8800; &#8869; &#8658; scale(x) &#8800; x  '
            '&#8212; val(scale(x)) = val(x) + 1 &#8800; val(x) since val(x) is finite. &#10003;',
            'scale_unique_fp: scale(x) = x &#8658; x = &#8869;  &#8212; from scale_ne_fixed. &#10003;',
            'instance toAbstractSelfApp: selfApp = scale; fixed_bot and unique_fp are theorems. '
            'No additional fields. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('IV. The Full Chain and the 2-Adic Parallel', S['h2']))
    E.append(body(
        'The complete derivation chain is:'))
    E.append(callout(
        'ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure\n'
        'Four valuation axioms &#8594; Two fixed-point fields &#8594; Three AFA fields\n'
        'At each step, the LAWS of the lower typeclass become derived theorems; the data fields '
        'are supplied, not proved.',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(6))
    E.append(body(
        '<b>What this chain does NOT establish, and the Lean says so explicitly.</b> '
        'AbstractSelfApp is a STRUCTURE, not a property: it supplies a <i>chosen</i> '
        'self-application map, and carrying one says nothing about the carrier, because '
        '<b>every</b> ZPSemilattice carries one. The NO-GO gauge in ZeroParadox/Computability/SelfApp.lean '
        '&#167;V records the consequence: because toAFAStructure is an instance, the whole AFA '
        'layer &#8212; IsQuineAtom, bot_is_quine_atom, T-EXEC &#8212; comes free from a degenerate '
        'map, so the anti-foundation layer is satisfied by a structure in which nothing refers to '
        'anything. The chain is therefore a statement about what FOLLOWS from the structure, not '
        'evidence that any particular carrier has it non-trivially. Membership is not an argument; '
        'a witness that the framework\'s real instances differ from the degenerate one is. '
        'Each arrow is an instance, so it runs from the stronger hypothesis to the weaker: every '
        'ZPSemilattice carries AbstractSelfApp and AFAStructure, while a ValuationStructure on a '
        'carrier with any element besides &#8869; forces that carrier to be infinite '
        '(valuationStructure_forces_infinite, ZeroParadox/Valuation/ScaleBridge.lean &#167; VI). '
        'The chain explains the AFA laws; it does not reduce what must be assumed.'))
    E.append(sp(6))
    E.append(body(
        'At each level of the chain, the 2-adic parallel holds. At the AbstractSelfApp level: '
        'multiplication by 2 in &#8474;&#8322; has 0 as its unique fixed point '
        '(2x = x &#8658; x = 0, by ring arithmetic), and {x &#8712; &#8474;&#8322; | 2x = x} = {0} '
        'by singleton_from_unique_witness. At the ValuationStructure level: in &#8484;&#8322;, '
        'scale = &#215;2 and val = 2-adic valuation satisfy all four axioms &#8212; '
        'in particular, v&#8322;(2x) = v&#8322;(x) + 1 for x &#8800; 0 (proved from '
        'PadicInt.valuation_mul and PadicInt.valuation_p in Mathlib). No ZPSemilattice or '
        'ValuationStructure instance on &#8484;&#8322; is registered, so the parallel is proved as '
        'standalone theorems demonstrating the same proof structure closes both cases. That is a '
        'fact about what is declared, not what is possible: ZeroParadox/Valuation/Scale.lean '
        '&#167; V proves &#8484;&#8322; admits a ZPSemilattice carrying a ValuationStructure.'))
    E.append(sp(6))

    print('[build_zpj] Building Section IX...')
    E += [
        hr(),
        Paragraph('Section IX: Concrete Instances &#8212; '
                  '&#8469;&#8734; and OntologicalStates', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Developed in Model.lean and OntBridge.lean to ground the abstraction '
        'chain in concrete types; OntologicalStates takes a shorter path because a '
        'two-element carrier admits no ValuationStructure.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. &#8469;&#8734; &#8212; The Canonical ValuationStructure Instance',
                       S['h2']))
    E.append(body(
        '&#8469;&#8734; = WithTop &#8469; (the extended naturals) carries a ZPSemilattice '
        'with join = min and bot = &#8868; (the natural maximum). The ZP partial order reverses '
        '&#8469;&#8734;\'s natural order: x &#8804; y iff min x y = y iff x &#8805; y. '
        'So &#8868; is the ZP-bottom (valuation &#8734;, unique fixed point) and 0 is the '
        'ZP-maximum (fully constrained).'))
    E.append(def_box(
        '&#8469;&#8734; Instances (Model.lean)',
        [
            'instNatInfZPS: ZPSemilattice &#8469;&#8734; with join = min, bot = &#8868;. '
            'A1&#8211;A3: min is associative, commutative, idempotent. '
            'A4: min &#8868; x = x because &#8868; is the maximum. &#10003;',
            'instNatInfVal: ValuationStructure &#8469;&#8734; with scale = (&#183; + 1), val = id. '
            'scale_bot: &#8868; + 1 = &#8868; (WithTop.top_add). '
            'val_bot: id &#8868; = &#8868;. '
            'val_unique: id x = &#8868; &#8658; x = &#8868;. '
            'val_scale: x &#8800; &#8868; &#8658; id(x + 1) = id(x) + 1 (rfl). &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(result_box(
        'Derived AFA Content on &#8469;&#8734; (Model.lean &#167; III)',
        [
            'natInf_scale_unique_fp: x + 1 = x &#8658; x = &#8868;. '
            '(The unique fixed point of (&#183; + 1) in &#8469;&#8734; is &#8868;.) &#10003;',
            'natInf_selfMem_singleton: {x : &#8469;&#8734; | x + 1 = x} = {&#8868;}. &#10003;',
            'Via toAbstractSelfApp and toAFAStructure, &#8469;&#8734; carries a full AFAStructure '
            'with the two laws as theorems and selfMem supplied as a definition. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. OntologicalStates &#8212; The Direct AbstractSelfApp Path',
                       S['h2']))
    E.append(body(
        'OntologicalStates = {null, exist} (ZP-B\'s two-element state space) cannot follow the '
        'ValuationStructure path: a ValuationStructure on a carrier with any element besides '
        '&#8869; forces that carrier to be infinite (valuationStructure_forces_infinite), so a '
        'two-element type admits none. '
        'Instead it takes the direct path to AbstractSelfApp.'))
    E.append(body(
        'The self-application operation is the constant-to-null function: every element maps '
        'to null. null is the unique fixed point because null &#8614; null (fixed_bot) and '
        'exist &#8614; null &#8800; exist (unique_fp holds vacuously for exist). '
        'AFA content follows immediately from the AbstractSelfApp instance.'))
    E.append(def_box(
        'OntologicalStates Instances (OntBridge.lean)',
        [
            'instOntZPS: ZPSemilattice OntologicalStates with null-identity join and bot = null. '
            'All four axioms proved by case analysis. &#10003;',
            'instOntSelfApp: AbstractSelfApp OntologicalStates with selfApp = constant-to-null. '
            'fixed_bot: null &#8614; null = null (rfl). '
            'unique_fp: null &#8614; rfl; exist &#8614; absurd hx (by decide). &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(result_box(
        'Derived AFA Content on OntologicalStates (OntBridge.lean &#167; III)',
        [
            'ont_bot_self_mem: null is self-containing. &#10003;',
            'ont_quine_unique: any two self-containing elements of OntologicalStates are equal. &#10003;',
            'ont_selfMem_singleton: {x | selfMemDerived(x)} = {null}. No Classical.choice. &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(callout(
        'Two concrete instances, two paths through the chain. &#8469;&#8734; takes the full '
        'ValuationStructure route. OntologicalStates bypasses ValuationStructure and connects '
        'directly to AbstractSelfApp. Both deliver the same conclusion: the unique self-containing '
        'element is the bottom. The architecture is sound because each type takes the path '
        'the mathematics allows.',
        bg=SLATE_LITE, border=SLATE
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section X...')
    E += [
        hr(),
        Paragraph('Section X: APG Decoration Uniqueness', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Formalised in APG.lean as the most recent addition; this section proves '
        'decoration uniqueness for finite accessible pointed graphs over abstract '
        'DecorationUniverses &#8212; an analogue of AFA\'s uniqueness clause, not that clause '
        'and not AFA itself &#8212; '
        'using the typeclass chain established in Sections VIII&#8211;IX.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. Accessible Pointed Graphs and Decorations', S['h2']))
    E.append(body(
        'An Accessible Pointed Graph (APG) is a directed graph (Quiver) with a distinguished '
        'root vertex from which every vertex is reachable via directed paths. AFA is an axiom, '
        'not a theorem: every graph has a unique decoration &#8212; a labelling of vertices by '
        'sets satisfying the membership equation d(v) = {d(w) | v &#8594; w} (Aczel 1988, ch. 1 '
        'p. 6). Its well-founded counterpart, Mostowski\'s Collapsing Lemma (p. 4), is a result: '
        'every well-founded graph has a unique decoration.'))
    E.append(body(
        'ZP-J\'s uniqueness result is stated for an abstract DecorationUniverse rather '
        'than sets. This avoids ZFSet (which satisfies Foundation, making self-loops impossible) '
        'and places the result in the typeclass framework established above.'))
    E.append(def_box(
        'Typeclass: DecorationUniverse (APG.lean &#167; II)',
        [
            'class DecorationUniverse (U : Type*) [ZPSemilattice U]',
            '      [ValuationStructure U] where',
            '  collect : Set U &#8594; U',
            '  collect_singleton : &#8704; x : U, collect {x} = scale x',
            '  collect_val_ge : &#8704; (S : Set U) (x : U), x &#8712; S &#8594;'
            '                   val (collect S) &#8805; val x + 1',
            '',
            'Exactly two laws. They pin the SINGLETON case and a lower bound; they do not '
            'require collect to assemble a parent value from its children.',
            'A valid decoration d : V &#8594; U satisfies d(v) = collect({d(w) | v &#8594; w}) '
            'at every vertex v.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. The Valuation Argument for Cyclic Vertices', S['h2']))
    E.append(body(
        'The first key results handle cyclic vertices. The argument is a chain of two '
        'inequalities, not an iterated equation. Let w be the next vertex on the cycle and p the '
        'path from w back to v. Because w is a child of v and d(v) collects over d of v&#8217;s '
        'children, collect_val_ge gives val(d(v)) &#8805; val(d(w)) + 1. Following p, the lemma '
        'path_val_chain (private to APG.lean) gives val(d(w)) &#8805; val(d(v)) + length(p). '
        'Together these force val(d(v)) to exceed itself, which no finite value in &#8469;&#8734; '
        'can do, so val(d(v)) = &#8868; (infinite) and therefore d(v) = &#8869;. No assumption is '
        'made about how many children a vertex has.'))
    E.append(body(
        'The iterated form d(v) = scale<sup>k</sup>(d(v)) is not how this proof proceeds. The class '
        'laws relate collect to scale only through collect_singleton, so composing decoration '
        'equations yields that form when each vertex&#8217;s set of child decorations on the cycle '
        'is a singleton &#8212; for example, when each vertex has exactly one child. The '
        'scale<sup>k</sup> lemmas below are genuine results about periodic points of scale, and '
        'kCycle_node_eq_bot takes that equation as a hypothesis rather than deriving it.'))
    E.append(result_box(
        'Cyclic Vertex Theorems (APG.lean &#167;&#167; III&#8211;VII\')',
        [
            'val_iterate: val(scale<sup>k</sup>(x)) = val(x) + k for x &#8800; &#8869;. &#10003;',
            'scale_iterate_unique_fp: scale<sup>k</sup>(x) = x &#8658; x = &#8869; for k &#8805; 1. &#10003;',
            'pureSelfLoop_decoration_eq_bot: any valid decoration assigns &#8869; to a pure '
            'self-loop vertex. &#10003;',
            'kCycle_node_eq_bot: if d(v) = scale<sup>k</sup>(d(v)) for some k &#8805; 1 under any valid decoration, '
            'then d(v) = &#8869;. The cycle equation is a hypothesis, not derived. &#10003;',
            'cyclic_decoration_eq_bot: any vertex with a directed cycle through itself '
            'receives &#8869; under any valid decoration. Proof route: collect_val_ge and '
            'path_val_chain, with val_finite_of_ne_bot; it uses neither val_iterate nor '
            'scale_iterate_unique_fp. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. The Acyclic Case and the "Infinite Period"', S['h2']))
    E.append(body(
        'Cyclic vertices have a finite period k &#8212; the path returns in k steps, and a '
        'valuation bound around the cycle forces &#8869;. Acyclic vertices have an "infinite period" &#8212; '
        'the path never returns to them, so they carry no cycle of their own for that bound to run around. '
        'Read as a coincidence of two charts, the finite k of a cycle is the zero side and its absence '
        'is the infinity side. The proved half holds of one vertex in both charts at once: a cyclic '
        'vertex receives the order-theoretic zero &#8869;, and &#8869;\'s valuation is &#8868;, infinite '
        'depth (cyclic_decoration_eq_bot with val_bot). The implication runs from the cycle to that '
        'value only; no value is claimed for an acyclic vertex from its period alone. The pairing is '
        'stated for DecorationUniverses: in AFA set theory a graph with a cycle can picture a set other '
        'than Q, such as 0* = {&#8709;, 0*} (Aczel 1988, Example 1.5).'))
    E.append(body(
        'The hardness of the acyclic proof is that "infinite period" gives you nothing to induct '
        'on. <i>Reach cardinality</i> &#8212; the cardinality of {w | Path v w}, the set of '
        'vertices reachable from v &#8212; serves as a finite proxy. For any child w of an '
        'acyclic vertex v, the reach of w is a strict subset of the reach of v (since v cannot '
        'be reached from w without creating a cycle). Reach cardinality is therefore strictly '
        'decreasing, providing a well-founded measure for the induction.'))
    E.append(result_box(
        'Acyclic Induction and Global Uniqueness (APG.lean &#167;&#167; VIII&#8211;IX)',
        [
            'acyclic_induction_step: if two valid decorations d&#8321;, d&#8322; agree on all '
            'children of an acyclic vertex v, they agree on v. '
            '(The two child image sets are equal by Set.ext, then rewrite &#8212; ordinary '
            'congruence, consuming no class axiom.) &#10003;',
            'decoration_unique [Fintype V]: for any finite APG with root r and any two valid '
            'decorations d&#8321;, d&#8322; into any DecorationUniverse, d&#8321; = d&#8322;. '
            'Proof: strong induction on |{w | Path u w}|; cyclic case by cyclic_decoration_eq_bot; '
            'acyclic case by acyclic_induction_step with IH on children. &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(callout(
        'decoration_unique is the ZP analogue of the uniqueness clause of AFA (an axiom, not a '
        'theorem): for any '
        '<b>finite</b> APG, at most one valid decoration exists into any DecorationUniverse. '
        'The proof consumes collect_val_ge (never collect_singleton), val_unique through '
        'val_finite_of_ne_bot, and [Fintype V] for the acyclic descent &#8212; it '
        'gives a sufficient condition for decoration uniqueness, not a characterisation. It does not construct a specific AFA '
        'model or derive AFA\'s axioms from ZP\'s.',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(6))

    print('[build_zpj] Building registers...')
    E += [hr(), Paragraph('Traceability Register &#8212; ZP-J', S['h1'])]

    trace_rows = [
        ['T-EXEC: Quine atom = &#8869;',
         'AFAStructure.bot_self_mem + the uniqueness half of IsQuineAtom q',
         'None &#8212; typeclass fields',
         'Lean: t_exec &#8212; axiom-free &#10003;'],
        ['J1: Quine join-identity',
         'T-EXEC + ZP-A A4 (bot_join)',
         'None',
         'Lean: j1_quine_join_identity &#8212; axiom-free &#10003; (was axiom ax_j1 in stub)'],
        ['CC-1, conditional form: S&#8320; = Q &#8658; S&#8320; = &#8869;',
         'T-EXEC',
         'None',
         'Lean: cc1_derived &#8212; axiom-free &#10003; (restates ZP-A\'s conditional claim; converse by t_exec_iff)'],
        ['bot_is_quine_atom',
         'AFAStructure.bot_self_mem + quine_unique',
         'None',
         'Lean: bot_is_quine_atom &#8212; axiom-free &#10003;'],
        ['t_exec_iff: IsQuineAtom &#8596; = &#8869;',
         'T-EXEC + bot_is_quine_atom',
         'None',
         'Lean: t_exec_iff &#8212; axiom-free &#10003;'],
        ['bot_unique: join-identity is unique',
         'da2_bottom_characterization',
         'None',
         'Lean: bot_unique &#8212; axiom-free &#10003; (no AFA required)'],
        ['J_self = {&#8869;} (no Classical.choice)',
         'AFAStructure.quine_unique &#8212; one step',
         'None',
         'Lean: J_self_eq_singleton_bot &#8212; no Classical.choice &#10003;'],
        ['singleton_from_unique_witness',
         'Set extensionality (propext)',
         'None',
         'Lean: singleton_from_unique_witness &#8212; [propext, Quot.sound]; no Classical.choice &#10003;'],
        ['AbstractSelfApp &#8594; AFAStructure',
         'AbstractSelfApp.fixed_bot + unique_fp',
         'None',
         'Lean: toAFAStructure &#8212; selfMem := selfMemDerived (a definition); bot_self_mem and quine_unique are theorems &#10003;'],
        ['ValuationStructure &#8594; AbstractSelfApp',
         'ValuationStructure.val_scale + val_unique',
         'None',
         'Lean: scale_unique_fp, toAbstractSelfApp &#8212; [propext, Classical.choice, Quot.sound], '
         'already in each STATEMENT (ZP-J AFA Addendum &#167; V) &#10003;'],
        ['&#8469;&#8734; : ValuationStructure',
         '&#8469;&#8734; arithmetic (WithTop.top_add)',
         'None',
         'Lean: instNatInfZPS, instNatInfVal &#8212; each [propext, Classical.choice, Quot.sound] &#10003;'],
        ['OntologicalStates : AbstractSelfApp',
         'Constant-to-null map; two-element case analysis',
         'None',
         'Lean: instOntSelfApp &#8212; axiom-free &#10003;'],
        ['cyclic_decoration_eq_bot',
         'collect_val_ge + path_val_chain + val_finite_of_ne_bot',
         'None',
         'Lean: cyclic_decoration_eq_bot &#8212; [propext, Classical.choice, Quot.sound] &#10003;'],
        ['decoration_unique [Fintype V]',
         'cyclic_decoration_eq_bot + acyclic_induction_step + Set.ncard',
         '[Fintype V] &#8212; finite graph assumption',
         'Lean: decoration_unique &#8212; propext, Classical.choice, Quot.sound &#10003;'],
        ['AFAStructure.bot_self_mem',
         'The role that the ZF+AFA identity &#8869; = {&#8869;} describes',
         'Typeclass field &#8212; a hypothesis; every ZPSemilattice meets it trivially',
         'Not a theorem; a hypothesis T-EXEC carries.'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'New assumption?', 'Status'],
        trace_rows,
        [TW*0.22, TW*0.27, TW*0.22, TW*0.29]
    ))
    E.append(sp(8))

    E += [hr(), Paragraph('Open Items Register &#8212; ZP-J', S['h1'])]

    oq_rows = [
        ['CC-1 (ZP-A) derivability',
         'RESTATED &#8212; not forced',
         'cc1_derived: a state sequence that starts at a Quine atom starts at &#8869;, and by '
         't_exec_iff the converse holds, so the two starting conditions are equivalent. No '
         'freestanding axiom; the choice of starting point remains, stated through the role.'],
        ['AX-J1 bridge axiom',
         'CLOSED &#8212; J1 derived',
         'The stub version had ax_j1 as a freestanding axiom. '
         'The final version derives J1 from T-EXEC + ZP-A A4. Axiom eliminated.'],
        ['AFAStructure concrete instances',
         'CLOSED &#8212; multiple instances',
         'MachinePhase (ZP-K): machinePhaseAFA : AFAStructure MachinePhase. '
         '&#8469;&#8734;: instNatInfZPS + instNatInfVal &#8594; AbstractSelfApp &#8594; AFA content. '
         'OntologicalStates: instOntSelfApp &#8594; AFA content directly.'],
        ['Aczel DC question',
         'NOT ADDRESSED',
         'J_self = {&#8869;} is proved with no Classical.choice, and J_self_is_largest holds by '
         'definition. Neither is a statement about Aczel\'s proof of Theorem 6.5 in set theory, so '
         'this document takes no position on whether his use of DC is essential.'],
        ['DA-1 Path 1 formalisation',
         'PARTIAL &#8212; APG case proved',
         'DA-1 Path 1 (ZP-E) invokes &#8869; = {&#8869;} informally. ZP-J T-EXEC formalises '
         'the role identification, not the set identity. decoration_unique (&#167; X) proves uniqueness for finite APGs '
         'over abstract DecorationUniverses. The full ZF+AFA set-theoretic bridge '
         '&#8212; showing the ZP types literally satisfy the ZF+AFA axioms &#8212; '
         'remains outside Lean scope.'],
        ['ZP-A CC-1 cross-check',
         'RESOLVED',
         'ZP-A\'s CC-1 box now matches this document: a Conditional Claim at ZP-A scope, which '
         'cc1_derived and t_exec_iff restate as an equivalence of starting conditions, not a forcing of the starting point.'],
        ['Formal ZPSemilattice instance for a ValuationStructure type',
         'PARTIAL &#8212; one registered',
         'Model.lean registers both instances on &#8469;&#8734;. '
         'ZeroParadox/Valuation/Scale.lean &#167; V proves &#8484;&#8322; admits a ZPSemilattice '
         'carrying a ValuationStructure, as an existence statement, without registering an '
         'instance; no registered instance on &#8484;&#8322; was located in ZeroParadox/**/*.lean '
         'on 2026-09-13.'],
    ]
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.22, TW*0.18, TW*0.60]
    ))

    E += [
        sp(12),
        hr(),
        Paragraph(
            '<i>End of ZP-J | Theorem T-EXEC: Executability of Self-Reference | '
            'CC-1 restated as an equivalence &#8212; no freestanding axioms | '
            'J_self = {&#8869;} with no Classical.choice | '
            'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure | '
            'Instances: &#8469;&#8734;, OntologicalStates | '
            'decoration_unique: any two valid decorations of a finite APG into a DecorationUniverse agree | '
            'All results sorry-free in Lean 4</i>',
            S['endnote']),
    ]

    print(f'[build_zpj] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpj] Written: {out_path}')


if __name__ == '__main__':
    build()
