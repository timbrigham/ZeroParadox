"""
Zero Paradox — ZP-J: Executability of Self-Reference PDF Builder
Version 2.2 | June 2026
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

VERSION = '2.2'


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
        Paragraph('Version ' + VERSION + ' | May 2026', S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'This document establishes Theorem T-EXEC (Executability of Self-Reference): in any '
        'ZP-A join-semilattice with AFA (Anti-Foundation Axiom) grounding, the unique Quine atom '
        'Q &#8212; the element satisfying Q = {Q} &#8212; is provably the bottom element &#8869;. '
        'This closes the bridge between the set-theoretic and order-theoretic layers of the '
        'framework. CC-1 from ZP-A, which stated "S&#8320; = &#8869;" as a modelling commitment, '
        'becomes a derived theorem.'))
    E.append(body(
        'This layer extends the core T-EXEC result in four directions: it establishes that '
        'Aczel\'s use of Dependent Choice is unnecessary for the self-membership case (Section VII); '
        'it generalises the AFAStructure typeclass into an abstraction chain reaching down to '
        'a pure valuation structure (Section VIII); it instantiates that chain on two concrete '
        'types (Section IX); and it proves global decoration uniqueness for finite accessible '
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
        'instantiation of ZP-A must begin at &#8869;? The answer is yes, provided the lattice '
        'has AFA grounding.'))

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
        'Answer (ZP-J T-EXEC): it is forced &#8212; by the AFA identification &#8869; = {&#8869;}, '
        'encoded structurally in the AFAStructure typeclass.',
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
        'The Anti-Foundation Axiom (AFA, Aczel 1988) replaces Foundation with a universal '
        'existence and uniqueness result: every accessible pointed graph (APG) has a unique '
        'set-theoretic decoration. Under AFA, self-containing sets are not only possible but '
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
            'principles alone. It is a structural prerequisite for any AFA-grounded lattice.',
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
        'The AFAStructure typeclass in ZPJ.lean captures exactly this. Its three fields are '
        'sufficient to derive T-EXEC with no additional axioms. The full AFA machinery '
        '(APGs, bisimulation, decoration) provides the informal justification for why any '
        'concrete lattice grounded in ZF+AFA satisfies these three fields &#8212; but the formal '
        'derivation requires only the fields themselves.'))

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
        'AFAStructure Typeclass (ZPJ.lean &#167; I)',
        [
            'class AFAStructure (L : Type*) [ZPSemilattice L] with:',
            '(1) selfMem : L &#8594; Prop  '
            '&#8212; the self-membership predicate. selfMem(x) means x contains itself as a member '
            'in the AFA sense.',
            '(2) quine_unique : &#8704; x y : L, selfMem(x) &#8594; selfMem(y) &#8594; x = y  '
            '&#8212; AFA uniqueness. At most one element of L is self-containing.',
            '(3) bot_self_mem : selfMem(&#8869;)  '
            '&#8212; the bridge field. The bottom element of the lattice is self-containing. '
            'This is the formal encoding of &#8869; = {&#8869;}.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. What bot_self_mem Says', S['h2']))
    E.append(body(
        'bot_self_mem is the single structural claim that connects the order-theoretic world '
        '(ZP-A\'s lattice) to the set-theoretic world (AFA). It says: the bottom element &#8869; '
        'of the lattice is self-containing &#8212; it satisfies selfMem(&#8869;).'))
    E.append(body(
        'In set-theoretic terms: &#8869; &#8712; &#8869;, i.e. &#8869; = {&#8869;}. '
        'In the framework: &#8869; contains itself as its sole content. '
        'This is not a new claim &#8212; it is the identification that ZP-E\'s DA-1 Path 1 already '
        'invokes informally. ZP-J encodes it as a typeclass field, making it a verifiable '
        'structural prerequisite rather than a narrative motivation.'))
    E.append(body(
        'Any concrete lattice L that claims to be AFA-grounded must prove bot_self_mem as '
        'part of its AFAStructure instance. If it cannot, it is not genuinely AFA-grounded &#8212; '
        'the identification &#8869; = {&#8869;} is part of what "AFA-grounded" means.'))
    E.append(remark_box(
        'Remark R-J.0 &#8212; CIC Encoding and the AFA Distinction',
        [
            'In the MachinePhase concrete instance (ZP-K), selfMem is defined as '
            'selfMem x := x = &#8869;. With this definition, bot_self_mem is proved by rfl: '
            '&#8869; = &#8869; holds by reflexivity.',
            'This is the CIC-compatible encoding of AFA self-containment. In Lean 4 (based on '
            'the Calculus of Inductive Constructions), the set-theoretic statement &#8869; &#8712; &#8869; '
            '&#8212; meaning &#8869; literally contains itself as a member under ZF+AFA &#8212; is not '
            'directly formalizable. CIC lacks the membership relation &#8712; of set theory. The '
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
        'In the stub version of ZPJ.lean, the bridge was a freestanding axiom: '
        'ax_j1_quine_join_identity. It stated directly that the Quine atom satisfies the '
        'join-identity. This compiled, but the purity check showed T-EXEC depending on '
        'ax_j1_quine_join_identity &#8212; a named axiom floating outside any typeclass.'))
    E.append(body(
        'Encoding the commitment as a typeclass field is philosophically and formally cleaner. '
        'A freestanding axiom is a global assertion that the proof checker accepts without '
        'verification. A typeclass field is a requirement: any instance of AFAStructure must '
        'supply a proof of bot_self_mem. The commitment is not asserted once and forgotten &#8212; '
        'it is checked at every instantiation. Concrete lattices must earn their AFA status.'))
    E.append(callout(
        'The distinction: a freestanding axiom says "trust me, this is true." '
        'A typeclass field says "prove it for your specific lattice, or it does not compile." '
        'ZP-J uses the second. The philosophical commitment (&#8869; = {&#8869;}) '
        'becomes a proof obligation at every concrete instantiation.',
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
            'Lean: ZeroParadox.ZPJ.t_exec &#8212; proved in ZPJ.lean. '
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
           '(This is the bridge field &#8212; &#8869; = {&#8869;} encoded structurally.)'),
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
            'the derived theorem J1 (Section V), but T-EXEC itself is purely order-theoretic: '
            'it uses only quine_unique and bot_self_mem.',
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
            'Lean: ZeroParadox.ZPJ.bot_is_quine_atom &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. The Full Biconditional', S['h2']))
    E.append(body(
        'Combining T-EXEC and bot_is_quine_atom yields the full biconditional: '
        'IsQuineAtom(q) &#8596; q = &#8869;. Being the Quine atom and being the bottom element '
        'are the same property, stated in set-theoretic and order-theoretic language respectively.'))
    E.append(result_box(
        'Theorem t_exec_iff &#8212; Full Equivalence',
        [
            'For any q : L in an AFAStructure lattice:',
            'IsQuineAtom(q) &#8596; q = &#8869; &#8596; &#8704; x : L, join q x = x.',
            'The three conditions are mutually equivalent: Quine atom (set-theoretic), '
            'bottom element (order-theoretic), and join-identity element (algebraic). '
            'They are three formulations of one structural role.',
            'Lean: ZeroParadox.ZPJ.t_exec_iff &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    print('[build_zpj] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Derived Results &#8212; J1 and CC-1 as Theorems', S['h1']),
        hr(),
    ]

    E.append(Paragraph('I. J1 &#8212; QuineJoinIdentity (Derived)', S['h2']))
    E.append(body(
        'In the initial stub of ZPJ.lean, the claim "the Quine atom satisfies the join-identity" '
        'was stated as a freestanding axiom (ax_j1_quine_join_identity). ZP-J replaces it with '
        'a theorem.'))
    E.append(result_box(
        'Theorem J1 &#8212; QuineJoinIdentity (formerly Axiom AX-J1)',
        [
            'In any AFAStructure lattice L, if q is the Quine atom, then &#8704; x : L, join q x = x.',
            'Proof: q = &#8869; by T-EXEC. Then join q x = join &#8869; x = x by A4 (bot_join, ZP-A). &#10003;',
            'Status: DERIVED THEOREM. Was axiom ax_j1_quine_join_identity in the stub &#8212; '
            'now proved from T-EXEC + ZP-A A4. No freestanding axiom remains.',
            'Lean: ZeroParadox.ZPJ.j1_quine_join_identity &#8212; does not depend on any axioms. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. CC-1 Derived', S['h2']))
    E.append(body(
        'ZP-A CC-1 is now a theorem. If the initial state S&#8320; of a state sequence is the '
        'Quine atom Q, then S&#8320; = &#8869; &#8212; a consequence of T-EXEC, not a modelling '
        'choice.'))
    E.append(result_box(
        'Theorem CC-1 (Derived) &#8212; cc1_derived',
        [
            'Let L be an AFAStructure lattice. Let S : &#8469; &#8594; L be a state sequence '
            '(ZP-A D3) and Q : L a Quine atom. If S(0) = Q, then S(0) = &#8869;.',
            'Proof: S(0) = Q (hypothesis). Q = &#8869; by T-EXEC. Therefore S(0) = &#8869;.',
            'The modelling commitment "we choose &#8869; as the initial state" is replaced by '
            '"the Quine atom IS &#8869;, structurally." Starting at Q and starting at &#8869; '
            'are not two choices &#8212; they are the same state, identified by structure.',
            'Lean: ZeroParadox.ZPJ.cc1_derived &#8212; does not depend on any axioms. &#10003;',
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
            'Lean: ZeroParadox.ZPJ.bot_unique &#8212; does not depend on any axioms. &#10003;',
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
        'ZPJ.lean proof obligations.'))
    E.append(body(
        'The foundational commitments are the typeclass fields themselves. In ZPSemilattice: '
        'A1&#8211;A4 (the semilattice axioms). In AFAStructure: selfMem (a predicate), '
        'quine_unique (AFA uniqueness), and bot_self_mem (the bridge). These are the structural '
        'prerequisites for any lattice that claims ZP-A + AFA grounding. They are not axioms '
        'floating in the ambient theory &#8212; they are proof obligations that any concrete '
        'instance must discharge.'))

    E.append(Paragraph('II. Where the Philosophy Lives Now', S['h2']))
    E.append(body(
        'The philosophical content of &#8869; = {&#8869;} has not disappeared. It has moved. '
        'Previously it lived in a narrative comment in ZP-A (CC-1\'s informal motivation) and '
        'in ZP-E\'s DA-1 Path 1 (one of three informal arguments for instantiation as execution). '
        'Now it lives in the definition of AFAStructure itself &#8212; specifically in bot_self_mem.'))
    E.append(body(
        'This is the correct location for a foundational claim. It is not hidden in a proof; '
        'it is stated in the typeclass definition where any reader can see it. Any lattice that '
        'wants to use ZP-J\'s results must provide a proof that its bottom element is '
        'self-containing. If it cannot, it is simply not an AFA-grounded lattice in the '
        'sense required by this framework.'))

    E.append(Paragraph('III. The Formal Chain', S['h2']))
    E.append(body(
        'The derivation chain entering ZP-J had one remaining gap: CC-1 was a committed '
        'starting point, not a derived one. Sections I&#8211;VI close that gap. '
        'Sections VII&#8211;X extend the chain further: they reduce the axiom load of '
        'AFAStructure, provide concrete models, and prove the full AFA decoration uniqueness '
        'theorem for finite graphs. Every node is either a proved theorem or a typeclass field:'))
    E += [
        li('ZP-A axioms A1&#8211;A4: semilattice structure (ZPSemilattice fields).'),
        li('ZP-B: 2-adic topology and irreversibility (proved from Mathlib).'),
        li('ZP-C: information theory, L-INF, L-RUN (proved axiom-free or from Mathlib).'),
        li('ZP-D: state layer, orthogonality (proved from ZP-A and ZP-B).'),
        li('ZP-E: T-SNAP, DA-1, DA-2 (T-SNAP and DA-2 proved axiom-free; DA-1 Path 3 outside Lean scope).'),
        li('ZP-J: AFAStructure fields (selfMem, quine_unique, bot_self_mem). '
           'T-EXEC, J1, CC-1: proved axiom-free. '
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
        Paragraph('Section VII: The Aczel Connection &#8212; DC-Free Results', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Formalised in ZPJ_AczelConn.lean as an immediate extension of the T-EXEC typeclass '
        'encoding; the DC-free observation follows directly from quine_unique.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. Aczel\'s Use of Dependent Choice', S['h2']))
    E.append(body(
        'Aczel (Non-Well-Founded Sets, 1988, ch. 6) proves that J&#934; = &#8899;{x | x &#8838; '
        '&#934;x} is the largest pre-fixed-point of a set-continuous operator &#934;. The proof uses '
        'the axiom of Dependent Choice (DC) to construct an &#969;-chain, and Aczel explicitly '
        'notes: "I do not know if this use of the axiom of dependent choices was essential."'))
    E.append(body(
        'DC is used when you must <i>build</i> a witness step by step because the fixed point '
        'cannot be identified structurally. In ZF+AFA, the Quine atom is unique by the axiom '
        'itself. Once uniqueness is available, construction is unnecessary &#8212; identification '
        'suffices.'))

    E.append(Paragraph('II. The J_self Set and Its Structure', S['h2']))
    E.append(body(
        'In ZP\'s encoding, the analogue of Aczel\'s J&#8721; for the self-membership operator '
        'is J_self = {x : L | selfMem(x)} &#8212; the set of self-containing elements. '
        'The key results about J_self follow immediately from AFAStructure '
        '(Lean: ZPJ_AczelConn.lean &#167; I):'))
    E.append(result_box(
        'J_self Theorems (ZPJ_AczelConn.lean &#167; I)',
        [
            'bot &#8712; J_self: the bottom element is self-containing. (AFAStructure.bot_self_mem.)',
            'J_self_eq_bot: every x &#8712; J_self satisfies x = &#8869;. '
            '(One step: quine_unique x &#8869; hx bot_self_mem.)',
            'J_self_eq_singleton_bot: J_self = {&#8869;}. Proved without DC. &#10003;',
            'J_self_is_largest: for any set S of self-containing elements, S &#8838; J_self. '
            '(Aczel 6.5 part (2), self-membership case &#8212; without DC.) &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(body(
        'Where Aczel\'s proof requires an &#969;-chain to arrive at J&#8721;, the ZP proof is '
        'one line: quine_unique applied once identifies the unique self-containing element as '
        '&#8869;. The chain is redundant because the fixed point is forced, not constructed.'))

    E.append(Paragraph('III. The Abstract Principle: Uniqueness Eliminates DC', S['h2']))
    E.append(body(
        'The argument is not specific to self-membership. It holds for any predicate with a '
        'unique witness. ZPJ_AczelConn.lean makes this explicit:'))
    E.append(result_box(
        'Theorem singleton_from_unique_witness (ZPJ_AczelConn.lean &#167; II)',
        [
            'For any type &#945; and predicate P : &#945; &#8594; Prop: '
            'if w satisfies P(w) and &#8704; x, P(x) &#8594; x = w, '
            'then {x | P(x)} = {w}.',
            'Proof: pure set extensionality. No DC, no Classical.choice. &#10003;',
            'Application: selfMem_determines_singleton &#8212; {x : L | selfMem(x)} = {&#8869;} '
            'for any AFAStructure lattice L.',
        ]
    ))
    E.append(sp(6))
    E.append(callout(
        'Scope note: the DC-free result applies to the self-membership operator because '
        'AFA provides uniqueness (quine_unique) directly. Whether DC can be eliminated for '
        'general set-continuous operators &#934; depends on whether uniqueness holds for each '
        '&#934;-fixed-point &#8212; an open question, as Aczel\'s "I do not know" reflects. '
        'ZP does not claim DC-freedom for the general case.',
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
        '<i>Developed in ZPJ_SelfApp.lean and ZPJ_Scale.lean after T-EXEC was established; '
        'the abstraction chain reduces the axiom load of AFAStructure by deriving its fields '
        'from a minimal fixed-point structure.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. The Question: Can AFAStructure\'s Fields Be Derived?', S['h2']))
    E.append(body(
        'AFAStructure has three fields: selfMem (a predicate), quine_unique (AFA uniqueness), '
        'and bot_self_mem (the bridge). These appear as structural prerequisites &#8212; '
        'typeclass fields rather than freestanding axioms, but still commitments that any '
        'instance must discharge. The abstraction chain asks: can these three commitments '
        'themselves be derived from something more primitive?'))
    E.append(body(
        'The answer is yes, in two steps. First, AbstractSelfApp provides a self-application '
        'operation and proves unique_fp, from which all three AFAStructure fields become '
        'derived theorems. Then ValuationStructure explains <i>why</i> &#8869; is the unique '
        'fixed point, making even unique_fp a theorem rather than a field.'))

    E.append(Paragraph('II. AbstractSelfApp &#8212; The Minimal Fixed-Point Structure', S['h2']))
    E.append(body(
        'AbstractSelfApp encodes the abstract pattern common to both the set-theoretic and '
        '2-adic domains: a self-application operation whose unique fixed point is &#8869;.'))
    E.append(def_box(
        'AbstractSelfApp Typeclass (ZPJ_SelfApp.lean &#167; I)',
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
        'From these two fields, all three AFAStructure fields become derived theorems:'))
    E.append(result_box(
        'Derived Results from AbstractSelfApp (ZPJ_SelfApp.lean &#167; II&#8211;III)',
        [
            'selfMemDerived x := selfApp(x) = x  &#8212; self-containment as fixed-point property.',
            'derived_bot_self_mem: selfMemDerived(&#8869;) &#8212; from fixed_bot. &#10003;',
            'derived_quine_unique: any two self-containing elements are equal &#8212; '
            'each equals &#8869; by unique_fp, so equal to each other. &#10003;',
            'selfMem_eq_singleton_bot: {x | selfMemDerived(x)} = {&#8869;} &#8212; '
            'via singleton_from_unique_witness. DC-free. &#10003;',
            'instance toAFAStructure: any AbstractSelfApp gives an AFAStructure. '
            'All three fields are theorems, not additional commitments. &#10003;',
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
        'ValuationStructure Typeclass (ZPJ_Scale.lean &#167; I)',
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
        'Derived Results from ValuationStructure (ZPJ_Scale.lean &#167; II&#8211;IV)',
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
        'At each step, the fields of the lower typeclass become derived theorems.',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(6))
    E.append(body(
        'At each level of the chain, the 2-adic parallel holds. At the AbstractSelfApp level: '
        'multiplication by 2 in &#8474;&#8322; has 0 as its unique fixed point '
        '(2x = x &#8658; x = 0, by ring arithmetic), and {x &#8712; &#8474;&#8322; | 2x = x} = {0} '
        'by singleton_from_unique_witness. At the ValuationStructure level: in &#8484;&#8322;, '
        'scale = &#215;2 and val = 2-adic valuation satisfy all four axioms &#8212; '
        'in particular, v&#8322;(2x) = v&#8322;(x) + 1 for x &#8800; 0 (proved from '
        'PadicInt.valuation_mul and PadicInt.valuation_p in Mathlib). &#8484;&#8322; cannot '
        'be a formal instance because it is a ring, not a ZPSemilattice; the parallel is '
        'proved as standalone theorems demonstrating the same proof structure closes both cases.'))
    E.append(sp(6))

    print('[build_zpj] Building Section IX...')
    E += [
        hr(),
        Paragraph('Section IX: Concrete Instances &#8212; '
                  '&#8469;&#8734; and OntologicalStates', S['h1']),
        hr(),
    ]

    E.append(body(
        '<i>Developed in ZPJ_Model.lean and ZPJ_OntBridge.lean to ground the abstraction '
        'chain in concrete types; OntologicalStates takes a shorter path because its '
        'two-element structure cannot support val_scale.</i>',
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
        '&#8469;&#8734; Instances (ZPJ_Model.lean)',
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
        'Derived AFA Content on &#8469;&#8734; (ZPJ_Model.lean &#167; III)',
        [
            'natInf_scale_unique_fp: x + 1 = x &#8658; x = &#8868;. '
            '(The unique fixed point of (&#183; + 1) in &#8469;&#8734; is &#8868;.) &#10003;',
            'natInf_selfMem_singleton: {x : &#8469;&#8734; | x + 1 = x} = {&#8868;}. &#10003;',
            'Via toAbstractSelfApp and toAFAStructure, &#8469;&#8734; carries a full AFAStructure '
            'with all three fields as theorems. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. OntologicalStates &#8212; The Direct AbstractSelfApp Path',
                       S['h2']))
    E.append(body(
        'OntologicalStates = {null, exist} (ZP-B\'s two-element state space) cannot follow the '
        'ValuationStructure path: a finite two-element type has no room for val_scale '
        '(val(scale x) = val(x) + 1 would require infinitely many distinct values). '
        'Instead it takes the direct path to AbstractSelfApp.'))
    E.append(body(
        'The self-application operation is the constant-to-null function: every element maps '
        'to null. null is the unique fixed point because null &#8614; null (fixed_bot) and '
        'exist &#8614; null &#8800; exist (unique_fp holds vacuously for exist). '
        'AFA content follows immediately from the AbstractSelfApp instance.'))
    E.append(def_box(
        'OntologicalStates Instances (ZPJ_OntBridge.lean)',
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
        'Derived AFA Content on OntologicalStates (ZPJ_OntBridge.lean &#167; III)',
        [
            'ont_bot_self_mem: null is self-containing. &#10003;',
            'ont_quine_unique: any two self-containing elements of OntologicalStates are equal. &#10003;',
            'ont_selfMem_singleton: {x | selfMemDerived(x)} = {null}. DC-free. &#10003;',
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
        '<i>Formalised in ZPJ_APG.lean as the most recent addition; this section proves the '
        'full AFA decoration uniqueness theorem for finite accessible pointed graphs, '
        'using the typeclass chain established in Sections VIII&#8211;IX.</i>',
        style='bodyI'))
    E.append(sp(4))

    E.append(Paragraph('I. Accessible Pointed Graphs and Decorations', S['h2']))
    E.append(body(
        'An Accessible Pointed Graph (APG) is a directed graph (Quiver) with a distinguished '
        'root vertex from which every vertex is reachable via directed paths. AFA\'s central '
        'theorem states that every APG has a unique set-theoretic decoration &#8212; a labelling '
        'of vertices by sets satisfying the membership equation d(v) = {d(w) | v &#8594; w}.'))
    E.append(body(
        'ZP-J\'s version of this theorem is stated for an abstract DecorationUniverse rather '
        'than sets. This avoids ZFSet (which satisfies Foundation, making self-loops impossible) '
        'and places the result in the typeclass framework established above.'))
    E.append(def_box(
        'DecorationUniverse Typeclass (ZPJ_APG.lean &#167; II)',
        [
            'class DecorationUniverse (U : Type*) [ZPSemilattice U] [ValuationStructure U] with:',
            '(1) collect_singleton : collect {x} = scale(x)  '
            '&#8212; a singleton set decorates to scale of its element.',
            '(2) collect_ext : collect s&#8321; = collect s&#8322; when s&#8321; = s&#8322;  '
            '&#8212; collect respects set equality.',
            '(3) collect_val_ge : val(collect s) &#8805; val(x) + 1 for x &#8712; s and x &#8800; &#8869;  '
            '&#8212; valuation of a collected set is strictly bounded below.',
            'A valid decoration d : V &#8594; U satisfies d(v) = collect({d(w) | v &#8594; w}) '
            'at every vertex v.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('II. The Valuation Argument for Cyclic Vertices', S['h2']))
    E.append(body(
        'The first key results handle cyclic vertices. If a vertex v lies on a directed cycle '
        'of length k, then composing the decoration equation around the cycle gives '
        'd(v) = scale<sup>k</sup>(d(v)). The valuation argument then forces d(v) = &#8869;: '
        'if d(v) &#8800; &#8869;, then val(scale<sup>k</sup>(d(v))) = val(d(v)) + k &#8800; val(d(v)), '
        'contradicting d(v) = scale<sup>k</sup>(d(v)).'))
    E.append(result_box(
        'Cyclic Vertex Theorems (ZPJ_APG.lean &#167;&#167; III&#8211;VII\')',
        [
            'val_iterate: val(scale<sup>k</sup>(x)) = val(x) + k for x &#8800; &#8869;. &#10003;',
            'scale_iterate_unique_fp: scale<sup>k</sup>(x) = x &#8658; x = &#8869; for k &#8805; 1. &#10003;',
            'pureSelfLoop_decoration_eq_bot: any valid decoration assigns &#8869; to a pure '
            'self-loop vertex. &#10003;',
            'kCycle_node_eq_bot: if d(v) = scale<sup>k</sup>(d(v)) under any valid decoration, '
            'then d(v) = &#8869;. &#10003;',
            'cyclic_decoration_eq_bot: any vertex with a directed cycle through itself '
            'receives &#8869; under any valid decoration. &#10003;',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('III. The Acyclic Case and the "Infinite Period"', S['h2']))
    E.append(body(
        'Cyclic vertices have a finite period k &#8212; the path returns in k steps, and the '
        'valuation argument closes the equation. Acyclic vertices have an "infinite period" &#8212; '
        'the path never returns, so there is no cycle length k to close the equation. This is '
        'the same zero-versus-infinity identification that runs throughout the framework: the '
        'finite k of a cycle is the zero side; its absence is the infinity side.'))
    E.append(body(
        'The hardness of the acyclic proof is that "infinite period" gives you nothing to induct '
        'on. <i>Reach cardinality</i> &#8212; the cardinality of {w | Path v w}, the set of '
        'vertices reachable from v &#8212; serves as a finite proxy. For any child w of an '
        'acyclic vertex v, the reach of w is a strict subset of the reach of v (since v cannot '
        'be reached from w without creating a cycle). Reach cardinality is therefore strictly '
        'decreasing, providing a well-founded measure for the induction.'))
    E.append(result_box(
        'Acyclic Induction and Global Uniqueness (ZPJ_APG.lean &#167;&#167; VIII&#8211;IX)',
        [
            'acyclic_induction_step: if two valid decorations d&#8321;, d&#8322; agree on all '
            'children of an acyclic vertex v, they agree on v. '
            '(From collect_ext applied to the decoration equations.) &#10003;',
            'decoration_unique [Fintype V]: for any finite APG with root r and any two valid '
            'decorations d&#8321;, d&#8322; into any DecorationUniverse, d&#8321; = d&#8322;. '
            'Proof: strong induction on |{w | Path u w}|; cyclic case by cyclic_decoration_eq_bot; '
            'acyclic case by acyclic_induction_step with IH on children. &#10003;',
        ]
    ))
    E.append(sp(6))
    E.append(callout(
        'decoration_unique is the ZP version of AFA\'s decoration uniqueness theorem: for any '
        '<b>finite</b> APG, at most one valid decoration exists into any DecorationUniverse. '
        'The proof uses only the three typeclass axioms and ValuationStructure &#8212; it '
        'characterises when decoration uniqueness holds. It does not construct a specific AFA '
        'model or derive AFA\'s axioms from ZP\'s.',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(6))

    print('[build_zpj] Building registers...')
    E += [hr(), Paragraph('Traceability Register &#8212; ZP-J', S['h1'])]

    trace_rows = [
        ['T-EXEC: Quine atom = &#8869;',
         'AFAStructure.quine_unique + AFAStructure.bot_self_mem',
         'None &#8212; typeclass fields',
         'Lean: t_exec &#8212; axiom-free &#10003;'],
        ['J1: Quine join-identity',
         'T-EXEC + ZP-A A4 (bot_join)',
         'None',
         'Lean: j1_quine_join_identity &#8212; axiom-free &#10003; (was axiom ax_j1 in stub)'],
        ['CC-1 (Derived): S&#8320; = Q &#8658; S&#8320; = &#8869;',
         'T-EXEC',
         'None',
         'Lean: cc1_derived &#8212; axiom-free &#10003; (was ZP-A conditional claim)'],
        ['bot_is_quine_atom',
         'AFAStructure.bot_self_mem + quine_unique',
         'None',
         'Lean: bot_is_quine_atom &#8212; axiom-free &#10003;'],
        ['t_exec_iff: IsQuineAtom &#8596; = &#8869;',
         'T-EXEC + bot_is_quine_atom',
         'None',
         'Lean: t_exec_iff &#8212; axiom-free &#10003;'],
        ['bot_unique: join-identity is unique',
         'ZPE.da2_bottom_characterization',
         'None',
         'Lean: bot_unique &#8212; axiom-free &#10003; (no AFA required)'],
        ['J_self = {&#8869;} (DC-free)',
         'AFAStructure.quine_unique &#8212; one step',
         'None',
         'Lean: J_self_eq_singleton_bot &#8212; no Classical.choice &#10003;'],
        ['singleton_from_unique_witness',
         'Set extensionality (propext)',
         'None',
         'Lean: singleton_from_unique_witness &#8212; axiom-free &#10003;'],
        ['AbstractSelfApp &#8594; AFAStructure',
         'AbstractSelfApp.fixed_bot + unique_fp',
         'None',
         'Lean: toAFAStructure instance &#8212; all fields as theorems &#10003;'],
        ['ValuationStructure &#8594; AbstractSelfApp',
         'ValuationStructure.val_scale + val_unique',
         'None',
         'Lean: scale_unique_fp, toAbstractSelfApp &#8212; axiom-free &#10003;'],
        ['&#8469;&#8734; : ValuationStructure',
         '&#8469;&#8734; arithmetic (WithTop.top_add)',
         'None',
         'Lean: instNatInfZPS, instNatInfVal &#8212; axiom-free &#10003;'],
        ['OntologicalStates : AbstractSelfApp',
         'Constant-to-null map; two-element case analysis',
         'None',
         'Lean: instOntSelfApp &#8212; axiom-free &#10003;'],
        ['cyclic_decoration_eq_bot',
         'val_iterate + scale_iterate_unique_fp',
         'None',
         'Lean: cyclic_decoration_eq_bot &#8212; axiom-free &#10003;'],
        ['decoration_unique [Fintype V]',
         'cyclic_decoration_eq_bot + acyclic_induction_step + Set.ncard',
         '[Fintype V] &#8212; finite graph assumption',
         'Lean: decoration_unique &#8212; propext, Classical.choice, Quot.sound &#10003;'],
        ['AFAStructure.bot_self_mem',
         'AFA (ZF+AFA) &#8212; &#8869; = {&#8869;}',
         'Typeclass field &#8212; proof obligation at instantiation',
         'Not a theorem; a structural prerequisite.'],
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
         'CLOSED &#8212; T-EXEC',
         'CC-1 is now a theorem. The Quine atom = &#8869; is structurally derived. '
         'No freestanding axiom. No modelling commitment beyond AFAStructure typeclass fields.'],
        ['AX-J1 bridge axiom',
         'CLOSED &#8212; J1 derived',
         'The stub version had ax_j1 as a freestanding axiom. '
         'The final version derives J1 from T-EXEC + ZP-A A4. Axiom eliminated.'],
        ['AFAStructure concrete instances',
         'CLOSED &#8212; multiple instances',
         'MachinePhase (ZP-K): machinePhaseAFA : AFAStructure MachinePhase. '
         '&#8469;&#8734;: instNatInfZPS + instNatInfVal &#8594; AbstractSelfApp &#8594; AFA content. '
         'OntologicalStates: instOntSelfApp &#8594; AFA content directly.'],
        ['Aczel DC question (self-membership)',
         'CLOSED &#8212; DC-free',
         'For the self-membership operator, DC is unnecessary. '
         'J_self = {&#8869;} proved in one step via quine_unique. '
         'General set-continuous operators: still open (Aczel\'s "I do not know" stands).'],
        ['DA-1 Path 1 formalisation',
         'PARTIAL &#8212; APG case proved',
         'DA-1 Path 1 (ZP-E) invokes &#8869; = {&#8869;} informally. ZP-J T-EXEC formalises '
         'the identification. decoration_unique (&#167; X) proves uniqueness for finite APGs '
         'over abstract DecorationUniverses. The full ZF+AFA set-theoretic bridge '
         '&#8212; showing the ZP types literally satisfy the ZF+AFA axioms &#8212; '
         'remains outside Lean scope.'],
        ['ZP-A CC-1 label update',
         'OPEN &#8212; editorial',
         'ZP-A still labels CC-1 as a Conditional Claim. With T-EXEC established, '
         'the label can be updated to Derived Theorem (citing ZP-J T-EXEC). '
         'Mathematical content unchanged; editorial update only.'],
        ['Formal ZPSemilattice instance for a ValuationStructure type',
         'OPEN &#8212; gap in chain',
         'ZPJ_Scale.lean proves the ValuationStructure &#8594; AbstractSelfApp chain abstractly. '
         'Connecting a concrete type (e.g. a 2-adic type or ZP state space) to both '
         'ZPSemilattice and ValuationStructure in the same instance requires a bridge file '
         'importing ZP-A and ZP-B. The &#8469;&#8734; instance (ZPJ_Model.lean) fills this for '
         'the abstract model; a concrete ZP-grounded instance remains future work.'],
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
            'CC-1 derived &#8212; no freestanding axioms | '
            'DC-free: J_self = {&#8869;} without Dependent Choice | '
            'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure | '
            'Instances: &#8469;&#8734;, OntologicalStates | '
            'decoration_unique: any two valid decorations of a finite APG agree | '
            'All results sorry-free in Lean 4</i>',
            S['endnote']),
    ]

    print(f'[build_zpj] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zpj] Written: {out_path}')


if __name__ == '__main__':
    build()
