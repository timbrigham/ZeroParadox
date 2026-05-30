"""
Zero Paradox — ZP-J AFA Addendum: Decoration Uniqueness from Valuation Structure
Version 1.0 | May 2026
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

VERSION = '1.0'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_AFA_Addendum.pdf')
    print(f'[build_zpj_afa_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-J AFA Addendum',
                   'ZP-J AFA Addendum', 'Version ' + VERSION,
                   date_str='May 2026')
    E = []

    print('[build_zpj_afa_addendum] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-J AFA Addendum', S['title']),
        Paragraph('Decoration Uniqueness from Valuation Structure', S['subtitle']),
        Paragraph('Version ' + VERSION + ' | May 2026', S['subtitle']),
        Paragraph(
            '<i>v1.0: Initial release. Presents the derivation chain from '
            'ValuationStructure to AFA decoration uniqueness for finite Accessible '
            'Pointed Graphs. All theorems proved sorry-free in Lean 4. '
            'Reads after ZP-J Self-Reference. '
            'Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble ────────────────────────────────────────────────────────────────
    print('[build_zpj_afa_addendum] Building preamble...')
    E.append(body(
        'This document presents the formal consequences of ZP-J\'s valuation framework '
        'for the central uniqueness theorem of Aczel\'s Anti-Foundation Axiom (AFA). '
        'The main result is decoration_unique (ZPJ_APG.lean §IX): for any finite '
        'Accessible Pointed Graph, any two valid decorations must agree at every vertex. '
        'The proof does not import set-theoretic AFA axioms. It derives the uniqueness '
        'property from a chain of abstract typeclasses whose root is ValuationStructure, '
        'established in ZP-J.'))
    E.append(body(
        'Readers of ZP-J Self-Reference will recognise the key move: &#8869; is the '
        'unique fixed point of scale because any non-&#8869; element has finite depth, '
        'and scale increases depth by 1. The same argument, iterated k times, forces '
        'every vertex on a directed cycle of length k to carry decoration &#8869;. '
        'Acyclic vertices are handled by strong induction on the size of the reachable '
        'set. Both cases together give decoration_unique.'))
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
        'Typeclass: ValuationStructure (ZPJ_Scale.lean)',
        [
            'class ValuationStructure (L : Type*) [ZPSemilattice L] where',
            '  scale      : L &#8594; L             -- self-application',
            '  val        : L &#8594; &#8469;&#8734;  -- depth measure',
            '  scale_bot  : scale &#8869; = &#8869;   -- &#8869; is a fixed point of scale',
            '  val_bot    : val &#8869; = &#8734;      -- &#8869; has infinite depth',
            '  val_unique : &#8704; x, val x = &#8734; &#8594; x = &#8869;'
            '               -- infinite depth identifies &#8869;',
            '  val_scale  : &#8704; x &#8800; &#8869;, val (scale x) = val x + 1'
            '               -- scale strictly increases depth',
        ]
    ))
    E.append(sp(4))

    E.append(body(
        'The four axioms are minimal. val_bot and val_scale together give the key '
        'consequence: for any x &#8800; &#8869;, val(x) is finite, and applying scale '
        'strictly increases it. No element with finite depth can therefore satisfy '
        'scale(x) = x.'))

    E.append(result_box(
        'Theorem: scale_unique_fp (ZPJ_Scale.lean)',
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
        'Aczel\'s three-field characterisation of the Quine atom property &#8212; '
        'is then derived from AbstractSelfApp. At each step, the fields of the target '
        'typeclass are proved as theorems from the source. No new axioms are introduced.'))

    E.append(def_box(
        'Typeclass: AbstractSelfApp (ZPJ_SelfApp.lean)',
        [
            'class AbstractSelfApp (L : Type*) [ZPSemilattice L] where',
            '  selfApp   : L &#8594; L',
            '  fixed_bot : selfApp &#8869; = &#8869;',
            '  unique_fp : &#8704; x : L, selfApp x = x &#8594; x = &#8869;',
            '',
            'Instance toAbstractSelfApp (ZPJ_Scale.lean):',
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
        'In ZF+AFA these follow from AFA\'s own decoration uniqueness clause. In the '
        'ZP encoding they are class fields &#8212; asserted once at the typeclass level '
        'rather than proved from the graph-decoration semantics.'))

    E.append(def_box(
        'Typeclass: AFAStructure (ZPJ.lean)',
        [
            'class AFAStructure (L : Type*) [ZPSemilattice L] where',
            '  selfMem      : L &#8594; Prop',
            '  quine_unique : &#8704; x y : L, selfMem x &#8594; selfMem y &#8594; x = y',
            '  bot_self_mem : selfMem &#8869;',
            '',
            'Instance toAFAStructure (ZPJ_SelfApp.lean):',
            '  selfMem      := &#955; x, selfApp x = x   (fixed-point predicate)',
            '  bot_self_mem := fixed_bot                 (&#8869; is a fixed point)',
            '  quine_unique := derived from unique_fp    (any fixed point is &#8869;)',
            'No new axioms.',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Proposition: Derivation Chain (ZPJ_Scale.lean, ZPJ_SelfApp.lean)',
        [
            'ValuationStructure L  &#8658;  AbstractSelfApp L  &#8658;  AFAStructure L',
            'Each arrow is a Lean instance derivation proved without new axioms.',
            'Any type satisfying ValuationStructure inherits the full AFAStructure '
            'as a chain of theorems.',
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
            'abstraction and says nothing about which set-theoretic axioms hold.',
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
        'Definition: Accessible Pointed Graph (ZPJ_APG.lean §I)',
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
        'Typeclass: DecorationUniverse (ZPJ_APG.lean §II)',
        [
            'class DecorationUniverse (U : Type*) [ZPSemilattice U]',
            '      [ValuationStructure U] where',
            '  collect : Set U &#8594; U',
            '  collect_singleton : &#8704; x : U, collect {x} = scale x',
            '  collect_val_ge : &#8704; (S : Set U) (x : U), x &#8712; S &#8594;'
            '                   val (collect S) &#8805; val x + 1',
            '',
            'IsDecoration d  means:  &#8704; v, d v = collect (d &#8220;&#8242; children v)',
            '  where d &#8220;&#8242; children v = { d w | w &#8712; children v }',
            '  is the image of the successor set under d.',
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
        'Theorem: decoration_unique (ZPJ_APG.lean §IX)',
        [
            '&#8704; {V : Type*} [Quiver V] [Fintype V]',
            '  {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]',
            '  (d&#8321; d&#8322; : V &#8594; U),',
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
    E.append(body(
        'The key tool is the iterated valuation lemma. If v lies on a cycle of length '
        'k &#8805; 1, the decoration equation applied k times around the cycle gives '
        'd(v) = scale&#7503;(d(v)). For any x &#8800; &#8869;, val(scale&#7503;(x)) = '
        'val(x) + k (val_iterate), so a fixed point would require val(x) = val(x) + k '
        '&#8212; impossible for finite val. Therefore d(v) = &#8869;.'))

    E.append(result_box(
        'Lemma: val_iterate (ZPJ_APG.lean §III)',
        [
            '&#8704; (x : U) (hx : x &#8800; &#8869;) (k : &#8469;),',
            '  val (scale^[k] x) = val x + k',
            'For any x &#8800; &#8869;, applying scale k times increases depth by exactly k.',
            'Proof: induction on k; val_scale applies at each step because '
            'scale^[n](x) &#8800; &#8869; follows from the induction hypothesis '
            'and finiteness of val(x).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: scale_iterate_unique_fp (ZPJ_APG.lean §IV)',
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
        'Theorem: cyclic_decoration_eq_bot (ZPJ_APG.lean §VIII)',
        [
            '&#8704; (d : V &#8594; U), IsDecoration d &#8594;',
            '  (v lies on a directed cycle) &#8594; d v = &#8869;',
            'Consequence: d&#8321; v = d&#8322; v = &#8869; for every cyclic vertex v.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(Paragraph('IV.2 — Acyclic Vertices', S['h2']))
    E.append(body(
        'A vertex v is acyclic if no directed cycle passes through it. The argument '
        'uses strong induction on |Reach(v)|.'))
    E.append(body(
        '<b>Base case.</b> If v has no successors, children(v) = &#8709;. The '
        'decoration equation gives d(v) = collect(&#8709;). Both d&#8321; and d&#8322; '
        'are constrained to the same value and agree at v.'))
    E.append(body(
        '<b>Inductive step.</b> Suppose d&#8321; and d&#8322; agree on every vertex w '
        'with |Reach(w)| &lt; n, and suppose |Reach(v)| = n. For each successor '
        'w &#8712; children(v): since v is acyclic, v is not reachable from w, so '
        'w &#8800; v and Reach(w) &#8842; Reach(v), giving |Reach(w)| &lt; n. '
        'By the induction hypothesis, d&#8321;(w) = d&#8322;(w) for every '
        'w &#8712; children(v). The decoration equation then gives '
        'd&#8321;(v) = collect(d&#8321; &#8220;&#8242; children(v)) = '
        'collect(d&#8322; &#8220;&#8242; children(v)) = d&#8322;(v).'))

    E.append(result_box(
        'Lemma: acyclic_induction_step (ZPJ_APG.lean §VIII)',
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

    E.append(label_box(
        'Lean Source Files',
        [
            'ZPJ_Scale.lean     &#8212; ValuationStructure, scale_unique_fp, '
            'toAbstractSelfApp',
            'ZPJ_SelfApp.lean   &#8212; AbstractSelfApp, derived_bot_self_mem, '
            'derived_quine_unique, toAFAStructure',
            'ZPJ_AczelConn.lean &#8212; J_self, selfMem_determines_singleton, '
            'DC-free identification theorems',
            'ZPJ_OntBridge.lean &#8212; OntologicalStates as AbstractSelfApp instance',
            'ZPJ_Model.lean     &#8212; &#8469;&#8734; as ValuationStructure instance',
            'ZPJ_ScaleBridge.lean &#8212; &#8484;&#8322; as ValuationStructure instance '
            '(via ValBridge typeclass)',
            'ZPJ_APG.lean       &#8212; APG, DecorationUniverse, val_iterate, '
            'scale_iterate_unique_fp, cyclic_decoration_eq_bot, '
            'acyclic_induction_step, decoration_unique',
            'All files in ZeroParadox/ in the public repository.',
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
            'every APG has a unique decoration into the universe of non-well-founded sets, '
            'proved using the AFA axiom itself. ZP-J derives the uniqueness half for '
            'abstract DecorationUniverses from ValuationStructure alone &#8212; without '
            'importing set-theoretic AFA. The mechanism differs: Aczel takes AFA as a '
            'hypothesis; ZP-J derives the same uniqueness property from the depth-measure '
            'structure. Whether Aczel\'s existence half can be similarly derived for '
            'abstract DecorationUniverses is an open question.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after '
        'it. The derivation chain (ValuationStructure &#8594; AbstractSelfApp &#8594; '
        'AFAStructure) is established in ZP-J; this document applies it to the APG '
        'decoration problem. Version 1.0 covers the uniqueness result for finite graphs. '
        'All results sorry-free in Lean 4 as of May 2026.',
        S['endnote']))

    print(f'[build_zpj_afa_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
