"""
Build ZP-D Illustrated Companion (v1.4)
Changes from v1.3:
- T5-b added: every genuine state transition produces an orthogonal shift
  (not just the Binary Snap). Key result box added after T4.
Changes from v1.2:
- n=2 foundational minimum explained in "What Is ZP-D Doing?"
- R3 (T locally constant and continuous) noted near the T operator key results
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF

def t_map_diagram():
    """Q₂ (totally disconnected) → T → H=ℂⁿ (orthogonality). Two panels."""
    dw, dh = TW, 2.2 * inch
    d = Drawing(dw, dh)

    # Left panel: Q2 with nested circles (topology)
    lx = dw * 0.22
    cy = dh * 0.50

    r_outer = 70
    r_inner = 35
    d.add(Circle(lx, cy, r_outer, fillColor=colors.HexColor('#C8EAEA'),
                 strokeColor=COMP_BLUE, strokeWidth=1.2))
    d.add(Circle(lx, cy, r_inner, fillColor=colors.HexColor('#88CCCC'),
                 strokeColor=COMP_BLUE, strokeWidth=1.2))
    # x dot
    d.add(Circle(lx + 42, cy - 15, 5, fillColor=COMP_BLUE, strokeColor=COMP_BLUE, strokeWidth=0))
    d.add(String(lx + 49, cy - 20, 'x', fontSize=9, fontName='DV-B', fillColor=COMP_BLUE))
    # 0 dot
    d.add(Circle(lx, cy, 6, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(lx + 9, cy - 5, '0', fontSize=9, fontName='DV-B', fillColor=COMP_AMBER))
    # Label
    d.add(String(lx - 50, cy - r_outer - 18, 'Q2 (topology)', fontSize=9,
                 fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(lx - 50, cy - r_outer - 30, 'totally disconnected', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#555555')))

    # Arrow T in middle
    ax1 = dw * 0.44
    ax2 = dw * 0.56
    ay  = cy
    d.add(Line(ax1, ay, ax2, ay, strokeColor=BLACK, strokeWidth=2))
    d.add(Line(ax2 - 8, ay - 5, ax2, ay, strokeColor=BLACK, strokeWidth=2))
    d.add(Line(ax2 - 8, ay + 5, ax2, ay, strokeColor=BLACK, strokeWidth=2))
    d.add(String(dw/2 - 6, ay + 8, 'T', fontSize=11, fontName='DV-B', fillColor=BLACK))
    d.add(String(dw/2 - 28, ay - 16, '(basis', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#666666')))
    d.add(String(dw/2 - 32, ay - 27, 'assignment)', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#666666')))

    # Right panel: H = ℂⁿ with two orthogonal axes
    rx = dw * 0.79
    # e1 axis (vertical)
    e1y_top = cy + 75
    d.add(Line(rx, cy - 20, rx, e1y_top, strokeColor=COMP_BLUE, strokeWidth=2))
    d.add(Line(rx - 5, e1y_top - 8, rx, e1y_top, strokeColor=COMP_BLUE, strokeWidth=2))
    d.add(Line(rx + 5, e1y_top - 8, rx, e1y_top, strokeColor=COMP_BLUE, strokeWidth=2))
    d.add(String(rx + 6, e1y_top - 4, 'e', fontSize=9, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(rx + 14, e1y_top - 9, '1', fontSize=6, fontName='DV-B', fillColor=COMP_BLUE))
    # e0 axis (horizontal)
    e0x_right = rx + 75
    d.add(Line(rx - 20, cy, e0x_right, cy, strokeColor=COMP_AMBER, strokeWidth=2))
    d.add(Line(e0x_right - 8, cy - 5, e0x_right, cy, strokeColor=COMP_AMBER, strokeWidth=2))
    d.add(Line(e0x_right - 8, cy + 5, e0x_right, cy, strokeColor=COMP_AMBER, strokeWidth=2))
    d.add(String(e0x_right - 2, cy - 16, 'e', fontSize=9, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(e0x_right + 6, cy - 21, '0', fontSize=6, fontName='DV-B', fillColor=COMP_AMBER))
    # Origin dot
    d.add(Circle(rx, cy, 4, fillColor=BLACK, strokeColor=BLACK, strokeWidth=0))
    # Right-angle box
    sq = 10
    d.add(Rect(rx, cy, sq, sq, fillColor=colors.white,
               strokeColor=colors.HexColor('#888888'), strokeWidth=0.8))
    # Inner product label
    d.add(String(rx - 48, cy - 36, '⟨e', fontSize=8.5, fontName='DV-B',
                 fillColor=colors.HexColor('#444444')))
    d.add(String(rx - 29, cy - 40, '0', fontSize=6, fontName='DV-B',
                 fillColor=colors.HexColor('#444444')))
    d.add(String(rx - 23, cy - 36, ', e', fontSize=8.5, fontName='DV-B',
                 fillColor=colors.HexColor('#444444')))
    d.add(String(rx - 6, cy - 40, '1', fontSize=6, fontName='DV-B',
                 fillColor=colors.HexColor('#444444')))
    d.add(String(rx, cy - 36, '⟩ = 0', fontSize=8.5, fontName='DV-B',
                 fillColor=colors.HexColor('#444444')))
    # Labels
    d.add(String(rx - 28, cy - r_outer - 18, 'H = Cn (state space)', fontSize=9,
                 fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(rx - 28, cy - r_outer - 30, 'isolation → orthogonality', fontSize=7.5,
                 fontName='DV-I', fillColor=colors.HexColor('#555555')))

    d.add(String(dw/2 - 155, dh - 14,
                 'T maps topological isolation to orthogonality — a 90° turn in state space',
                 fontSize=8.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-D_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-D Companion  |  State Layer (Hilbert Space)  |  May 2026  |  v1.4')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-D Illustrated Companion',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header banner ──────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-D Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('How topology maps to quantum state space', CS['title']),
        Paragraph('State Layer (Hilbert Space) | Version 1.4', CS['subtitle']),
        Paragraph('ZP Companion | May 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── Page 1: grounding section — NEW ────────────────────────────────────────
    E.append(Paragraph('Background: Vectors and Orthogonality', CS['h1']))
    E.append(cbody(
        'ZP-D works with objects called <b>vectors</b>. A vector is simply a quantity that has '
        'both a size and a direction — an arrow in space. You can add vectors (combine the '
        'arrows tip-to-tail) and scale them (stretch or shrink). A <b>vector space</b> is a '
        'collection of vectors where these operations always produce another vector in the '
        'collection.'))
    E.append(cbody(
        'The key relationship between vectors is <b>orthogonality</b> — which just means '
        'perpendicular. Two vectors are orthogonal when they share no common direction: '
        'pointing entirely independently of each other. In 2D, North and East are orthogonal. '
        'In 3D, you can have three mutually orthogonal directions. In higher-dimensional '
        'abstract spaces the same idea extends: orthogonal vectors are completely independent, '
        'with zero overlap.'))
    E.append(cbody(
        'Orthogonality is measured by the <b>inner product</b> ⟨u, v⟩: a number that captures '
        'how much two vectors "point in the same direction." When ⟨u, v⟩ = 0, the vectors are '
        'orthogonal — they have nothing in common.'))
    E.append(example_box('Real-world example — Compass directions', [
        'North and East are orthogonal — perpendicular, sharing nothing. If you know how far '
        'north something is, that tells you nothing about how far east it is. ZP-D says: states '
        'that are topologically isolated in ℚ₂ (no continuous path connects them) should be '
        'represented as orthogonal vectors in H (no shared component). Geometric independence '
        'matches topological isolation.',
    ]))
    E.append(sp(4))

    # ── What ZP-D does ─────────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-D Doing?', CS['h1']))
    E.append(cbody(
        'ZP-D builds a bridge between the p-adic topology of ZP-B and a Hilbert space '
        'H = ℂⁿ. A Hilbert space is a vector space equipped with an inner product — the '
        'operation that measures orthogonality. The ℂⁿ notation means the vectors have '
        'n complex-number components rather than n real-number components. (Complex numbers '
        'extend the real number line by adding an imaginary dimension; they are the natural '
        'language of quantum mechanics, but the geometric intuition of vectors and perpendicularity '
        'carries over directly.)'))
    E.append(cbody(
        'ZP-D constructs an explicit map T: ℚ₂ → H that carries the topological structure of '
        'ℚ₂ into the state geometry of H. The central insight: topological isolation in ℚ₂ '
        'corresponds to orthogonality in H. States with no continuous path between them are '
        'represented as perpendicular vectors.'))
    E.append(cbody(
        'ZP-D works with exactly two foundational states: the Null State (⊥, non-existence) '
        'and the first non-null state (ε₀, existence). This is not a simplifying assumption — '
        'it is the irreducible minimum. The core question is whether any transition from ⊥ to '
        'a first state is possible, and for that question n=2 is the smallest meaningful case. '
        'No claim in ZP-D requires n > 2. Binary is the logical ground floor, not a placeholder '
        'for a more general construction.'))

    # ── Page 2: T operator ─────────────────────────────────────────────────────
    E.append(Paragraph('The Transition Operator T', CS['h1']))
    E.append(cbody(
        'T is constructed by <b>basis assignment</b>: the clopen ball partition of ℚ₂ maps to '
        'an orthonormal basis of H. An <b>orthonormal basis</b> is a set of vectors that are '
        'mutually orthogonal (all inner products equal zero) and each have length exactly 1. '
        'Think of it as a coordinate system where every axis is perpendicular to every other '
        'and all axes are the same length.'))
    E.append(cbody(
        'The element 0 maps to e₀; the first non-zero state ε₀ maps to e₁; and so on. Because '
        'clopen balls are completely separated (ZP-B), their images under T are orthogonal in H.'))
    E.append(t_map_diagram())
    E.append(ccaption(
        'T maps topological isolation (left, ℚ₂) to orthogonality (right, H = ℂⁿ). '
        '0 (amber) maps to e₀. Non-zero point x maps to e₁. Topological isolation '
        'becomes orthogonality: ⟨e₀, e₁⟩ = 0.'))
    E.append(sp(6))

    E.append(example_box('Real-world example — Red and blue channels in an image', [
        'In digital images, the red and blue channels are orthogonal: changing one has no effect '
        'on the other. ZP-D maps topologically distinct states (no path between them) to '
        'independent dimensions in H (no overlap between vectors). Independence in topology '
        'becomes independence in geometry.',
    ]))
    E.append(remember_box(
        'Remember: Image processing illustrates orthogonality, not the content of the framework. '
        'H is an abstract mathematical space; its elements become physical states only when the '
        'framework is instantiated with specific physical parameters.'))
    E.append(sp(6))

    # ── Key results ────────────────────────────────────────────────────────────
    E.append(key_result_box('Key Result: T Exists and is Unique up to Rotation (T2, T3)',
        'T can be explicitly constructed by basis assignment (T2). It is unique up to a '
        'rotation of the basis (T3) — meaning any two valid T operators differ only in which '
        'direction they label as "e₀" vs. "e₁" vs. "e₂" etc. This is called unitary '
        'equivalence: like choosing different compass orientations for a map, the underlying '
        'geometry is the same. Two maps that agree on distances but point north differently '
        'are equivalent in all the ways that matter.'))
    E.append(sp(4))
    E.append(cbody(
        '<b>R3 — T respects the topology:</b> A map between topological spaces can introduce '
        'discontinuities that were not present in the original space. R3 establishes that T '
        'does not do this — T is locally constant and continuous with respect to the p-adic '
        'topology of ℚ₂. It does not invent jumps or boundaries that are absent from the source '
        'structure. The orthogonal geometry of H reflects exactly the topological structure of ℚ₂, '
        'nothing more.'))
    E.append(sp(6))
    E.append(key_result_box('Key Result: The Snap Produces an Orthogonal Shift (T4)',
        'The Binary Snap — 0 → ε₀ in ℚ₂ — maps to a shift from e₀ to e₁ in H such that '
        '⟨e₀, e₁⟩ = 0. The Snap is a right-angle turn in state space.'))
    E.append(sp(4))
    E.append(key_result_box('Key Result: Every Genuine Transition Produces an Orthogonal Shift (T5-b)',
        'The Snap is not a special case. For any state sequence, whenever two consecutive '
        'states are distinct — meaning the sequence actually moved — their T-images in H '
        'are orthogonal. Each genuine transition opens a new direction. The whole ascending '
        'chain, not just the first step, unfolds through orthogonal shifts. '
        'Lean: ZPD.t5_strict_orthogonal (axiom-free, via DP-1).'))
    E.append(sp(8))

    E.append(cbody(
        '<b>Design Commitment DP-1:</b> The choice to represent topological isolation as '
        'orthogonality is a design commitment — the natural and consistent choice, stated '
        'explicitly. Other faithful representations exist in principle. This honesty about '
        'what is chosen versus derived is central to the framework.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
