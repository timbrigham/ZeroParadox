"""
zp_utils.py — Shared utilities for Zero Paradox PDF build scripts.

All build scripts import this module to get fonts, colours, layout constants,
styles, and component helpers. Each script's build() function contains only the
document-specific content; nothing here changes between documents.

Usage (formal docs):
    from zp_utils import *

Usage (companion docs):
    from zp_utils import *
    # CS styles, example_box, remember_box, key_result_box are all available.
"""
import os, sys
sys.stdout.reconfigure(encoding='utf-8')

from reportlab.lib import colors
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                 Table, TableStyle, PageBreak, HRFlowable)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# ── Paths ─────────────────────────────────────────────────────────────────────
SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)
FONT_DIR     = os.path.join(SCRIPT_DIR, 'fonts') + os.sep

# ── Font registration ─────────────────────────────────────────────────────────
# DejaVuSans: sans-serif UI elements (headings, table headers, footers, checkmarks)
# STIXTwo-Math: body text and all mathematical content
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'STIXTwo-Math.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'STIXTwo-Math.ttf'))

# ── Colours ───────────────────────────────────────────────────────────────────
# Formal document palette
BLUE       = colors.HexColor('#2E75B6')
BLUE_LITE  = colors.HexColor('#D5E8F0')
GREY_LITE  = colors.HexColor('#F5F5F5')
BLACK      = colors.black
WHITE      = colors.white
# Companion / shared palette
COMP_BLUE  = colors.HexColor('#4D89C0')
COMP_GREEN = colors.HexColor('#4D9050')
COMP_SLATE = colors.HexColor('#60727B')
COMP_AMBER = colors.HexColor('#BB8C26')
SLATE_LITE = colors.HexColor('#ECEFF1')
AMBER_LITE = colors.HexColor('#FFF8E7')
AMBER      = COMP_AMBER          # alias for callout() clarity
RED        = colors.HexColor('#CC0000')
GREY       = colors.HexColor('#888888')
GREY_TEXT  = colors.HexColor('#555555')
TEAL       = colors.HexColor('#1E7B74')
TEAL_LITE  = colors.HexColor('#D0EDED')
GREEN      = colors.HexColor('#2E7D32')
GREEN_LITE = colors.HexColor('#E8F5E9')
GREEN_DARK = colors.HexColor('#1B5E20')
ORANGE     = colors.HexColor('#BF4E30')
ORANGE_LITE= colors.HexColor('#FBE9E7')
SLATE      = colors.HexColor('#455A64')
INDIGO     = colors.HexColor('#3949AB')
INDIGO_LITE= colors.HexColor('#E8EAF6')

# ── Layout constants ──────────────────────────────────────────────────────────
TW         = 6.5 * inch          # text width
LM = RM = TM = BM = 1.0 * inch  # margins

# ── Formal document styles (S) ────────────────────────────────────────────────
S = {
    'title':    ParagraphStyle('title',    fontName='DV-B',  fontSize=18, leading=24,
                               spaceAfter=6,  alignment=1),
    'subtitle': ParagraphStyle('subtitle', fontName='DV-I',  fontSize=11, leading=15,
                               spaceAfter=4,  alignment=1),
    'h1':       ParagraphStyle('h1',       fontName='DV-B',  fontSize=13, leading=18,
                               spaceBefore=14, spaceAfter=5, textColor=BLUE),
    'h2':       ParagraphStyle('h2',       fontName='DV-B',  fontSize=11, leading=15,
                               spaceBefore=10, spaceAfter=4, textColor=BLUE),
    'h3':       ParagraphStyle('h3',       fontName='DV-B',  fontSize=10, leading=14,
                               spaceBefore=8,  spaceAfter=3),
    'body':     ParagraphStyle('body',     fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'bodyI':    ParagraphStyle('bodyI',    fontName='DVS-I', fontSize=10, leading=14,
                               spaceAfter=6),
    'label':    ParagraphStyle('label',    fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=WHITE),
    'cell':     ParagraphStyle('cell',     fontName='DVS',   fontSize=9,  leading=13),
    'cellB':    ParagraphStyle('cellB',    fontName='DVS-B', fontSize=9,  leading=13),
    'cellSans': ParagraphStyle('cellSans', fontName='DV',    fontSize=9,  leading=13),
    'cellI':    ParagraphStyle('cellI',    fontName='DVS-I', fontSize=9,  leading=13),
    'footer':   ParagraphStyle('footer',   fontName='DV-I',  fontSize=8,  leading=10,
                               textColor=colors.grey, alignment=1),
    'note':     ParagraphStyle('note',     fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=4),
    'li':       ParagraphStyle('li',       fontName='DVS',   fontSize=10, leading=14,
                               leftIndent=18, spaceAfter=3),
    'derived':  ParagraphStyle('derived',  fontName='DVS-B', fontSize=10, leading=14,
                               spaceAfter=6, textColor=GREEN_DARK),
    'endnote':  ParagraphStyle('endnote',  fontName='DVS-I', fontSize=9,  leading=13,
                               alignment=1),
}

# ── Companion styles (CS) ─────────────────────────────────────────────────────
CS = {
    'title':    ParagraphStyle('ctitle',    fontName='DV-B',  fontSize=22, leading=28,
                               alignment=1, spaceAfter=4, textColor=BLACK),
    'subtitle': ParagraphStyle('csubtitle', fontName='DV-I',  fontSize=12, leading=16,
                               alignment=1, spaceAfter=4),
    'meta':     ParagraphStyle('cmeta',     fontName='DV',    fontSize=9,  leading=13,
                               alignment=1, spaceAfter=8, textColor=colors.grey),
    'disc':     ParagraphStyle('cdisc',     fontName='DVS-I', fontSize=9,  leading=13,
                               spaceAfter=10, textColor=colors.HexColor('#555555')),
    'h1':       ParagraphStyle('ch1',       fontName='DV-B',  fontSize=13, leading=17,
                               spaceBefore=14, spaceAfter=5, textColor=COMP_BLUE),
    'body':     ParagraphStyle('cbody',     fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'caption':  ParagraphStyle('ccaption',  fontName='DVS-I', fontSize=9,  leading=12,
                               spaceAfter=8, textColor=colors.HexColor('#555555')),
    'ex_title': ParagraphStyle('cex_title', fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=COMP_AMBER),
    'ex_body':  ParagraphStyle('cex_body',  fontName='DVS',   fontSize=9,  leading=13),
    'rem':      ParagraphStyle('crem',      fontName='DVS-I', fontSize=9,  leading=13),
    'kr_hdr':   ParagraphStyle('ckr_hdr',   fontName='DVS-B', fontSize=9,  leading=13,
                               textColor=WHITE),
    'kr_body':  ParagraphStyle('ckr_body',  fontName='DVS',   fontSize=9,  leading=13),
}

# ── Universal helpers ─────────────────────────────────────────────────────────
def sp(n=6):
    """Vertical spacer."""
    return Spacer(1, n)

def chk():
    """Unicode checkmark in DV font."""
    return '<font name="DV">&#10003;</font>'

def fix(text):
    """
    Convert Unicode math symbols to ReportLab-safe HTML entities and markup.
    Handles subscripts, superscripts, operators, Greek letters, and blackboard bold.
    Required because ReportLab's XML parser does not handle raw Unicode math well.
    """
    sub_map = {'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4',
               '₅':'5','₆':'6','₇':'7','₈':'8','₉':'9',
               'ₙ':'n','ₖ':'k','ₘ':'m','ᵢ':'i','ⱼ':'j',
               '₊':'+','₋':'-'}
    sup_map = {'⁰':'0','¹':'1','²':'2','³':'3','⁴':'4',
               '⁵':'5','⁶':'6','⁷':'7','⁸':'8','⁹':'9',
               'ⁿ':'n','ᵏ':'k'}
    for ch, rep in sub_map.items():
        text = text.replace(ch, f'<sub>{rep}</sub>')
    for ch, rep in sup_map.items():
        text = text.replace(ch, f'<super>{rep}</super>')
    text = text.replace('✓', '<font name="DV">&#10003;</font>')
    text = text.replace('✗', '<font name="DV">&#10007;</font>')
    text = text.replace('∅', '<font name="DV">&#8709;</font>')
    for char, entity in [
        ('⊥','&#8869;'),  ('∨','&#8744;'),  ('∧','&#8743;'),
        ('≤','&#8804;'),  ('≥','&#8805;'),  ('≠','&#8800;'),
        ('∈','&#8712;'),  ('∉','&#8713;'),  ('⊆','&#8838;'),
        ('∪','&#8746;'),  ('∩','&#8745;'),  ('∀','&#8704;'),
        ('∃','&#8707;'),  ('∞','&#8734;'),  ('∑','&#8721;'),
        ('→','&#8594;'),  ('←','&#8592;'),  ('↔','&#8596;'),
        ('⇒','&#8658;'),  ('⟺','&#10234;'), ('⟹','&#10233;'),
        ('⟨','&#10216;'), ('⟩','&#10217;'), ('‖','&#8214;'),
        ('—','&#8212;'),  ('–','&#8211;'),  ('·','&#183;'),
        ('×','&#215;'),   ('−','&#8722;'),  ('≡','&#8801;'),
        ('∘','&#8728;'),  ('⊗','&#8855;'),  ('⊕','&#8853;'),
        ('∥','&#8741;'),  ('≺','&#8826;'),  ('≻','&#8827;'),
        ('ε','&#949;'),   ('α','&#945;'),   ('β','&#946;'),
        ('γ','&#947;'),   ('δ','&#948;'),   ('η','&#951;'),
        ('σ','&#963;'),   ('π','&#960;'),   ('λ','&#955;'),
        ('Δ','&#916;'),   ('Σ','&#931;'),   ('Γ','&#915;'),   ('Λ','&#923;'),
        ('ℚ','&#8474;'),  ('ℤ','&#8484;'),  ('ℂ','&#8450;'),
        ('ℕ','&#8469;'),  ('ℝ','&#8477;'),
    ]:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    """Paragraph in the given S style key (default: body)."""
    return Paragraph(fix(text), S[style])

def hr():
    """Thin horizontal rule."""
    return HRFlowable(width='100%', thickness=0.5,
                      color=colors.HexColor('#AAAAAA'),
                      spaceAfter=6, spaceBefore=2)

def li(text):
    """Bullet list item."""
    return Paragraph('&#8226;  ' + fix(text), S['li'])

def derived(text):
    """Green bold paragraph for derived results."""
    return Paragraph(fix(text), S['derived'])

def cbody(t):
    """Companion body paragraph."""
    return Paragraph(fix(t), CS['body'])

def ccaption(t):
    """Companion caption paragraph."""
    return Paragraph(fix(t), CS['caption'])

# ── Formal document components ────────────────────────────────────────────────
def _colored_box(title, rows, hdr_color):
    """Generic colored-header single-column box for formal documents."""
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  hdr_color),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, hdr_color),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, hdr_color),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

# Semantic box helpers:
# result_box  → GREEN   — Theorems, Propositions, Lemmas, Corollaries
# axiom_box   → ORANGE  — Axioms, Design Principles, Conditional Claims
# def_box     → BLUE    — Definitions, Typeclasses
# remark_box  → SLATE   — Remarks
# import_box  → AMBER   — Imported results from other layers
def result_box(title, rows): return _colored_box(title, rows, GREEN)
def axiom_box(title, rows):  return _colored_box(title, rows, ORANGE)
def def_box(title, rows):    return _colored_box(title, rows, BLUE)
def remark_box(title, rows): return _colored_box(title, rows, SLATE)
def import_box(title, rows): return _colored_box(title, rows, AMBER)

def label_box(title, rows_list):
    """Blue-header single-column info box used throughout formal documents."""
    data = [[Paragraph(fix(title), S['label'])]]
    for r in rows_list:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('TEXTCOLOR',     (0,0), (-1,0),  WHITE),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('LINEBEFORE',    (0,0), (-1,-1), 0.5, colors.HexColor('#CCCCCC')),
        ('LINEAFTER',     (0,0), (-1,-1), 0.5, colors.HexColor('#CCCCCC')),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t

def data_table(headers, rows_data, col_widths, header_bg=None):
    """Multi-column data table with blue (or custom) header row."""
    if header_bg is None:
        header_bg = BLUE
    hdr_row = [Paragraph(fix(h), S['label']) for h in headers]
    data = [hdr_row]
    for row in rows_data:
        data.append([Paragraph(fix(str(c)), S['cell']) for c in row])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  header_bg),
        ('BACKGROUND',    (0,1), (-1,-1), GREY_LITE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, GREY_LITE]),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('LINEAFTER',     (0,0), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 4),
        ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ('LEFTPADDING',   (0,0), (-1,-1), 6),
        ('RIGHTPADDING',  (0,0), (-1,-1), 6),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=col_widths, repeatRows=1)
    t.setStyle(ts)
    return t

def make_doc(path, title_str, doc_id, version_str, date_str='April 2026'):
    """SimpleDocTemplate with standard Zero Paradox footer."""
    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            f'Zero Paradox {doc_id}  |  {version_str}  |  {date_str}  |  Page {doc.page}',
        )
        canvas.restoreState()
    return SimpleDocTemplate(
        path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title=title_str, author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb,
    )

def callout(text, bg=None, border=None):
    """
    Amber (or custom) callout box. Used for transparency notices on unlinked PDFs
    and other prominent inline warnings. bg and border default to AMBER_LITE / AMBER.
    """
    if bg is None:
        bg = AMBER_LITE
    if border is None:
        border = AMBER
    style = ParagraphStyle('callout', fontName='DVS-I', fontSize=9, leading=13)
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), bg),
        ('BOX',           (0,0), (-1,-1), 1.5, border),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
        ('RIGHTPADDING',  (0,0), (-1,-1), 10),
    ])
    t = Table([[Paragraph(fix(text), style)]], colWidths=[TW])
    t.setStyle(ts)
    return t

# ── Companion components ──────────────────────────────────────────────────────
def example_box(title, rows):
    """Amber-border example box used in companion documents."""
    data = [[Paragraph(title, CS['ex_title'])]]
    for r in rows:
        data.append([Paragraph(fix(r), CS['ex_body'])])
    ts = TableStyle([
        ('BOX',           (0,0), (-1,-1), 1.5, COMP_AMBER),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, COMP_AMBER),
        ('BACKGROUND',    (0,0), (-1,-1), AMBER_LITE),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t

def remember_box(text):
    """Slate-border 'remember' callout used in companion documents."""
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), SLATE_LITE),
        ('BOX',           (0,0), (-1,-1), 0.5, COMP_SLATE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
        ('RIGHTPADDING',  (0,0), (-1,-1), 10),
    ])
    t = Table([[Paragraph(fix(text), CS['rem'])]], colWidths=[TW])
    t.setStyle(ts)
    return t

def key_result_box(title, body_text):
    """Green-header key-result box used in companion documents."""
    data = [[Paragraph(fix(title), CS['kr_hdr'])],
            [Paragraph(fix(body_text), CS['kr_body'])]]
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  COMP_GREEN),
        ('BACKGROUND',    (0,1), (-1,-1), WHITE),
        ('BOX',           (0,0), (-1,-1), 0.5, COMP_GREEN),
        ('TOPPADDING',    (0,0), (-1,-1), 6),
        ('BOTTOMPADDING', (0,0), (-1,-1), 6),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW])
    t.setStyle(ts)
    return t
