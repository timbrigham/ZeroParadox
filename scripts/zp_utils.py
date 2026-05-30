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
import os, sys, re, inspect
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
# Structural / diagram neutrals — use these instead of inline HexColor
GRID       = colors.HexColor('#CCCCCC')   # table grid and rule lines
ARROW      = GREY                         # diagram arrows (alias)
LABEL_DIM  = GREY_TEXT                    # dim label text in diagrams (alias)

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
                               spaceAfter=10, textColor=GREY_TEXT),
    'h1':       ParagraphStyle('ch1',       fontName='DV-B',  fontSize=13, leading=17,
                               spaceBefore=14, spaceAfter=5, textColor=COMP_BLUE),
    'body':     ParagraphStyle('cbody',     fontName='DVS',   fontSize=10, leading=14,
                               spaceAfter=6),
    'caption':  ParagraphStyle('ccaption',  fontName='DVS-I', fontSize=9,  leading=12,
                               spaceAfter=8, textColor=GREY_TEXT),
    'ex_title': ParagraphStyle('cex_title', fontName='DV-B',  fontSize=9,  leading=13,
                               textColor=COMP_AMBER),
    'ex_body':  ParagraphStyle('cex_body',  fontName='DVS',   fontSize=9,  leading=13),
    'rem':      ParagraphStyle('crem',      fontName='DVS-I', fontSize=9,  leading=13),
    'kr_hdr':   ParagraphStyle('ckr_hdr',   fontName='DVS-B', fontSize=9,  leading=13,
                               textColor=WHITE),
    'kr_body':  ParagraphStyle('ckr_body',  fontName='DVS',   fontSize=9,  leading=13),
    'tbl_hdr':  ParagraphStyle('ctbl_hdr',  fontName='DVS-B', fontSize=9,  leading=13,
                               textColor=WHITE),
    'tbl_cell': ParagraphStyle('ctbl_cell', fontName='DVS',   fontSize=9,  leading=13),
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
    text = text.replace('ℵ', '<font name="DVS">&#8501;</font>')
    for char, entity in [
        ('⊥','&#8869;'),  ('∨','&#8744;'),  ('∧','&#8743;'),
        ('≤','&#8804;'),  ('≥','&#8805;'),  ('≠','&#8800;'),
        ('∈','&#8712;'),  ('∉','&#8713;'),  ('⊆','&#8838;'),
        ('∪','&#8746;'),  ('∩','&#8745;'),  ('⊂','&#8834;'),  ('∀','&#8704;'),
        ('∃','&#8707;'),  ('∞','&#8734;'),  ('∑','&#8721;'),
        ('→','&#8594;'),  ('←','&#8592;'),  ('↔','&#8596;'),
        ('⇒','&#8658;'),  ('⟺','&#10234;'), ('⟹','&#10233;'),
        ('⟨','&#10216;'), ('⟩','&#10217;'), ('‖','&#8214;'),
        ('—','&#8212;'),  ('–','&#8211;'),  ('·','&#183;'),
        ('×','&#215;'),   ('−','&#8722;'),  ('≡','&#8801;'),
        ('∘','&#8728;'),  ('⊗','&#8855;'),  ('⊕','&#8853;'),
        ('∥','&#8741;'),  ('≺','&#8826;'),  ('≻','&#8827;'),
        ('′','&#8242;'),  ('″','&#8243;'),
        ('ε','&#949;'),   ('α','&#945;'),   ('β','&#946;'),
        ('γ','&#947;'),   ('δ','&#948;'),   ('η','&#951;'),
        ('ω','&#969;'),   ('τ','&#964;'),   ('φ','&#966;'),
        ('ι','&#953;'),   ('σ','&#963;'),   ('π','&#960;'),   ('λ','&#955;'),
        ('Δ','&#916;'),   ('Σ','&#931;'),   ('Γ','&#915;'),   ('Λ','&#923;'),
        ('ℚ','&#8474;'),  ('ℤ','&#8484;'),  ('ℂ','&#8450;'),
        ('ℕ','&#8469;'),  ('ℝ','&#8477;'),
    ]:
        if char in text:
            text = text.replace(char, entity)
    return text

def body(text, style='body'):
    """Paragraph in the given S style key (default: body)."""
    prose_check(text)
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
    prose_check(t)
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


# ── Prose vocabulary and version gate ─────────────────────────────────────────
# HTML entity pattern — used by validate_drawing() to catch entities in String() primitives.
# String() does not parse HTML; entities render literally. Use Unicode characters directly.
_HTML_ENT_PAT = re.compile(r'&(?:#\d+|#x[0-9a-fA-F]+|[a-zA-Z]\w*);')

# Terms banned from rendered prose. Source: vocabulary_reference.md §1.
# To suppress on a specific call site: append  # ZP-NOCHECK: <reason>
_BANNED_PROSE = (
    'null state',
    'null distribution',
    'first atomic state',
    'informational extremity',
    'informational incompressibility',
    'state-transition structure',
    'description-instantiation gap',
    'gödel ceiling',
    'categorical bridge',
    'cross-framework bridge',
    'assembly step',
    'topologically isolated',
    'metric isolation',
    'converging at the bottom element',
)
_VERSION_IN_PROSE = re.compile(r'\bv\d+\.\d+\b', re.IGNORECASE)

def _caller_nocheck():
    """Return True if the first non-zp_utils call site has # ZP-NOCHECK."""
    for frame in inspect.stack():
        fp = frame.filename
        if not fp or os.path.basename(fp) == 'zp_utils.py':
            continue
        try:
            with open(fp, encoding='utf-8') as fh:
                lines = fh.readlines()
            if 0 < frame.lineno <= len(lines):
                return '# ZP-NOCHECK' in lines[frame.lineno - 1]
        except OSError:
            pass
        return False
    return False

def prose_check(text, name=''):
    """
    Vocabulary and version gate — called automatically by body() and cbody().
    Fails the build on banned terms or version numbers in rendered prose.
    Suppress on a specific call site with:  # ZP-NOCHECK: <reason>
    """
    low = text.lower()
    violations = []
    for term in _BANNED_PROSE:
        if term in low:
            violations.append(f'  banned term: "{term}"')
    m = _VERSION_IN_PROSE.search(text)
    if m:
        violations.append(f'  version number in prose: "{m.group()}"')
    if not violations:
        return

    # Find caller location for reporting and ZP-NOCHECK detection
    caller_file, caller_line_no, caller_line = '', 0, ''
    for frame in inspect.stack():
        fp = frame.filename
        if not fp or os.path.basename(fp) == 'zp_utils.py':
            continue
        caller_file = os.path.basename(fp)
        caller_line_no = frame.lineno
        try:
            with open(fp, encoding='utf-8') as fh:
                lines = fh.readlines()
            if 0 < frame.lineno <= len(lines):
                caller_line = lines[frame.lineno - 1].rstrip()
        except OSError:
            pass
        break

    if '# ZP-NOCHECK' in caller_line:
        label = name or 'prose'
        print(f'  [ZP-NOCHECK suppressed {len(violations)} violation(s) in {label}]')
        return

    print()
    print('!' * 70)
    label = f'"{name}"' if name else 'prose'
    print(f'  ZP BUILD BLOCKED — prose violation in {label}')
    print(f'  Location: {caller_file}:{caller_line_no}')
    if caller_line:
        print(f'  Line: {caller_line[:120]}')
    for v in violations:
        print(v)
    print()
    print('  Fix the term or append  # ZP-NOCHECK: <reason>  to the call site.')
    print('  See .claude-local/vocabulary_reference.md Section 1.')
    print('!' * 70)
    print()
    raise SystemExit(1)


# ── Diagram geometry gate ──────────────────────────────────────────────────────
def validate_drawing(drawing, dh, name='diagram'):
    """
    Geometry bounds gate for companion diagram Drawing objects.
    Call at the end of every diagram function:
        return validate_drawing(d, dh, 'diagram_name')

    Enforces the CLAUDE.md layout rules:
        max content y  <  dh - 10   (top margin)
        min content y  >  5         (bottom margin)

    Raises SystemExit(1) on violation.
    """
    from reportlab.graphics.shapes import Circle, Rect, String, Line, PolyLine, Group
    ys = []
    entity_violations = []

    def _collect(shapes):
        for shape in shapes:
            try:
                if isinstance(shape, Circle):
                    ys.extend([shape.cy - shape.r, shape.cy + shape.r])
                elif isinstance(shape, Rect):
                    ys.extend([shape.y, shape.y + shape.height])
                elif isinstance(shape, String):
                    fs = getattr(shape, 'fontSize', 10) or 10
                    ys.extend([shape.y, shape.y + fs])
                    if _HTML_ENT_PAT.search(shape.text or ''):
                        entity_violations.append(shape.text)
                elif isinstance(shape, Line):
                    ys.extend([shape.y1, shape.y2])
                elif isinstance(shape, PolyLine):
                    pts = shape.points
                    for i in range(1, len(pts), 2):
                        ys.append(pts[i])
                elif isinstance(shape, Group):
                    _collect(shape.contents)
            except AttributeError:
                pass

    _collect(drawing.contents)

    if entity_violations:
        print()
        print('!' * 70)
        print(f'  ZP BUILD BLOCKED — HTML entities in String() in "{name}"')
        for v in entity_violations:
            print(f'  ↳ {v!r}')
        print()
        print('  String() primitives do not parse HTML entities — they render literally.')
        print('  Fix: replace &#NNNN; / &name; with the actual Unicode character.')
        print('!' * 70)
        print()
        raise SystemExit(1)

    if not ys:
        return drawing

    min_y, max_y = min(ys), max(ys)
    violations = []
    if max_y > dh - 10:
        violations.append(
            f'  top overflow: max_y={max_y:.1f} > dh-10={dh-10:.1f}  (dh={dh:.1f})')
    if min_y < 5:
        violations.append(
            f'  bottom overflow: min_y={min_y:.1f} < 5')

    if violations:
        print()
        print('!' * 70)
        print(f'  ZP BUILD BLOCKED — diagram geometry "{name}"')
        for v in violations:
            print(v)
        print()
        print('  Fix: increase dh or adjust element positions (cy, r, label offsets).')
        print('  See CLAUDE.md §Companion PDF Diagram Layout Standards.')
        print('!' * 70)
        print()
        raise SystemExit(1)

    return drawing


# ── Palette enforcement gate ──────────────────────────────────────────────────
# Protected palette names: redefining these in a build script without a
# # ZP-OVERRIDE: comment is a hard error that aborts the build.
_PROTECTED_PALETTE = frozenset({
    'BLUE', 'BLUE_LITE', 'GREEN', 'GREEN_LITE', 'GREEN_DARK',
    'ORANGE', 'ORANGE_LITE', 'AMBER', 'AMBER_LITE',
    'SLATE', 'SLATE_LITE', 'INDIGO', 'INDIGO_LITE',
    'RED', 'GREY', 'GREY_TEXT', 'GREY_LITE',
    'TEAL', 'TEAL_LITE', 'WHITE', 'BLACK',
    'COMP_BLUE', 'COMP_GREEN', 'COMP_SLATE', 'COMP_AMBER',
    'GRID', 'ARROW', 'LABEL_DIM',
})
_SHADOW_PAT = re.compile(
    r'^(' + '|'.join(re.escape(n) for n in _PROTECTED_PALETTE) + r')\s*=\s*colors\.'
)

def _palette_gate():
    """
    Hard gate — called at import time. Reads the importing build script's source
    and aborts (SystemExit 1) if any protected palette constant is redefined
    without a  # ZP-OVERRIDE: <reason>  comment on the same line.

    To add a legitimate exception: append  # ZP-OVERRIDE: <reason>  to the line.
    """
    caller_path = None
    for frame in inspect.stack():
        fp = frame.filename
        if not fp:
            continue
        if '<frozen' in fp or 'importlib' in fp:
            continue
        if os.path.basename(fp) == 'zp_utils.py':
            continue
        caller_path = fp
        break
    if not caller_path or not os.path.isfile(caller_path):
        return

    try:
        with open(caller_path, encoding='utf-8') as fh:
            lines = fh.readlines()
    except OSError:
        return

    violations = []
    for i, line in enumerate(lines, 1):
        if _SHADOW_PAT.match(line) and '# ZP-OVERRIDE' not in line:
            violations.append(f'  line {i}: {line.rstrip()}')

    if violations:
        name = os.path.basename(caller_path)
        print()
        print('!' * 70)
        print(f'  ZP BUILD BLOCKED — {name}')
        print('  Unapproved palette constant shadowing detected:')
        for v in violations:
            print(v)
        print()
        print('  Each flagged line must end with:  # ZP-OVERRIDE: <reason here>')
        print('  See .claude-local/PDF_Rendering_Standards.md §Palette Enforcement.')
        print('!' * 70)
        print()
        raise SystemExit(1)

    # Advisory checklist (informational only — palette has already passed)
    print()
    print('=' * 70)
    print(f'  ZP BUILD — palette OK ({os.path.basename(caller_path)})')
    print()
    print('  Auto-checked (hard failures):')
    print('  [x] Palette constants — no unapproved shadowing')
    print('  [x] Banned vocabulary in body()/cbody() prose')
    print('  [x] Version numbers in body()/cbody() prose')
    print('  [x] Diagram geometry — call validate_drawing(d, dh, name) in each diagram fn')
    print('  [x] HTML entities in String() drawing primitives — use Unicode directly')
    print()
    print('  Remaining checklist (not auto-checked):')
    print('  [ ] Font stack: DV (sans UI) / DVS (body + math) — never raw Unicode')
    print('  [ ] Body paragraphs through body()/cbody() — not bare Paragraph()')
    print('  [ ] Table cells are Paragraph objects — never plain strings')
    print('  [ ] Table grid lines use GRID constant, not inline HexColor')
    print()
    print('  Post-build: null-char verification (Standards doc §7)')
    print('=' * 70)
    print()


_palette_gate()
