"""
PDF build validation — run before every push.
Checks:
  1. All DVS* font slots in every build script use STIXTwo-Math.ttf.
  2. STIXTwo-Math.ttf covers every non-ASCII character actually used in the scripts.
  3. Every expected output PDF exists in the project root.
Exit 0 = clean. Exit 1 = problems found (push blocked).
"""
import os, re, sys
sys.stdout.reconfigure(encoding='utf-8')
sys.stderr.reconfigure(encoding='utf-8')

SCRIPT_DIR  = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
FONT_DIR    = os.path.join(SCRIPT_DIR, 'fonts')

BUILD_SCRIPTS = [
    'build_foreword.py', 'build_tools.py', 'build_gen2.py',
    'build_zpe.py', 'build_zpg.py', 'build_zph.py', 'build_zpi.py',
    'build_zpa.py', 'build_zpb.py', 'build_zpc.py', 'build_zpd.py',
    'build_zpj.py', 'build_zpk.py',
    'build_zpa_companion.py', 'build_zpb_companion.py', 'build_zpc_companion.py',
    'build_zpd_companion.py', 'build_zpe_companion.py', 'build_zpg_companion.py',
    'build_zph_companion.py', 'build_zpi_companion.py', 'build_zpj_companion.py',
    'build_zpk_companion.py', 'build_zp_philosophical_question.py',
]

EXPECTED_PDFS = [
    'Zero_Paradox_Foreword.pdf',
    'ZP_Tools_and_Methods.pdf',
    'ZP_Gen2_Applications.pdf',
    'ZP_Philosophical_Question.pdf',
    'ZP-A_Lattice_Algebra_v1_12.pdf',   'ZP-A_Illustrated_Companion.pdf',
    'ZP-B_pAdic_Topology_v1_6.pdf',     'ZP-B_Illustrated_Companion.pdf',
    'ZP-C_Information_Theory_v1_12.pdf', 'ZP-C_Illustrated_Companion.pdf',
    'ZP-D_State_Layer_v1_8.pdf',        'ZP-D_Illustrated_Companion.pdf',
    'ZP-E_Bridge_Document_v3_12.pdf',   'ZP-E_Illustrated_Companion.pdf',
    'ZP-G_Category_Theory_v1_7.pdf',    'ZP-G_Illustrated_Companion.pdf',
    'ZP-H_Categorical_Bridge_v1_11.pdf', 'ZP-H_Illustrated_Companion.pdf',
    'ZP-I_Inside_Zero_v1_8.pdf',        'ZP-I_Illustrated_Companion.pdf',
    'ZP-J_Self_Reference_v1_1.pdf',     'ZP-J_Illustrated_Companion.pdf',
    'ZP-K_Computational_Grounding_v1_3.pdf', 'ZP-K_Illustrated_Companion.pdf',
]

# Regex: font registration lines for DVS* slots
DVS_RE = re.compile(r"registerFont\(TTFont\('DVS(?:-B|-I|-BI)?',\s*FONT_DIR \+ '([^']+)'\)")

# --- Check 1: script font registrations ----------------------------------
print('Check 1: DVS font registrations ...')
reg_errors = []
for name in BUILD_SCRIPTS:
    path = os.path.join(SCRIPT_DIR, name)
    if not os.path.exists(path):
        reg_errors.append(f'  MISSING script: {name}')
        continue
    with open(path, encoding='utf-8') as f:
        content = f.read()
    for m in DVS_RE.finditer(content):
        font_file = m.group(1)
        if font_file != 'STIXTwo-Math.ttf':
            reg_errors.append(f'  {name}: DVS slot uses {font_file!r} (must be STIXTwo-Math.ttf)')

if reg_errors:
    print('  FAIL')
    for e in reg_errors: print(e)
else:
    print('  PASS')

# --- Check 2: glyph coverage of STIXTwo-Math.ttf -------------------------
print('Check 2: STIXTwo-Math.ttf glyph coverage ...')
coverage_errors = []
math_font_path = os.path.join(FONT_DIR, 'STIXTwo-Math.ttf')

if not os.path.exists(math_font_path):
    coverage_errors.append(f'  Font file not found: {math_font_path}')
else:
    # Characters known to be safe: sub_map / sup_map convert them to ASCII <sub>/<sup> tags
    # before any font renders them, and DV-routed chars are handled via explicit font tags.
    SAFE_CHARS = set(
        '₀₁₂₃₄₅₆₇₈₉ₙₖₘᵢⱼ₊₋'   # sub_map — converted to <sub>ASCII</sub>
        '⁰¹²³⁴⁵⁶⁷⁸⁹ⁿᵏ'          # sup_map — converted to <sup>ASCII</sup>
        '✗✓'                       # explicitly routed to DV (DejaVu Sans) font tag
        '➤'                        # used in String() calls with fontName='DV-I'
    )

    # Collect every non-ASCII character actually used in string literals in the scripts
    needed = set()
    str_re = re.compile(r"'([^'\\]*(?:\\.[^'\\]*)*)'" + r'|"([^"\\]*(?:\\.[^"\\]*)*)"')
    for name in BUILD_SCRIPTS:
        path = os.path.join(SCRIPT_DIR, name)
        if not os.path.exists(path):
            continue
        with open(path, encoding='utf-8') as f:
            src = f.read()
        for m in str_re.finditer(src):
            text = m.group(1) or m.group(2) or ''
            for ch in text:
                if ord(ch) > 127 and ch not in SAFE_CHARS:
                    needed.add(ch)

    # Load font cmap via ReportLab
    try:
        from reportlab.pdfbase.ttfonts import TTFont as RLTTFont
        font = RLTTFont('_scan', math_font_path)
        covered = set(font.face.charToGlyph.keys())
        missing = {ch for ch in needed if ord(ch) not in covered}
        if missing:
            display = ' '.join(f'U+{ord(c):04X}' for c in sorted(missing, key=ord))
            coverage_errors.append(
                f'  STIXTwo-Math.ttf missing glyphs for: {display}')
    except Exception as e:
        coverage_errors.append(f'  Could not load font for coverage check: {e}')

if coverage_errors:
    print('  FAIL')
    for e in coverage_errors: print(e)
else:
    print(f'  PASS ({len(needed)} non-ASCII chars all covered)')

# --- Check 3: expected PDFs exist ----------------------------------------
print('Check 3: expected PDFs present ...')
pdf_errors = []
for pdf in EXPECTED_PDFS:
    if not os.path.exists(os.path.join(PROJECT_DIR, pdf)):
        pdf_errors.append(f'  MISSING: {pdf}')

if pdf_errors:
    print('  FAIL')
    for e in pdf_errors: print(e)
else:
    print(f'  PASS ({len(EXPECTED_PDFS)} PDFs found)')

# --- Summary -------------------------------------------------------------
all_errors = reg_errors + coverage_errors + pdf_errors
if all_errors:
    print(f'\nVALIDATION FAILED — {len(all_errors)} issue(s). Push blocked.')
    sys.exit(1)
else:
    print('\nAll checks passed.')
    sys.exit(0)
