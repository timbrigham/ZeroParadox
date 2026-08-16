# Zero Paradox — PDF Rendering Standards
## Instructions for Claude | Updated 2026-08-15

This document is the single authoritative source for all PDF rendering rules in this project. Read it before writing a single line of builder code. Every rule here applies to all PDFs — formal layers, companions, and any other document in this repository.

**Diagram coordinate geometry and overflow rules are separate.** See CLAUDE.md § "Companion PDF Diagram Layout Standards".

**Session log:**
- April 2026 (initial): Three failure modes identified — font stack, checkmark glyph, table cell wrapping.
- April 2026 (session 2): ∅ missing from DejaVuSerif added; verification updated to `page.chars`.
- April 2026 (session 3): Migrated from Linux/Bash to Windows/PowerShell.
- May 2026: Full rewrite. Body font changed from DejaVuSerif to STIXTwo-Math. Font registration and all boilerplate centralised in `zp_utils.py`. All stale Linux paths, old diagnostic scripts, and DejaVuSerif references removed.

---

## 1. Font Stack

Two font families. All registration happens in `zp_utils.py` — individual scripts never register fonts directly.

| Alias | File | Role |
|---|---|---|
| `DV` | DejaVuSans.ttf | UI elements: headers, table headers, labels, footers |
| `DV-B` | DejaVuSans-Bold.ttf | Bold sans |
| `DV-I` | DejaVuSans-Oblique.ttf | Italic sans |
| `DV-BI` | DejaVuSans-BoldOblique.ttf | Bold italic sans |
| `DVS` | STIXTwo-Math.ttf | Body text and all mathematical content |
| `DVS-B` | STIXTwo-Math.ttf | (same file — ReportLab alias) |
| `DVS-I` | STIXTwo-Math.ttf | (same file — ReportLab alias) |
| `DVS-BI` | STIXTwo-Math.ttf | (same file — ReportLab alias) |

Fonts ship with the repository at `scripts/fonts/` (tracked since 2026-08-15, with both licences beside them). Every script begins with:

```python
from zp_utils import *
```

That single import provides fonts, colours, layout constants, all styles (`S`, `CS`), and all helper functions. Nothing else is needed at the top of a build script.

**Run command (PowerShell — always include PYTHONUTF8=1):**
```powershell
$env:PYTHONUTF8=1; python scripts/build_<doc>_companion.py
```

---

## 2. Glyph Safety — Use fix() and the Paragraph Helpers

STIXTwo-Math covers most mathematical symbols well. Two glyphs are routed through a DV (DejaVuSans)
font switch:

| Glyph | Codepoint | Why it is wrapped |
|---|---|---|
| ✓ | U+2713 | absent from **DejaVuSerif**, the body font before the STIXTwo-Math swap |
| ∅ | U+2205 | absent from **DejaVuSerif**, the body font before the STIXTwo-Math swap |

⚠ **Not a STIXTwo-Math gap, and this table said it was.** Measured 2026-08-16 against the binary
now shipped in `scripts/fonts/`: resolving each codepoint through the cmap gives a real glyph with
outline data, and rendering both in `DVS` style with no wrap produces zero null characters — this
document's own pass criterion. `DejaVuSerif.ttf` maps both to `.notdef`, which is where the finding
came from. It was true of the body font **before** the May 2026 substrate change, was carried across
that change, and was then relabelled "confirmed". The wrap is harmless and is kept; the reason it
gives was wrong.

**The `fix()` helper handles both automatically.** It also converts raw Unicode math symbols (subscripts, superscripts, operators, arrows, blackboard bold) to ReportLab-safe HTML entities. `fix()` is your primary defence against rendering failures.

**Always go through the Paragraph helpers — never construct `Paragraph(raw_text, style)` directly:**

```python
# WRONG — bypasses fix(), glyph failures possible
Paragraph('Result: ✓ (v₂(0) = ∞)', CS['body'])

# CORRECT — fix() is called automatically
cbody('Result: ✓ (v₂(0) = ∞)')    # companion body
body('Result: ✓ (v₂(0) = ∞)')     # formal body
```

Available helpers from `zp_utils`:
- `cbody(text)` — companion body paragraph, calls fix()
- `body(text)` — formal body paragraph, calls fix()
- `ccaption(text)` — companion caption, calls fix()
- `li(text)` — bullet list item, calls fix()
- All box components (`label_box`, `result_box`, `example_box`, etc.) call fix() internally

**Exception — `String()` inside a `Drawing`:** ReportLab's vector drawing objects do not parse HTML entities and `fix()` has no effect on them. Use raw Unicode characters directly in `String()` calls (e.g. `'⊥'`, `'∞'`, `'→'`). Do not use `&#8869;` or `fix()` output inside a `Drawing`.

---

## 3. Tables — Always Use Paragraph Objects

**Never build table cells as plain strings.** Plain strings do not wrap, do not parse HTML entities, and overflow their column boundaries silently.

**Rule:** Every table cell must be a `Paragraph` object. Use `data_table()` for multi-column tables and the semantic box helpers (`label_box`, `result_box`, etc.) for single-column boxes — all are in `zp_utils` and all use Paragraph cells internally.

```python
# WRONG — plain strings
data = [['Component', 'Status'],
        ['T2: Non-conservation', 'Derived &#8212; from ZP-B']]

# CORRECT — use data_table() from zp_utils
rows = [['T2: Non-conservation', 'Derived — from ZP-B']]
t = data_table(['Component', 'Status'], rows, [2.5*inch, 4.0*inch])
```

---

## 4. Column Widths — Minimum Specifications

Text width is **6.5 inches (TW)**. Column widths must sum to exactly TW. Give more width to the rightmost (description/notes) column — it always carries the longest content.

| Table type | Col 1 | Col 2 | Col 3 |
|---|---|---|---|
| Two-column (component / notes) | 2.5 in | 4.0 in | — |
| Three-column (item / status / description) | 1.6 in | 1.5 in | 3.4 in |
| Three-column (claim / grounded in / status) | 1.9 in | 2.2 in | 2.4 in |
| Export tables (export / status / receiver) | 1.6 in | 1.7 in | 3.2 in |

Never make a two-column notes column narrower than 3.5 inches.

---

## 5. Subscripts and Superscripts

**Never use Unicode subscript or superscript characters** (₀₁₂, ⁰¹², ₙₖ, etc.). STIXTwo-Math does not reliably render them via ReportLab's text path.

Use ReportLab XML tags, or pass text through `fix()` which converts known Unicode sub/super characters automatically:

```python
# WRONG — unicode subscripts
'Q₂'  'v₂(x)'  '|x|₂'  'S₀'

# CORRECT — markup tags (or let fix() convert them)
'Q<sub>2</sub>'
'v<sub>2</sub>(x)'
'|x|<sub>2</sub>'
'S<sub>0</sub>'
```

`fix()` handles: ₀₁₂₃₄₅₆₇₈₉ₙₖₘᵢⱼ₊₋ and ⁰¹²³⁴⁵⁶⁷⁸⁹ⁿᵏ. Any subscript/superscript not in that set must be written with explicit tags.

---

## 6. HTML Entities — Safe List

Use these decimal entities in Paragraph text. `fix()` converts the raw Unicode symbols in the left column to these entities automatically — prefer raw Unicode in source strings and let fix() handle conversion.

### Math operators
| Symbol | Entity | Symbol | Entity |
|---|---|---|---|
| ⊥ | `&#8869;` | ∨ | `&#8744;` |
| ∧ | `&#8743;` | ≤ | `&#8804;` |
| ≥ | `&#8805;` | ≠ | `&#8800;` |
| ≡ | `&#8801;` | ∈ | `&#8712;` |
| ∉ | `&#8713;` | ⊆ | `&#8838;` |
| ⊂ | `&#8834;` | ∪ | `&#8746;` |
| ∩ | `&#8745;` | ∀ | `&#8704;` |
| ∃ | `&#8707;` | ∞ | `&#8734;` |
| ∑ | `&#8721;` | ∏ | `&#8719;` |
| ∘ | `&#8728;` | ⊗ | `&#8855;` |
| ⊕ | `&#8853;` | − | `&#8722;` |
| × | `&#215;` | · | `&#183;` |

### Arrows
| Symbol | Entity | Symbol | Entity |
|---|---|---|---|
| → | `&#8594;` | ← | `&#8592;` |
| ↔ | `&#8596;` | ⇒ | `&#8658;` |
| ⟹ | `&#10233;` | ⟺ | `&#10234;` |

### Blackboard bold
| Symbol | Entity | Symbol | Entity |
|---|---|---|---|
| ℚ | `&#8474;` | ℤ | `&#8484;` |
| ℂ | `&#8450;` | ℕ | `&#8469;` |
| ℝ | `&#8477;` | | |

### Greek (common in this project)
| Symbol | Entity | Symbol | Entity |
|---|---|---|---|
| ε | `&#949;` | α | `&#945;` |
| β | `&#946;` | γ | `&#947;` |
| δ | `&#948;` | η | `&#951;` |
| ω | `&#969;` | λ | `&#955;` |
| π | `&#960;` | φ | `&#966;` |
| Δ | `&#916;` | Σ | `&#931;` |

### Delimiters and punctuation
| Symbol | Entity | Notes |
|---|---|---|
| ⟨ | `&#10216;` | left angle bracket |
| ⟩ | `&#10217;` | right angle bracket |
| ‖ | `&#8214;` | double vertical (norm) |
| — | `&#8212;` | em dash |
| – | `&#8211;` | en dash |
| ✓ | `<font name="DV">&#10003;</font>` | **always wrap in DV — use fix() or chk()** |
| ∅ | `<font name="DV">&#8709;</font>` | **always wrap in DV — use fix()** |

---

## 7. Pre-Build Verification

Always verify the output PDF with `page.chars` — not `extract_text()` and not raw binary search. Both produce false negatives for math symbols near subscript/superscript text.

- `extract_text()` drops glyphs that sit at a different baseline (sub/super context).
- Raw binary search fails because ReportLab embeds glyphs by internal font ID, not Unicode codepoint.
- `page.chars` returns every character individually, bypassing both problems.

**Null character check is the primary signal:** A U+0000 in the character stream means ReportLab tried to render a glyph the font doesn't have and substituted a blank box. Any non-zero null count is a failure.

```python
import pdfplumber, os

def verify_pdf(path):
    issues = []
    with pdfplumber.open(path) as pdf:
        pages = len(pdf.pages)
        all_chars = []
        for page in pdf.pages:
            all_chars.extend(c['text'] for c in page.chars if c['text'])

    null_count = sum(1 for c in all_chars if ord(c) == 0)
    if null_count > 0:
        issues.append(f'NULL CHARS x{null_count} — missing glyph, check DV font wrap')

    size = os.path.getsize(path) // 1024
    status = 'PASS' if not issues else 'FAIL'
    print(f'{os.path.basename(path)}: {pages}pp {size}KB [{status}]')
    for issue in issues:
        print(f'  !! {issue}')
    return len(issues) == 0
```

---

## 8. Standard Builder Pattern

Every build script follows this structure:

```python
"""
Build ZP-X [Title]
Version N.N | Month Year
"""
import os
from zp_utils import *
# Add only if the script uses custom diagrams:
# from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Ellipse
# from reportlab.graphics import renderPDF

VERSION = 'N.N'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-X_filename.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox ZP-X  |  Title  |  Month Year')
        # NOTE: CLAUDE.md rule — companion footers must NOT include version.
        # Version lives in exactly one place: the tagline meta line in the header banner.
        # Formal doc footers (via make_doc()) may include version — companions may not.
        canvas.restoreState()

    doc = SimpleDocTemplate(
        out_path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-X Title', author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb)

    E = []
    # ... document content using zp_utils helpers ...

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
```

`companion_template.py` is the full starting-point template for new companion scripts, and it is **private** — kept in `.claude-local/` and not published. A maintainer with that folder should start from it; a public reader cannot, and should copy the nearest existing `scripts/build_*_companion.py` instead.

---

## 9. Palette Enforcement — Hard Gate

`zp_utils.py` enforces the colour palette at import time. **This is not advisory — it aborts the build with exit code 1.**

### What is checked

Every build script is scanned for module-level redefinition of any protected palette constant:

```
BLUE  BLUE_LITE  GREEN  GREEN_LITE  GREEN_DARK  ORANGE  ORANGE_LITE
AMBER  AMBER_LITE  SLATE  SLATE_LITE  INDIGO  INDIGO_LITE  RED
GREY  GREY_TEXT  GREY_LITE  TEAL  TEAL_LITE  WHITE  BLACK
COMP_BLUE  COMP_GREEN  COMP_SLATE  COMP_AMBER
GRID  ARROW  LABEL_DIM
```

If any line matches `PROTECTED_NAME = colors.XXX` without an approved override comment, the build is blocked:

```
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  ZP BUILD BLOCKED — build_xyz.py
  Unapproved palette constant shadowing detected:
  line 27: GREEN = colors.HexColor('#123456')
  ...
```

### Approved overrides

To add a legitimate palette exception, append a `# ZP-OVERRIDE: <reason>` comment to the line:

```python
AMBER = colors.HexColor('#B07800')  # ZP-OVERRIDE: ZP-G import_box label uses darker amber
```

Currently approved overrides (3 scripts):
- `build_zpg.py` — `AMBER` override for darker import_box label colour
- `build_tools.py` — `GREEN` (GREEN_DARK value) and `GREY` (darker for captions)
- `build_zp_philosophical_question.py` — `AMBER` brighter accent for essay style

### Standard neutral colours (use these — not raw HexColor)

| Constant | Hex | Use |
|----------|-----|-----|
| `GRID` | `#CCCCCC` | Table grid and rule lines |
| `GREY` / `ARROW` | `#888888` | Diagram arrows, neutral strokes |
| `GREY_TEXT` / `LABEL_DIM` | `#555555` | Dim label text in diagrams |

### What is NOT checked (diagram exemption)

Inline `colors.HexColor()` calls **inside Drawing/diagram functions** are not flagged. Diagrams necessarily use custom colours for nodes, arrows, and fills. The gate only catches module-level constant definitions.

---

*Zero Paradox — PDF Rendering Standards | May 2026 | Internal Technical Reference*
