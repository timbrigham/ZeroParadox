# Zero Paradox — PDF Rendering Standards
## Instructions for Claude | April 2026

This document captures the specific technical requirements for generating PDFs in this project. It exists because we discovered rendering failure modes in production. Every future PDF generation session must follow these standards before writing a single line of builder code.

**Session log:**
- April 2026 (initial): Three failure modes identified — font stack, checkmark glyph, table cell wrapping.
- April 2026 (session 2): Two additional findings added — ∅ missing from DejaVuSerif (Section 2b), and verification must use `page.chars` not raw binary or `extract_text()` (Section 6, updated).

---

## 1. Font Stack — Non-Negotiable

Use DejaVu fonts exclusively. They are installed at `/usr/share/fonts/truetype/dejavu/` in the Claude environment and have the broadest unicode math coverage of any available font family.

Register all four weights at the top of every builder script:

```python
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

FONT_DIR = '/usr/share/fonts/truetype/dejavu/'
pdfmetrics.registerFont(TTFont('DV',     FONT_DIR + 'DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DV-B',   FONT_DIR + 'DejaVuSans-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DV-I',   FONT_DIR + 'DejaVuSans-Oblique.ttf'))
pdfmetrics.registerFont(TTFont('DV-BI',  FONT_DIR + 'DejaVuSans-BoldOblique.ttf'))
pdfmetrics.registerFont(TTFont('DVS',    FONT_DIR + 'DejaVuSerif.ttf'))
pdfmetrics.registerFont(TTFont('DVS-B',  FONT_DIR + 'DejaVuSerif-Bold.ttf'))
pdfmetrics.registerFont(TTFont('DVS-I',  FONT_DIR + 'DejaVuSerif-Italic.ttf'))
pdfmetrics.registerFont(TTFont('DVS-BI', FONT_DIR + 'DejaVuSerif-BoldItalic.ttf'))
```

**Body text** uses `DVS` (DejaVu Serif). **UI elements, headers, labels** use `DV` (DejaVu Sans).

---

## 2. The Checkmark Problem — Critical

**U+2713 (✓) is missing from DejaVuSerif.** It exists in DejaVuSans. This means any `&#10003;` in a `Paragraph` styled with `DVS` renders as a blank black box.

**Rule:** Never use `&#10003;` bare in a Paragraph that uses a Serif style. Always wrap it:

```python
# WRONG — blank box if the paragraph style uses DVS
'Status: DERIVED. &#10003;'

# CORRECT — inline font switch to the Sans font which has the glyph
'Status: DERIVED. <font name="DV">&#10003;</font>'
```

This applies everywhere: label boxes, theorem boxes, table cells, body text. If the surrounding `ParagraphStyle` is `DVS`-based and the text contains `&#10003;`, the font tag is required.

---

## 2b. The Empty Set Problem — Identical Fix Required

**U+2205 (∅) is also missing from DejaVuSerif.** Discovered in session 2 when `hom(X, 0) = ∅` rendered as a null/blank box in ZP-E.

The fix is identical to the checkmark rule:

```python
# WRONG — blank box if the paragraph style uses DVS
'hom(X, 0) = &#8709; for X ≠ 0'

# CORRECT
'hom(X, 0) = <font name="DV">&#8709;</font> for X &#8800; 0'
```

**The canonical `fix()` helper handles this automatically** — it replaces both `✓` (U+2713) and `∅` (U+2205) with their DV-wrapped equivalents. Do not bypass `fix()`.

The updated diagnostic suspects list (run before every build session):

```python
from fontTools.ttLib import TTFont
dv  = TTFont('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')
dvs = TTFont('/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf')
cmap_sans  = dv.getBestCmap()
cmap_serif = dvs.getBestCmap()

suspects = {
    'checkmark ✓': 0x2713,
    'heavy check ✔': 0x2714,
    'empty set ∅': 0x2205,   # Added session 2 — also missing from DejaVuSerif
    'aleph ℵ': 0x2135,       # Added session 3 — missing from both DejaVu fonts; requires STIX fallback
}
for name, cp in suspects.items():
    print(f'{name}: Sans={cp in cmap_sans}  Serif={cp in cmap_serif}')
```

If Serif shows `False` for any symbol you intend to use, wrap that symbol in `<font name="DV">...</font>`.

---

## 3. Tables — Always Use Paragraph Objects

**Never build table cells as plain strings.** ReportLab's `TableStyle` font commands (`FONTNAME`, `FONTSIZE`, `LEADING`) style the cell but do not parse HTML entities and do not word-wrap long content. Plain string cells overflow their column boundaries silently.

**Rule:** Every table cell must be a `Paragraph` object.

```python
# WRONG — plain strings do not wrap and do not parse entities
data = [['Component', 'Status / Notes'],
        ['T2: Non-conservation', 'Valid &#8212; Derived from ZP-B ball hierarchy']]

# CORRECT — Paragraph objects wrap and parse entities
from reportlab.platypus import Paragraph
from reportlab.lib.styles import ParagraphStyle

cell_style = ParagraphStyle('cell', fontName='DVS', fontSize=9, leading=13)
hdr_style  = ParagraphStyle('hdr',  fontName='DV-B', fontSize=9, leading=13,
                              textColor=colors.white)

data = [
    [Paragraph('Component', hdr_style), Paragraph('Status / Notes', hdr_style)],
    [Paragraph('T2: Non-conservation', cell_style),
     Paragraph('Valid &#8212; Derived from ZP-B ball hierarchy', cell_style)],
]
```

The canonical `data_table()` helper already implements this correctly. Do not bypass it.

---

## 4. Column Widths — Minimum Specifications

The text width for US Letter with 1-inch margins is **6.5 inches (TW)**. Column widths must sum to exactly TW.

These are the minimum widths tested to contain content without overflow:

| Table type | Column 1 | Column 2 | Column 3 |
|---|---|---|---|
| Two-column (component / notes) | 2.5 in | 4.0 in | — |
| Three-column (item / status / description) | 1.6 in | 1.5 in | 3.4 in |
| Three-column (claim / grounded in / status) | 1.9 in | 2.2 in | 2.4 in |
| Export tables (export / status / receiver) | 1.6 in | 1.7 in | 3.2 in |

**Rule:** When in doubt, give more width to the rightmost column (the description or notes column). It always contains the longest content. Never make the notes column narrower than 3.5 inches in a two-column layout.

---

## 5. HTML Entities — Safe List

All of the following have been confirmed to render correctly in DejaVuSans and DejaVuSerif. Use these decimal entities in all Paragraph text.

### Greek and math operators
| Symbol | Entity | Notes |
|---|---|---|
| ∨ | `&#8744;` | join |
| ⊥ | `&#8869;` | bottom |
| ≤ | `&#8804;` | less-than-or-equal |
| ≥ | `&#8805;` | greater-than-or-equal |
| ∈ | `&#8712;` | element-of |
| ∉ | `&#8713;` | not element-of |
| ⊆ | `&#8838;` | subset-or-equal |
| ∪ | `&#8746;` | union |
| ∩ | `&#8745;` | intersection |
| ∀ | `&#8704;` | for-all |
| ∃ | `&#8707;` | there-exists |
| ≠ | `&#8800;` | not-equal |
| ≡ | `&#8801;` | equivalent |
| ∞ | `&#8734;` | infinity |
| ∑ | `&#8721;` | sum |
| ∏ | `&#8719;` | product |
| ∘ | `&#8728;` | composition |
| − | `&#8722;` | minus (typographic) |
| × | `&#215;` | times |
| · | `&#183;` | middle dot |

### Arrows
| Symbol | Entity | Notes |
|---|---|---|
| → | `&#8594;` | right arrow |
| ← | `&#8592;` | left arrow |
| ↔ | `&#8596;` | bidirectional |
| ⇒ | `&#8658;` | double right |
| ⟺ | `&#10234;` | long double arrow |
| ⟹ | `&#10233;` | long double right |

### Set / number symbols
| Symbol | Entity | Notes |
|---|---|---|
| ℚ | `&#8474;` | rationals |
| ℤ | `&#8484;` | integers |
| ℂ | `&#8450;` | complex numbers |
| ℕ | `&#8469;` | natural numbers |
| ℝ | `&#8477;` | reals |

### Greek letters (used in this project)
| Symbol | Entity |
|---|---|
| ε | `&#949;` |
| α | `&#945;` |
| β | `&#946;` |
| γ | `&#947;` |
| η | `&#951;` |
| Σ | `&#931;` |
| Δ | `&#916;` |

### Delimiters and punctuation
| Symbol | Entity | Notes |
|---|---|---|
| ⟨ | `&#10216;` | left angle bracket |
| ⟩ | `&#10217;` | right angle bracket |
| ‖ | `&#8214;` | double vertical (norm) |
| — | `&#8212;` | em dash |
| – | `&#8211;` | en dash |
| ✓ | `<font name="DV">&#10003;</font>` | **always wrap in DV font** |

### Subscripts and superscripts
**Never use unicode subscript/superscript characters** (₀₁₂₃, ⁰¹²³ etc.). They are missing from both DejaVu fonts and render as blank boxes.

Use ReportLab's XML markup tags instead:

```python
# WRONG — unicode subscripts are missing glyphs
'Q₂'   'S_n'   '2^k'

# CORRECT — use sub/super tags
'Q<sub>2</sub>'
'S<sub>n</sub>'
'2<super>k</super>'
'x<sub>i+1</sub>'
'v<sub>2</sub>(x)'
'|x|<sub>2</sub>'
```

---

## 6. Pre-Build Verification Checklist

Run this script before delivering any PDF. **Updated in session 2** — the original version used `extract_text()` and raw binary searches, both of which produce false negatives for math symbols adjacent to sub/superscript text. The correct method is `page.chars` (character-level extraction).

**Why `extract_text()` fails:** pdfplumber's text extraction algorithm groups characters by proximity and baseline. Glyphs that sit between subscript/superscript text (at a different baseline) are silently dropped from the word-level output. `page.chars` bypasses this grouping and returns every character individually.

**Why raw binary search fails:** ReportLab uses font-internal glyph IDs for some characters when embedding, not direct Unicode codepoints. Neither UTF-16-BE nor UTF-16-LE searches reliably find all glyphs in the raw PDF bytes.

**The correct verification approach:**

```python
import pdfplumber, os

# Per-document symbol map: only check symbols actually used in each document.
# Do not check for symbols a document correctly does not contain.
# ZP-B (topology) has no ∨ or ≤. ZP-C (info theory) has no ≤.
DOC_SYMBOLS = {
    'ZP-A': [0x22A5, 0x2228, 0x2264],        # ⊥ ∨ ≤
    'ZP-B': [0x22A5, 0x2208, 0x211A, 0x2192], # ⊥ ∈ ℚ →
    'ZP-C': [0x22A5, 0x2228, 0x2192, 0x2208], # ⊥ ∨ → ∈
    'ZP-D': [0x22A5, 0x2208, 0x2102, 0x2264], # ⊥ ∈ ℂ ≤
    'ZP-E': [0x22A5, 0x2192, 0x2208, 0x2228], # ⊥ → ∈ ∨
}

def verify_pdf(path):
    fname = os.path.basename(path)
    issues = []

    with pdfplumber.open(path) as pdf:
        pages = len(pdf.pages)
        # CORRECT: use page.chars for character-level extraction
        all_chars = []
        for page in pdf.pages:
            all_chars.extend(c['text'] for c in page.chars if c['text'])

    char_set = set(all_chars)
    size = os.path.getsize(path) // 1024

    # Check 1: null chars = genuine missing glyph (font does not have it)
    # A null char (U+0000) in the char stream means ReportLab tried to render a glyph
    # the font doesn't have and substituted a blank box.
    null_count = sum(1 for c in all_chars if ord(c) == 0)
    if null_count > 0:
        issues.append(f'NULL CHARS x{null_count} — missing glyph, check DV font wrap')

    # Check 2: per-doc symbols via char-level set membership
    doc_key = next((k for k in DOC_SYMBOLS if k in fname), None)
    if doc_key:
        for cp in DOC_SYMBOLS[doc_key]:
            if chr(cp) not in char_set:
                issues.append(f'MISSING {chr(cp)} U+{cp:04X}')

    status = 'PASS' if not issues else 'FAIL'
    print(f'{fname}: {pages}pp {size}KB [{status}]')
    for issue in issues:
        print(f'  !! {issue}')
    return len(issues) == 0
```

---

## 7. The Standard Builder Pattern

Every PDF builder script for this project must follow this structure:

```python
# 1. Font registration (Section 1 above)
# 2. Color constants
# 3. Page geometry — always US Letter, 1-inch margins, TW = 6.5 inch
# 4. ParagraphStyle definitions
# 5. Helper functions — label_box(), data_table() using Paragraph cells
# 6. make_doc() — SimpleDocTemplate with footer callback
# 7. Per-document build functions
# 8. Main: build all, copy to /mnt/user-data/outputs/ AND /mnt/project/

# CRITICAL: data_table() must use Paragraph objects (Section 3)
# CRITICAL: checkmarks must use font switch (Section 2)
# CRITICAL: no unicode subscripts (Section 5)
```

The working builder script is saved at `/home/claude/build_zp_pdfs.py` and implements all of the above correctly. Use it as the canonical reference for any future rebuild or extension.

---

## 8. When Starting a New PDF Session

Tell Claude:

> "Before building any PDFs, read the Zero Paradox PDF Rendering Standards document in the project files. Follow all rules in that document. In particular: use DejaVu fonts, wrap all checkmarks in `<font name="DV">`, wrap all empty set symbols (∅) in `<font name="DV">`, build all table cells as Paragraph objects, never use unicode subscript or superscript characters, and verify with `page.chars` not `extract_text()`."

That single instruction, combined with this document, prevents all known failure modes.

**Known glyphs missing from DejaVuSerif (require DV font wrap):**
- U+2713 ✓ checkmark
- U+2205 ∅ empty set
- U+2717 ✗ ballot cross
- U+2118 ℘ power set (Weierstrass P)

**Known glyphs missing from ALL DejaVu fonts (require STIX fallback):**
- U+2135 ℵ aleph — register STIX font and wrap: `<font name="STIX">&#8501;</font>`. See build_zpe.py for STIX registration pattern with path fallback logic.

Run the diagnostic (Section 2/2b) at the start of any new session to check if additional glyphs have been discovered missing.

---

## 2e. Graphics String Objects — Different Rules Apply

`Drawing.String()` objects in `reportlab.graphics.shapes` do NOT use Paragraph styles. They use a `fontName=` parameter that directly selects the font. This means:

- `fix()` does not apply — there is no HTML entity processing
- The problem-character rules from sections 2/2b/2c only apply to **Paragraph contexts**
- For `Drawing.String()`, the fix is simply to use `fontName='DV-B'` or `fontName='DV'` for any string containing characters that are absent from DejaVuSerif

```python
# CORRECT — explicit Sans font covers all characters present in Sans
d.add(String(x, y, '⊥', fontSize=14, fontName='DV-B', fillColor=colors.white))
d.add(String(x, y, '✗ No return path', fontSize=9, fontName='DV-B', fillColor=RED))
```

All raw Unicode characters used in `Drawing.String()` in this project use `fontName='DV-B'`, which contains ⊥ (U+22A5), ✗ (U+2717), and all other symbols needed for diagrams. This is correct and safe.

---

## 2c. The HTML Entity Bypass Problem — Critical

**`fix()` only processes raw Unicode characters, not pre-written HTML entities.**

If you write `&#8709;` directly in a source string, `fix()` will not touch it. The entity passes straight to ReportLab, which resolves it to U+2205 and attempts to render it in the current paragraph font (DVS). Since U+2205 is missing from DejaVuSerif, you get a blank box — the same failure as the raw character, but silently bypassing the fix.

**Rule:** For any character that needs DV wrapping, write the raw Unicode character in your source so `fix()` can process it. Do NOT write pre-escaped HTML entities for problem characters.

```python
# WRONG — &#8709; bypasses fix(), renders as blank box in DVS context
'The bottom is &#8709;'

# CORRECT — raw Unicode character; fix() wraps it automatically
'The bottom is ∅'
```

This applies to all known problem glyphs: ∅ (U+2205), ✓ (U+2713), ✗ (U+2717), ℘ (U+2118).

---

## 2d. Mathematical Unicode Blocks — Not Supported

**Characters from the Mathematical Alphanumerics block (U+1D400–U+1D7FF) are not in any DejaVu font.** This includes mathematical script letters (𝒫, 𝒜, ℬ…), mathematical bold letters, and mathematical fraktur letters.

Examples of what does NOT work:
- `&#119823;` (U+1D4AB, 𝒫 mathematical script capital P) — blank/missing in both fonts
- Any character in the U+1D400–U+1D7FF range

**Rule:** Use standard Latin equivalents. For power set notation, write `P(X)`. For other mathematical scripts, use the plain Latin letter or spell it out.

```python
# WRONG — mathematical script P is not in DejaVu
'L = &#119823;(X)'

# CORRECT — plain Latin P
'L = P(X)'
```

---

## 9. Problems
The environment often has issues hanging on pipe actions. Instead of using find and piping toexecute, try direct `ls` list command without xargs or pipes to verify the files: ls -R | grep .py or find . -maxdepth 2 -name '*.py'."

Additionally, when genrating scripts include verbouse output by default. We see freezes in thr output creation scripts. 

---

## 10. Color Palette Standard

All formal ZP documents (ZP-A through ZP-H) use a shared color palette. Define these constants at the top of every builder script using the exact hex values below. Do not introduce new colors without updating this document.

### Formal Document Palette

| Constant | Hex | Role |
|---|---|---|
| `BLUE` | `#2E75B6` | Box headers for Definitions; data table header backgrounds |
| `BLUE_LITE` | `#D5E8F0` | Box body backgrounds for Definitions |
| `GREEN` | `#2E7D32` | Box headers for Results (Theorems, Propositions, Lemmas, Corollaries) |
| `GREEN_LITE` | `#E8F5E9` | Box body backgrounds for Results |
| `GREEN_DARK` | `#1B5E20` | Inline derived-status text on white backgrounds (e.g. "DERIVED ✓" lines outside boxes) |
| `ORANGE` | `#BF4E30` | Box headers for Axioms, Design Principles, Conditional Claims |
| `ORANGE_LITE` | `#FBE9E7` | Box body backgrounds for Axioms |
| `SLATE` | `#455A64` | Box headers for Remarks; bridge document claim boxes (ZP-E bridge_box) |
| `SLATE_LITE` | `#ECEFF1` | Box body backgrounds for Remarks |
| `AMBER` | `#B07800` | Box headers for Import boxes (results imported from other layers) |
| `AMBER_LITE` | `#FFF8E7` | Box body backgrounds for Imports |
| `GREY_LITE` | `#F5F5F5` | Alternating row background in data tables |

`GREEN` vs `GREEN_DARK`: use `GREEN` (`#2E7D32`) for box header backgrounds; use `GREEN_DARK` (`#1B5E20`) only for inline text rendered on white backgrounds. Never swap them.

### Semantic Box Type → Color Mapping

| Box helper | Header color | Body color | Used for |
|---|---|---|---|
| `def_box()` | `BLUE` | `GREY_LITE` | Definitions |
| `result_box()` | `GREEN` | `GREY_LITE` | Theorems, Propositions, Lemmas, Corollaries |
| `axiom_box()` | `ORANGE` | `GREY_LITE` | Axioms, Design Principles, Conditional Claims |
| `remark_box()` | `SLATE` | `GREY_LITE` | Remarks |
| `import_box()` | `AMBER` | `GREY_LITE` | Imported results from other layers |
| `bridge_box()` | `SLATE` | `GREY_LITE` | ZP-E bridge claim boxes (DA-1, DA-2, DA-3) |

All box body backgrounds use `GREY_LITE`. Header text uses the `label` ParagraphStyle (DV-B, 9pt, WHITE) except `import_box()` whose header text uses `labelAmber` (DV-B, 9pt, AMBER text on AMBER_LITE background).

### Typography Standard

| Style key | Font | Size | Leading | Alignment | Notes |
|---|---|---|---|---|---|
| `title` | DV-B | 18pt | 24 | centered | Document title |
| `subtitle` | DV-I | 11pt | 15 | centered | Version / date line |
| `h1` | DV-B | 13pt | 18 | left | BLUE; section headings |
| `h2` | DV-B | 11pt | 15 | left | BLUE; subsection headings |
| `body` | DVS | 10pt | 14 | left | Main prose |
| `bodyI` | DVS-I | 10pt | 14 | left | Italic prose (companion notes, version notes) |
| `label` | DV-B | 9pt | 13 | left | WHITE text — box headers |
| `cell` | DVS | 9pt | 13 | left | Table cells |
| `cellB` | DVS-B | 9pt | 13 | left | Bold table cells |
| `cellI` | DVS-I | 9pt | 13 | left | Italic table cells |
| `derived` | DVS-B | 10pt | 14 | left | GREEN_DARK — inline derived-status lines |

ZP-E uses `alignment=4` (justified) for `body`, `bodyI`, `li`, and `derived` — intentional for that document's prose-heavy bridge character. Other formal docs use default left alignment.

### Companion Document Accent Color

| Constant | Hex | Role |
|---|---|---|
| `TEAL` | `#2A8080` | Accent for ALL companion documents — h1 headings, example box borders |

Use `#2A8080` in every companion builder (ZP-A through ZP-H). Do not introduce per-layer accent colors.

### Footer Format

**Formal documents:**
```
Zero Paradox {doc_id}: {title}  |  Version {version}  |  April 2026  |  Page {n}
```
Example: `Zero Paradox ZP-A: Lattice Algebra  |  Version 1.5  |  April 2026  |  Page 1`

**Companion documents:**
```
Zero Paradox {doc_id} Illustrated Companion  |  Version {version}  |  April 2026  |  Page {n}
```

---

*Zero Paradox — PDF Rendering Standards | April 2026 | Internal Technical Reference*
