#!/usr/bin/env python3
"""Are two PDFs the same RENDERED document? The proof the no-bump token resync route asks for.

WHY (Tim, ruling R4 2026-10-03, proof tightened 2026-10-04). `document-workflow.md` lets a build
script's `register.md` token be hand-set without a version bump when the code changed but the output
did not. The first proof it accepted was an empty diff of the extracted text, and `/rely` 2026-10-03
(BLOCKING-2) built three PDFs that differ by a reversed diagram arrow, a box fill and bold type, all
of which extract to identical text. Text extraction cannot see Drawing geometry, colour, emphasis,
images or layout. So this tool answers SAME only when the pages are pixel-identical AND the text is.

  python pdf_same.py OLD.pdf NEW.pdf   # exit 0 SAME, 1 DIFFERENT, 2 CANNOT-DECIDE
  python pdf_same.py --selftest        # reportlab-built controls, each seen to fire on a mutant

EXIT CONTRACT (`R-ZERONULL`: "could not tell" never shares a value with "same").
  0  SAME           both open, the same nonzero page count, every page renders to identical
                    pixels at SCALE, and the pypdf extracted text is identical.
  1  DIFFERENT      page count differs, a page's pixels differ (page and region printed), or
                    the extracted text differs.
  2  CANNOT-DECIDE  a file is missing or unreadable, has zero pages, a page fails to render, the
                    text cannot be extracted, or the arguments are wrong. Never a licence.

SCALE is 2.0, i.e. 144 dpi (a PDF unit is 1/72 inch). Rendering is pypdfium2; the text extraction
is `check_paths._pdf_text`, imported rather than copied, so the claim sweep and this proof read the
same text. The text leg is still needed beside the pixels: invisible text (render mode 3) changes
what a search finds and leaves every pixel alone.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

common.utf8_stdout()

SAME = 0
DIFFERENT = 1
CANNOT_DECIDE = 2
VERDICTS = {SAME: "SAME", DIFFERENT: "DIFFERENT", CANNOT_DECIDE: "CANNOT-DECIDE"}
SCALE = 2.0


def _text(path):
    import check_paths
    return check_paths._pdf_text(path)


def _open(path):
    """(document, None) or (None, why)."""
    if not os.path.isfile(path):
        return None, "%s: no such file" % path
    try:
        import pypdfium2 as pdfium
        return pdfium.PdfDocument(path), None
    except Exception as e:                                   # noqa: BLE001 — any failure is undecided
        return None, "%s: cannot open (%s: %s)" % (path, type(e).__name__, e)


def _render(doc, i):
    """(PIL image, None) or (None, why) for page i, rendered at SCALE."""
    try:
        page = doc[i]
        try:
            return page.render(scale=SCALE).to_pil(), None
        finally:
            page.close()
    except Exception as e:                                   # noqa: BLE001
        return None, "page %d failed to render (%s: %s)" % (i + 1, type(e).__name__, e)


def compare(old, new):
    """(exit code, message). The whole decision; `main` only prints it."""
    a, why = _open(old)
    if a is None:
        return CANNOT_DECIDE, why
    b, why = _open(new)
    if b is None:
        a.close()
        return CANNOT_DECIDE, why
    try:
        na, nb = len(a), len(b)
        if na == 0 or nb == 0:
            return CANNOT_DECIDE, "zero pages (old %d, new %d): nothing was compared" % (na, nb)
        if na != nb:
            return DIFFERENT, "page count differs: old %d, new %d" % (na, nb)
        from PIL import ImageChops
        for i in range(na):
            ia, why = _render(a, i)
            if ia is None:
                return CANNOT_DECIDE, "old " + why
            ib, why = _render(b, i)
            if ib is None:
                return CANNOT_DECIDE, "new " + why
            if ia.size != ib.size:
                return DIFFERENT, "page %d: rendered size differs, old %s, new %s" % (
                    i + 1, ia.size, ib.size)
            if ia.mode != ib.mode or ia.tobytes() != ib.tobytes():
                box = ImageChops.difference(ia.convert("RGB"), ib.convert("RGB")).getbbox()
                return DIFFERENT, "page %d: pixels differ in region %s (px at scale %s)" % (
                    i + 1, box, SCALE)
    finally:
        a.close()
        b.close()
    ta, tb = _text(old), _text(new)
    if ta is None or tb is None:
        return CANNOT_DECIDE, "text extraction failed (old %s, new %s)" % (
            "ok" if ta is not None else "FAILED", "ok" if tb is not None else "FAILED")
    if ta != tb:
        return DIFFERENT, "pixels identical on all %d page(s), extracted text differs" % na
    return SAME, "%d page(s), pixel-identical at scale %s, extracted text identical" % (na, SCALE)


# ------------------------------------------------------------------ controls
#
# Each control builds its PDFs with reportlab in a temporary directory, MUST PASS on this module and
# MUST FAIL on a mutant with exactly one protection removed. A control nobody has seen fail is a
# hypothesis, so a mutation that does not apply fails the suite.

def _build(path, arrow="AB", fill="white", bold=False, extra_page=False, hidden=None):
    from reportlab.lib import colors
    from reportlab.pdfgen import canvas
    c = canvas.Canvas(path, pagesize=(300, 200))
    c.setFont("Helvetica-Bold" if bold else "Helvetica", 12)
    c.drawString(20, 170, "The map is injective.")
    c.setFillColor(getattr(colors, fill))
    c.rect(20, 60, 60, 40, fill=1)
    c.rect(200, 60, 60, 40, fill=1)
    c.setFillColor(colors.black)
    c.drawString(45, 75, "A")
    c.drawString(225, 75, "B")
    x0, x1 = (80, 200) if arrow == "AB" else (200, 80)
    c.line(x0, 80, x1, 80)
    d = -8 if arrow == "AB" else 8
    c.line(x1, 80, x1 + d, 86)
    c.line(x1, 80, x1 + d, 74)
    if hidden:
        t = c.beginText(20, 20)
        t.setTextRenderMode(3)
        t.textLine(hidden)
        c.drawText(t)
    if extra_page:
        c.showPage()
        c.drawString(20, 170, "A second page.")
    c.save()


def _fixtures(d):
    from pypdf import PdfWriter
    f = {}
    for name, kw in (("base", {}), ("base2", {}), ("arrow", {"arrow": "BA"}),
                     ("fill", {"fill": "red"}), ("bold", {"bold": True}),
                     ("pages", {"extra_page": True}), ("hidden", {"hidden": "hidden words"})):
        f[name] = os.path.join(d, name + ".pdf")
        _build(f[name], **kw)
    f["garbage"] = os.path.join(d, "garbage.pdf")
    with open(f["garbage"], "wb") as fh:
        fh.write(b"%PDF-1.4\nthis is not a pdf body\n")
    f["empty"] = os.path.join(d, "empty.pdf")
    w = PdfWriter()
    with open(f["empty"], "wb") as fh:
        w.write(fh)
    f["missing"] = os.path.join(d, "does_not_exist.pdf")
    return f


def _expect(m, f, a, b, want):
    code, msg = m.compare(f[a], f[b])
    return code == want, "%s vs %s -> %s: %s" % (a, b, VERDICTS.get(code, code), msg)


def _ctl_identical(m, f):
    return _expect(m, f, "base", "base2", SAME)


def _ctl_text_blind(m, f, which):
    same_text = _text(f["base"]) == _text(f[which])
    ok, why = _expect(m, f, "base", which, DIFFERENT)
    return ok and same_text, why + "; extracted text identical=%s" % same_text


def _ctl_hidden_text(m, f):
    return _expect(m, f, "base", "hidden", DIFFERENT)


def _ctl_pages(m, f):
    ok1, w1 = _expect(m, f, "base", "pages", DIFFERENT)
    ok2, w2 = _expect(m, f, "pages", "base", DIFFERENT)
    return ok1 and ok2, w1 + "; " + w2


def _ctl_unreadable(m, f):
    ok1, w1 = _expect(m, f, "base", "garbage", CANNOT_DECIDE)
    ok2, w2 = _expect(m, f, "missing", "base", CANNOT_DECIDE)
    return ok1 and ok2, w1 + "; " + w2


def _ctl_text_unreadable(m, f):
    """Pixels identical, the NEW file's text extraction fails (`_pdf_text` returned None)."""
    saved = m._text
    m._text = lambda p: None if p == f["base2"] else saved(p)
    try:
        return _expect(m, f, "base", "base2", CANNOT_DECIDE)
    finally:
        m._text = saved


class _ZeroPageDoc(object):
    """Stands in for a document pdfium opened and found empty. pdfium refuses to open the pypdf-
    written zero-page file outright (leg 1), so leg 2 injects this to reach the page-count check."""

    def __len__(self):
        return 0

    def close(self):
        pass


def _ctl_zero_pages(m, f):
    ok1, w1 = _expect(m, f, "empty", "empty", CANNOT_DECIDE)
    saved = m._open
    m._open = lambda p: (_ZeroPageDoc(), None)
    try:
        ok2, w2 = _expect(m, f, "empty", "empty", CANNOT_DECIDE)
    finally:
        m._open = saved
    return ok1 and ok2, "real file: " + w1 + "; opened-but-empty: " + w2


def _ctl_distinct(m, f):
    vals = (m.SAME, m.DIFFERENT, m.CANNOT_DECIDE)
    return len(set(vals)) == 3 and m.SAME == 0, "exit values %s" % (vals,)


_CONTROLS_MARK = "# " + "-" * 66 + " controls"

# (label, control, anchor, replacement): the replacement removes exactly what the control guards.
_CONTROLS = [
    ("identical builds are SAME", _ctl_identical,
     "    return SAME, \"%d page(s), pixel-identical",
     "    return DIFFERENT, \"%d page(s), pixel-identical"),
    ("reversed arrow is DIFFERENT (text identical)", lambda m, f: _ctl_text_blind(m, f, "arrow"),
     "            if ia.mode != ib.mode or ia.tobytes() != ib.tobytes():",
     "            if False:"),
    ("fill colour is DIFFERENT (text identical)", lambda m, f: _ctl_text_blind(m, f, "fill"),
     "            if ia.mode != ib.mode or ia.tobytes() != ib.tobytes():",
     "            if False:"),
    ("bold type is DIFFERENT (text identical)", lambda m, f: _ctl_text_blind(m, f, "bold"),
     "            if ia.mode != ib.mode or ia.tobytes() != ib.tobytes():",
     "            if False:"),
    ("pages rendered from BOTH files", lambda m, f: _ctl_text_blind(m, f, "arrow"),
     "            ib, why = _render(b, i)",
     "            ib, why = _render(a, i)"),
    ("invisible text is DIFFERENT (pixels identical)", _ctl_hidden_text,
     "    if ta != tb:",
     "    if False:"),
    ("page-count mismatch is DIFFERENT", _ctl_pages,
     "        if na != nb:\n            return DIFFERENT",
     "        if False:\n            return DIFFERENT"),
    ("unreadable NEW is CANNOT-DECIDE, never SAME", _ctl_unreadable,
     "        a.close()\n        return CANNOT_DECIDE, why",
     "        a.close()\n        return SAME, why"),
    ("missing OLD is CANNOT-DECIDE, never SAME", _ctl_unreadable,
     "    if a is None:\n        return CANNOT_DECIDE, why",
     "    if a is None:\n        return SAME, why"),
    ("text extraction failure is CANNOT-DECIDE", _ctl_text_unreadable,
     "    if ta is None or tb is None:",
     "    if False:"),
    ("zero pages is CANNOT-DECIDE, never SAME", _ctl_zero_pages,
     "        if na == 0 or nb == 0:",
     "        if False:"),
    ("R-ZERONULL three distinct exit values", _ctl_distinct,
     "CANNOT_DECIDE = 2",
     "CANNOT_DECIDE = 0"),
]


def _mutant(anchor, repl):
    """(module, None) built from this file with ONE anchor replaced above the controls, or (None, why)."""
    import types
    src_path = os.path.abspath(__file__)
    with open(src_path, encoding="utf-8") as fh:
        src = fh.read()
    head, sep, tail = src.partition(_CONTROLS_MARK)
    if head.count(anchor) != 1:
        return None, "MUTATION DID NOT APPLY — anchor found %d time(s)" % head.count(anchor)
    try:
        code = compile(head.replace(anchor, repl, 1) + sep + tail, src_path + ".mutant", "exec")
    except SyntaxError as e:
        return None, "MUTATION DID NOT APPLY — mutant does not compile: %s" % (e,)
    mod = types.ModuleType("zp_pdf_same_mutant")
    mod.__file__ = src_path
    exec(code, mod.__dict__)
    return mod, None


def selftest():
    import shutil
    import tempfile
    me = sys.modules[__name__]
    d = tempfile.mkdtemp(prefix="pdf_same_ctl_")
    try:
        f = _fixtures(d)
        print("pdf_same controls (each: MUST PASS on the live code, MUST FIRE on its mutant)")
        total = bad = 0
        for label, ctl, anchor, repl in _CONTROLS:
            total += 1
            try:
                ok_live, why_live = ctl(me, f)
            except Exception as e:                           # noqa: BLE001 — a raise is a failure
                ok_live, why_live = False, "raised %r" % (e,)
            mod, err = _mutant(anchor, repl)
            if mod is None:
                ok_mut, why_mut = True, err
            else:
                try:
                    ok_mut, why_mut = ctl(mod, f)
                except Exception as e:                       # noqa: BLE001 — a crash is not a catch
                    ok_mut, why_mut = True, "mutant raised %r, which proves nothing" % (e,)
            good = ok_live and not ok_mut
            bad += 0 if good else 1
            print("  %-4s %-48s live: %s" % ("ok" if good else "FAIL", label, why_live))
            print("       %-48s mutant fired: %s — %s" % ("", "yes" if not ok_mut else "NO", why_mut))
    finally:
        shutil.rmtree(d, ignore_errors=True)
    print("\npdf_same selftest: %s (%d/%d control(s))" % ("PASS" if not bad else "FAIL",
                                                          total - bad, total))
    return 1 if bad else 0


def main(argv):
    if argv[1:] == ["--selftest"]:
        return selftest()
    if len(argv) != 3:
        print("usage: pdf_same.py OLD.pdf NEW.pdf | --selftest   (CANNOT-DECIDE: wrong arguments)")
        return CANNOT_DECIDE
    code, msg = compare(argv[1], argv[2])
    print("pdf_same: %s — %s" % (VERDICTS[code], msg))
    print("  old: %s\n  new: %s" % (argv[1], argv[2]))
    return code


if __name__ == "__main__":
    sys.exit(main(sys.argv))
