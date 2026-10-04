#!/usr/bin/env python3
"""Are two PDFs the same RENDERED document? The proof the no-bump token resync route asks for.

WHY (Tim, ruling R4 2026-10-03, proof tightened 2026-10-04). `document-workflow.md` lets a build
script's `register.md` token be hand-set without a version bump when the code changed but the output
did not. The first proof it accepted was an empty diff of the extracted text, and `/rely` 2026-10-03
(BLOCKING-2) built three PDFs that differ by a reversed diagram arrow, a box fill and bold type, all
of which extract to identical text. Text extraction cannot see Drawing geometry, colour, emphasis,
images or layout. So this tool answers SAME only when the pages are pixel-identical AND the text is.
`/rely` 2026-10-04 (BLOCKING-1) then showed both of those blind to the document around the pages:
an edit that changed only a build script's `title=` read SAME, as did a changed bookmark, an added
link border and a changed link URL. "Unchanged" means unchanged to a reader (Tim, 2026-10-04), and a
viewer shows the title bar, the bookmark sidebar and where a link goes, so a third leg compares the
document-level content too.

  python pdf_same.py OLD.pdf NEW.pdf   # exit 0 SAME, 1 DIFFERENT, 2 CANNOT-DECIDE
  python pdf_same.py --selftest        # reportlab-built controls, each seen to fire on a mutant

EXIT CONTRACT (`R-ZERONULL`: "could not tell" never shares a value with "same").
  0  SAME           both open, the same nonzero page count, every page renders to identical
                    pixels at SCALE, the pypdf extracted text is identical, AND the document-level
                    content is identical (below).
  1  DIFFERENT      page count differs, a page's pixels differ (page and region printed), the
                    extracted text differs, or the document-level content differs (the first
                    differing path printed).
  2  CANNOT-DECIDE  a file is missing or unreadable, has zero pages, a page fails to render, the
                    text cannot be extracted, the document-level content cannot be read, an import
                    fails, any other exception is raised, or the arguments are wrong. Never a
                    licence, and never shared with DIFFERENT.

DOCUMENT-LEVEL CONTENT is read with pypdf and resolved to plain values, so object numbering, which
a rebuild may change, is invisible and only content is compared:
  info   the trailer's document information dictionary, EVERY key (/Title, /Author, /Subject,
         /Keywords, /Creator, /Producer, /CreationDate, /ModDate, ...).
  root   the document catalog except /Pages: XMP metadata (/Metadata, compared by its decoded
         bytes), the outline (/Outlines: every bookmark title and destination), named
         destinations, /OpenAction, /PageMode, /ViewerPreferences, /AcroForm, /PageLabels, ...
  pages  every page dictionary except /Contents, /Resources and /Parent (which the pixel and text
         legs already answer for), so every annotation with every key: link /URI and /Dest,
         /Border, /C, appearance streams /AP (by decoded bytes), popups, /Rotate and so on.
  A reference to a page object is replaced by "<page N>", and a reference back into an object
  already being read by "<cycle>".
EXCLUDED: nothing. Measured 2026-10-04: two builds of an unchanged `scripts/build_zpa_companion.py`
in the same month were byte-identical (ReportLab invariant mode, set in `zp_utils`), so no field,
/CreationDate and /ModDate included, varies on its own. The trailer /ID is a file identifier, not
document content, and is not read.

SCALE is 2.0, i.e. 144 dpi (a PDF unit is 1/72 inch). Rendering is pypdfium2; the text extraction
is `check_paths._pdf_text`, imported rather than copied, so the claim sweep and this proof read the
same text. The text leg is still needed beside the pixels: invisible text (render mode 3) changes
what a search finds and leaves every pixel alone.

KNOWN LIMIT: every build stamps its month into the subtitle meta line, so a rebuild in a later month
than the committed PDF is DIFFERENT on that line. That fails closed (no licence), and it means the
no-bump route can be shown only within the calendar month of the last build.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

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


def _plain(obj, pages, stack):
    """A pypdf object resolved to plain, comparable values (see DOCUMENT-LEVEL CONTENT above)."""
    from pypdf.generic import (ArrayObject, BooleanObject, ByteStringObject, DictionaryObject,
                               FloatObject, IndirectObject, NameObject, NullObject, NumberObject,
                               StreamObject, TextStringObject)
    if isinstance(obj, IndirectObject):
        key = (obj.idnum, obj.generation)
        if key in pages:
            return "<page %d>" % pages[key]
        if key in stack:
            return "<cycle>"
        return _plain(obj.get_object(), pages, stack | {key})
    if isinstance(obj, StreamObject):
        import hashlib
        d = {str(k): _plain(v, pages, stack) for k, v in obj.items()
             if k not in ("/Length", "/Filter", "/DecodeParms")}
        d["<decoded sha256>"] = hashlib.sha256(obj.get_data()).hexdigest()
        return d
    if isinstance(obj, DictionaryObject):
        return {str(k): _plain(v, pages, stack) for k, v in obj.items()}
    if isinstance(obj, ArrayObject):
        return [_plain(v, pages, stack) for v in obj]
    if isinstance(obj, TextStringObject):
        return ("str", str(obj))
    if isinstance(obj, ByteStringObject):
        return ("bytes", bytes(obj).hex())
    if isinstance(obj, NameObject):
        return ("name", str(obj))
    if isinstance(obj, BooleanObject):
        return ("bool", bool(obj))
    if isinstance(obj, (NumberObject, FloatObject)):
        return ("num", float(obj))
    if isinstance(obj, NullObject) or obj is None:
        return ("null",)
    return (type(obj).__name__, str(obj))


def _doclevel(path):
    """({"info", "root", "pages"}, None) or (None, why). Never raises."""
    try:
        from pypdf import PdfReader
        r = PdfReader(path, strict=False)
        pages = {}
        for i, p in enumerate(r.pages):
            ref = p.indirect_reference
            if ref is not None:
                pages[(ref.idnum, ref.generation)] = i + 1
        info = r.trailer.get("/Info")
        root = r.trailer["/Root"]
        root_d = root.get_object()
        out = {
            "info": _plain(info, pages, frozenset()) if info is not None else ("absent",),
            "root": {str(k): _plain(v, pages, frozenset())
                     for k, v in root_d.items() if k != "/Pages"},
            "pages": [{str(k): _plain(v, pages, frozenset())
                       for k, v in p.items() if k not in ("/Contents", "/Resources", "/Parent")}
                      for p in r.pages],
        }
        return out, None
    except Exception as e:                                   # noqa: BLE001 — unreadable is undecided
        return None, "%s: document-level content unreadable (%s: %s)" % (path, type(e).__name__, e)


def _first_diff(a, b, path=""):
    """The first path at which two plain values differ, with both sides, or None."""
    if isinstance(a, dict) and isinstance(b, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a or k not in b:
                return "%s/%s: %s in old, %s in new" % (
                    path, k, "present" if k in a else "absent", "present" if k in b else "absent")
            d = _first_diff(a[k], b[k], "%s/%s" % (path, k))
            if d:
                return d
        return None
    if isinstance(a, list) and isinstance(b, list):
        if len(a) != len(b):
            return "%s: %d item(s) in old, %d in new" % (path, len(a), len(b))
        for i, (x, y) in enumerate(zip(a, b)):
            d = _first_diff(x, y, "%s[%d]" % (path, i))
            if d:
                return d
        return None
    if a != b:
        return "%s: old %r, new %r" % (path, a, b)
    return None


def _doc_diff(da, db):
    """The first differing path across the three components, or None when all are identical."""
    for part in ("info", "root", "pages"):
        d = _first_diff(da[part], db[part], part)
        if d:
            return d
    return None


def compare(old, new):
    """(exit code, message). The whole decision; `main` only prints it. ANY exception, an import
    failure included, is CANNOT-DECIDE: a crash is "could not tell", never DIFFERENT and never SAME."""
    try:
        return _compare(old, new)
    except Exception as e:                                   # noqa: BLE001
        return CANNOT_DECIDE, "unexpected %s: %s (nothing was decided)" % (type(e).__name__, e)


def _compare(old, new):
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
    da, why_a = _doclevel(old)
    db, why_b = _doclevel(new)
    if da is None or db is None:
        return CANNOT_DECIDE, "pixels and text identical, but %s" % (why_a or why_b)
    diff = _doc_diff(da, db)
    if diff:
        return DIFFERENT, ("pixels and extracted text identical on all %d page(s), document-level "
                           "content differs at %s" % (na, diff))
    return SAME, ("%d page(s), pixel-identical at scale %s, extracted text identical, document-level "
                  "content identical (info, catalog, page dictionaries)" % (na, SCALE))


def _cli(argv):
    """`main` with every unexpected exception, an import failure included, mapped to exit 2."""
    try:
        return main(argv)
    except Exception as e:                                   # noqa: BLE001
        print("pdf_same: CANNOT-DECIDE — unexpected %s: %s (nothing was decided)"
              % (type(e).__name__, e))
        return CANNOT_DECIDE


# ------------------------------------------------------------------ controls
#
# Each control builds its PDFs with reportlab in a temporary directory, MUST PASS on this module and
# MUST FAIL on a mutant with exactly one protection removed. A control nobody has seen fail is a
# hypothesis, so a mutation that does not apply fails the suite.

def _build(path, arrow="AB", fill="white", bold=False, extra_page=False, hidden=None,
           title="Doc A", outline="Section 1", link="https://example.org/", border=0):
    from reportlab.lib import colors
    from reportlab.pdfgen import canvas
    c = canvas.Canvas(path, pagesize=(300, 200), invariant=1)   # no build timestamp, as zp_utils
    c.setTitle(title)
    c.setFont("Helvetica-Bold" if bold else "Helvetica", 12)
    c.drawString(20, 170, "The map is injective.")
    c.bookmarkPage("s1")
    c.addOutlineEntry(outline, "s1", level=0)
    c.linkURL(link, (20, 160, 200, 185), relative=0, thickness=border,
              color=colors.blue if border else None)
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
                     ("pages", {"extra_page": True}), ("hidden", {"hidden": "hidden words"}),
                     ("title", {"title": "Doc B"}), ("outline", {"outline": "Section 99"}),
                     ("border", {"border": 1}), ("url", {"link": "https://elsewhere.example/"})):
        f[name] = os.path.join(d, name + ".pdf")
        _build(f[name], **kw)
    for name, packet in (("xmp1", "<x:xmpmeta>title A</x:xmpmeta>"),
                         ("xmp2", "<x:xmpmeta>title B</x:xmpmeta>")):
        from pypdf.generic import DecodedStreamObject, NameObject
        w = PdfWriter(clone_from=f["base"])
        s = DecodedStreamObject()
        s.set_data(packet.encode("utf-8"))
        s[NameObject("/Type")] = NameObject("/Metadata")
        s[NameObject("/Subtype")] = NameObject("/XML")
        w._root_object[NameObject("/Metadata")] = w._add_object(s)
        f[name] = os.path.join(d, name + ".pdf")
        with open(f[name], "wb") as fh:
            w.write(fh)
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


def _pixels(path):
    import pypdfium2 as pdfium
    doc = pdfium.PdfDocument(path)
    try:
        out = []
        for i in range(len(doc)):
            page = doc[i]
            try:
                out.append(page.render(scale=SCALE).to_pil().tobytes())
            finally:
                page.close()
        return out
    finally:
        doc.close()


def _ctl_doclevel(m, f, a, b):
    """DIFFERENT, with the pixels AND the extracted text measured identical (by this module's own
    renderer, not the module under test), so only the document-level leg can be what saw it."""
    px = _pixels(f[a]) == _pixels(f[b])
    tx = _text(f[a]) == _text(f[b])
    ok, why = _expect(m, f, a, b, DIFFERENT)
    return ok and px and tx, why + "; pixels identical=%s, text identical=%s" % (px, tx)


def _ctl_doclevel_unreadable(m, f):
    """Both files' document-level content unreadable: CANNOT-DECIDE, never SAME."""
    saved = m._doclevel
    m._doclevel = lambda p: (None, "%s: ctl: unreadable" % os.path.basename(p))
    try:
        return _expect(m, f, "base", "base2", CANNOT_DECIDE)
    finally:
        m._doclevel = saved


_BLOCKER = r"""
import runpy, sys
class _Block(object):
    def find_spec(self, name, path=None, target=None):
        if name == %(mod)r or name.startswith(%(mod)r + "."):
            raise ImportError("ctl: %%s blocked" %% name)
sys.meta_path.insert(0, _Block())
for k in [k for k in sys.modules if k == %(mod)r or k.startswith(%(mod)r + ".")]:
    del sys.modules[k]
sys.argv = [%(script)r, %(old)r, %(new)r]
runpy.run_path(%(script)r, run_name="__main__")
"""


def _ctl_cli_blocked(m, f, mod):
    """The CLI, as a separate process, with one import blocked: must EXIT 2, never 1. Runs the
    source of `m` (the live file, or the mutant's text) from a temp copy."""
    import subprocess
    src = getattr(m, "_MUTANT_SRC", None)
    if src is None:
        with open(os.path.abspath(__file__), encoding="utf-8") as fh:
            src = fh.read()
    script = os.path.join(os.path.dirname(f["base"]), "pdf_same_ctl_copy.py")
    with open(script, "w", encoding="utf-8") as fh:
        fh.write(src)
    env = dict(os.environ)
    here = os.path.dirname(os.path.abspath(__file__))
    env["PYTHONPATH"] = here + os.pathsep + env.get("PYTHONPATH", "")
    code = _BLOCKER % {"mod": mod, "script": script, "old": f["base"], "new": f["arrow"]}
    p = subprocess.run([sys.executable, "-c", code], env=env, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", timeout=120)
    last = (p.stdout.strip().splitlines() or [p.stderr.strip()[-160:]])[0]
    return p.returncode == CANNOT_DECIDE, "%s blocked -> exit %s: %s" % (mod, p.returncode, last)


_CONTROLS_MARK = "# " + "-" * 66 + " controls"

# (label, control, anchor, replacement): the replacement removes exactly what the control guards.
_CONTROLS = [
    ("identical builds are SAME", _ctl_identical,
     "    return SAME, (\"%d page(s), pixel-identical",
     "    return DIFFERENT, (\"%d page(s), pixel-identical"),
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
    # ⚠ `/rely` 2026-10-04 BLOCKING-1: the document-level leg. Each pair is pixel- and
    #   text-identical; each mutant drops the component that pair differs in.
    ("changed /Title is DIFFERENT (pixels, text same)", lambda m, f: _ctl_doclevel(m, f, "base", "title"),
     '    for part in ("info", "root", "pages"):',
     '    for part in ("root", "pages"):'),
    ("document-level leg skipped entirely", lambda m, f: _ctl_doclevel(m, f, "base", "title"),
     "    if diff:\n        return DIFFERENT",
     "    if False:\n        return DIFFERENT"),
    ("changed bookmark text is DIFFERENT", lambda m, f: _ctl_doclevel(m, f, "base", "outline"),
     '    for part in ("info", "root", "pages"):',
     '    for part in ("info", "pages"):'),
    ("changed XMP metadata is DIFFERENT", lambda m, f: _ctl_doclevel(m, f, "xmp1", "xmp2"),
     '    for part in ("info", "root", "pages"):',
     '    for part in ("info", "pages"):'),
    ("added link border is DIFFERENT", lambda m, f: _ctl_doclevel(m, f, "base", "border"),
     '    for part in ("info", "root", "pages"):',
     '    for part in ("info", "root"):'),
    ("changed link URL is DIFFERENT", lambda m, f: _ctl_doclevel(m, f, "base", "url"),
     '    for part in ("info", "root", "pages"):',
     '    for part in ("info", "root"):'),
    ("unreadable doc-level content is CANNOT-DECIDE", _ctl_doclevel_unreadable,
     '        return CANNOT_DECIDE, "pixels and text identical, but %s"',
     '        return SAME, "pixels and text identical, but %s"'),
    # ⚠ `/rely` 2026-10-04 ORDINARY-3: a crash exited 1 (DIFFERENT). Run as a real process.
    ("CLI: PIL import blocked exits 2, not 1", lambda m, f: _ctl_cli_blocked(m, f, "PIL"),
     '        return CANNOT_DECIDE, "unexpected %s: %s (nothing was decided)"',
     '        return DIFFERENT, "unexpected %s: %s (nothing was decided)"'),
    ("CLI: `common` import blocked exits 2, not 1", lambda m, f: _ctl_cli_blocked(m, f, "common"),
     "              % (type(e).__name__, e))\n        return CANNOT_DECIDE",
     "              % (type(e).__name__, e))\n        return DIFFERENT"),
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
    mutated = head.replace(anchor, repl, 1) + sep + tail
    try:
        code = compile(mutated, src_path + ".mutant", "exec")
    except SyntaxError as e:
        return None, "MUTATION DID NOT APPLY — mutant does not compile: %s" % (e,)
    mod = types.ModuleType("zp_pdf_same_mutant")
    mod.__file__ = src_path
    mod._MUTANT_SRC = mutated          # the CLI controls run this text as a separate process
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
    import common                # inside main, so a failing import is caught as CANNOT-DECIDE
    common.utf8_stdout()
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
    sys.exit(_cli(sys.argv))
