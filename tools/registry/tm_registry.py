#!/usr/bin/env python3
"""Translation-matrix / SSOT registry builder — emits the canonical registry.json.

One entry per declaration in ZeroParadox/**/*.lean, keyed by OLD qualified name. Populates only the
MECHANICAL fields (old.*, verify.sorry_free at file granularity). Curated fields (new.*, ontology.*,
claims.*) are left null/pending until the object x domain structure is decided — the schema anticipates
them so nothing has to be re-migrated later.

This JSON is the single source of truth: the migration checker reads it, and (later) the CLAIMS / web /
BOTTOMELEMENT / citation-rewrite views are generated from it.

Run:  python .claude-local/tm_registry.py
Out:  .claude-local/translation_matrix/registry.json
"""
import os, re, sys, json
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

# This tool lives at <repo>/tools/registry/ (public transparency copy). Repo root is three
# levels up. Generated output stays in the private working dir .claude-local/translation_matrix/
# (gitignored) — the PUBLISHED registry is produced separately by sjv's export_full, not here.
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(REPO, "ZeroParadox")
OUTDIR = os.path.join(REPO, ".claude-local", "translation_matrix")
os.makedirs(OUTDIR, exist_ok=True)
OUT = os.path.join(OUTDIR, "registry.json")

# anchor: the immutable public-production reference this baseline corresponds to
ANCHOR = {
    "branch": "origin/main",
    "commit": "7075d4abfe49b81c0080166d848e08579f1cafb7",
    "tree":   "eacbc513a541d465b9937b33a53f923d3e9ea4b6",
}

# Directory prefixes EXCLUDED from the registry by policy: external / vendored code that
# is not Zero Paradox original work. It is credited upstream (Apache-2.0), never cited in
# ZP prose by name, and never restructured into a ZP domain namespace — registering it
# would only add infra noise and muddy provenance. Excluded consistently from every scan
# so the loss-checker never sees phantom churn. The exclusion is COUNTED and logged, never
# silent. (ZeroParadox/Vendored/ = Mathlib NaturalOps + the CGT NaturalOpsPow port.)
EXCLUDE_DIRS = ("ZeroParadox/Vendored/",)

def is_excluded(rel):
    return any(rel.startswith(d) for d in EXCLUDE_DIRS)

# Register anonymous instances (source-unnamed `instance : Foo`)? They have no
# citable name; excluding is defensible for a citation-rewrite registry as long
# as old and new scans skip them consistently. Flip to True to include them as
# short=None entries keyed by file+line. (Scope decision, not a bug.)
INCLUDE_ANON = False

# Capture the RAW token after the keyword; clean_name() then validates it as a
# Lean identifier. The old class [A-Za-z0-9_'.]+ truncated non-ASCII names
# (c₀ -> c, nmul_nadd_lt₃ -> nmul_nadd_lt) and dropped Greek-initial names
# (σ, ωeval) entirely — a silent conservation failure.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+|unsafe\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+(\S+)")
NS  = re.compile(r"^\s*namespace\s+(\S+)")
SEC = re.compile(r"^\s*section\b\s*(\S+)?")
END = re.compile(r"^\s*end\b")
SORRY = re.compile(r"\bsorry\b")

# characters that terminate an identifier when they follow it (binders, type ascription, ...)
_STOP = ":({[⦃⟨⟮"
_UNIV = re.compile(r"\.\{.*$")  # universe annotation  foo.{u,v}

def clean_name(tok):
    """Return the Lean identifier from a raw post-keyword token, or None if the
    token is anonymous (`:`/binder start) or prose (`—`, etc.)."""
    tok = _UNIV.sub("", tok)
    cut = len(tok)
    for ch in _STOP:
        i = tok.find(ch)
        if i != -1:
            cut = min(cut, i)
    name = tok[:cut].strip()
    if not name:
        return None
    # a Lean identifier starts with a (unicode) letter, `_`, or the French-quote «
    if not (name[0].isalpha() or name[0] in "_«"):
        return None
    return name

def prefix_of(fn):
    m = re.match(r"(ZP[A-Z])", fn)
    return m.group(1) if m else "(misc)"

def clean_lines(f):
    """Yield (lineno, code) with comments removed, so NS/SEC/END/DECL never match keyword
    words inside docstrings/comments. Handles NESTED block comments `/- /- -/ -/` (incl. `/--`
    docstrings and `/-!` module docs — both are `/-` variants) and `--` line comments; block
    state persists across lines. Line numbers are preserved. (Heuristic: does not model string
    literals containing `/-`/`--`; the Lean build is the authoritative check.)

    Rationale: WITHOUT this, a docstring line `theorem and cannot be…` became a phantom decl
    `and`, and a prose line `end inward…` popped the namespace stack — mis-qualifying real
    decls (e.g. ZPG.t6 recorded bare). Caught by the trust-root check 2026-07-01."""
    depth = 0
    for ln, line in enumerate(f, 1):
        out, i, n = [], 0, len(line)
        while i < n:
            two = line[i:i+2]
            if depth == 0:
                if two == "--":
                    break                      # line comment: ignore rest of line
                if two == "/-":
                    depth += 1; i += 2; continue
                out.append(line[i]); i += 1
            else:
                if two == "-/":
                    depth -= 1; i += 2; continue
                if two == "/-":
                    depth += 1; i += 2; continue
                i += 1
        yield ln, "".join(out)

def scan_file(path):
    stack, out, file_sorry = [], [], False
    with open(path, encoding="utf-8") as f:
        for ln, line in clean_lines(f):
            if SORRY.search(line):             # sorry in a comment no longer counts (cleaned)
                file_sorry = True
            if NS.match(line):
                stack.append(("ns", NS.match(line).group(1))); continue
            if END.match(line):
                if stack: stack.pop()
                continue
            if SEC.match(line) and not DECL.match(line):
                stack.append(("sec", None)); continue
            d = DECL.match(line)
            if d:
                kind, raw = d.group(1), d.group(2)
                short = clean_name(raw)
                if short is None:
                    # genuine anonymous instance (`instance : Foo`) vs prose false-positive
                    if not (INCLUDE_ANON and kind == "instance" and raw[:1] in ":[("):
                        continue
                    short = None  # register anon instance with a null name
                nsparts = [n for (t, n) in stack if t == "ns"]
                if short is None:
                    qualified = None
                else:
                    qualified = ".".join(nsparts + [short]) if nsparts else short
                out.append((qualified, short, kind, ln))
    return out, file_sorry

def main():
    entries, seen, collisions = [], {}, []
    files = 0
    excluded_files, excluded_decls = [], 0
    for dp, _, fnames in os.walk(SRC):
        for fn in sorted(fnames):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dp, fn)
            rel = os.path.relpath(full, REPO).replace(os.sep, "/")
            if is_excluded(rel):
                d, _ = scan_file(full)
                excluded_files.append(rel); excluded_decls += len(d)
                continue
            files += 1
            decls, file_sorry = scan_file(full)
            for (q, s, k, ln) in decls:
                # id is the guaranteed-unique primary key (bare qualified name collides 12x)
                eid = f"{rel}::{q}::L{ln}"
                if eid in seen:
                    collisions.append((eid, seen[eid], rel))
                seen[eid] = rel
                entries.append({
                    "id": eid,
                    # UNIFORM SHAPE: every key present at every level; only leaf scalars may be null.
                    "old": {"qualified": q, "short": s, "kind": k, "file": rel,
                            "line": ln, "prefix": prefix_of(fn)},
                    "new": {"qualified": None, "short": None, "file": None, "namespace": None},
                    "disposition": "pending",
                    "reason": None,
                    "ontology": {"object": None, "domain": None, "role": None},
                    "claims": {"witness_of": [], "citations": []},
                    # corpus verified sorry-free at the anchor (grep: no live `sorry` tactic anywhere);
                    # per-declaration axiom/sorry data is enriched from a lake pass later.
                    "verify": {"sorry_free": True, "axioms": None},
                })

    doc = {
        "schema_version": "1",
        "purpose": "Canonical SSOT registry + migration translation matrix for the ontology revamp. "
                   "Mechanical fields populated from the frozen baseline; curated fields deferred.",
        "anchor": ANCHOR,
        "counts": {"files": files, "declarations": len(entries)},
        "notes": {
            "verify.sorry_free": "file-granularity heuristic (file contains no `sorry`); the Lean build is "
                                 "the authoritative semantic check.",
            "curated_deferred": "new.*, ontology.*, claims.* are null until the object x domain structure "
                                "is agreed.",
            "excluded_by_policy": f"{excluded_decls} declarations in {len(excluded_files)} vendored file(s) "
                                  f"excluded (external Mathlib code, not ZP-original): {excluded_files}",
        },
        "entries": entries,
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(doc, f, indent=1, ensure_ascii=False)

    print(f"wrote {OUT}")
    print(f"files: {files}   declarations: {len(entries)}")
    print(f"EXCLUDED by policy: {excluded_decls} decls in {len(excluded_files)} vendored file(s): {excluded_files}")
    print(f"unique qualified names: {len(seen)}   (entries - unique = duplicate-qualified: {len(entries)-len(seen)})")
    sorry_files = sorted({e['old']['file'] for e in entries if not e['verify']['sorry_free']})
    print(f"files flagged with a `sorry` token: {len(sorry_files)}")
    for fp in sorry_files:
        print(f"    sorry? {fp}")
    if collisions:
        print(f"\nQUALIFIED-NAME COLLISIONS ({len(collisions)}) — same qualified name in 2 files (reopened "
              f"namespace or dup); id is not unique for these, review:")
        for (q, a, b) in collisions[:20]:
            print(f"    {q}  :: {a}  &  {b}")

if __name__ == "__main__":
    main()
