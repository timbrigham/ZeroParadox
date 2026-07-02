#!/usr/bin/env python3
"""Facts-only emitter for the SSOT registry baseline import.

Re-uses tm_registry.py's exact scan logic, but emits ONLY the mechanical
scanner_output list (one dict per declaration: qualified/short/kind/file/line/
prefix) — the payload sjv's protected `import_baseline(scanner_output, anchor)`
op expects. This is the sanctioned population path: the facts reach the registry
THROUGH the gate, not by adopting the hand-built registry.json.

The Lean source in the working tree is verified identical to the anchor
(7075d4a) for all ZeroParadox/**/*.lean, so a working-tree scan == anchor scan.

Run:  python .claude-local/tm_facts.py [N]
        N (optional) = emit only the first N declarations (for a test import).
Out:  .claude-local/translation_matrix/scanner_output.json   (full or sliced)
      also prints the count and the anchor.
"""
import os, sys, json

# reuse the proven scanner + policy verbatim
from tm_registry import scan_file, prefix_of, is_excluded, ANCHOR, SRC, REPO

def emit():
    facts, files = [], 0
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
            decls, _ = scan_file(full)
            for (q, s, k, ln) in decls:
                facts.append({
                    "qualified": q, "short": s, "kind": k,
                    "file": rel, "line": ln, "prefix": prefix_of(fn),
                })
    return facts, files, excluded_files, excluded_decls

def main():
    facts, files, excluded_files, excluded_decls = emit()
    n = None
    if len(sys.argv) > 1:
        n = int(sys.argv[1])
        facts = facts[:n]
    # output goes to the private working dir (.claude-local/translation_matrix/, gitignored);
    # REPO is imported from tm_registry. The published registry comes from sjv export_full.
    outdir = os.path.join(REPO, ".claude-local", "translation_matrix")
    out = os.path.join(outdir, "scanner_output.json")
    with open(out, "w", encoding="utf-8") as f:
        json.dump(facts, f, indent=1, ensure_ascii=False)
    print(f"wrote {out}")
    print(f"files scanned: {files}   declarations emitted: {len(facts)}"
          + (f"  (sliced to first {n})" if n is not None else "  (full)"))
    print(f"EXCLUDED by policy: {excluded_decls} decls in {len(excluded_files)} vendored file(s): {excluded_files}")
    print(f"anchor: {ANCHOR['commit']}  tree {ANCHOR['tree']}")

if __name__ == "__main__":
    main()
