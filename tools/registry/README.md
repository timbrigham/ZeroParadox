# tools/registry — the Zero Paradox declaration extractor

Source-visibility copy of the tooling that produces the mechanical declaration inventory for
the Zero Paradox SSOT registry. Like `scripts/` (the PDF-build transparency copy), this folder
exists so the provenance of a generated artifact is inspectable — you can see exactly how the
registry's baseline was built, and re-run it to check the numbers. It is not a packaged/installable
tool; it is Python that scans this repo's Lean source.

## What it does

`tm_registry.py` walks `ZeroParadox/**/*.lean` and emits one record per top-level declaration
(`theorem/lemma/def/abbrev/instance/structure/class/inductive`), capturing the mechanical facts:
qualified name, short name, kind, file, line, and prefix. `tm_facts.py` emits the same facts as a
flat list (`scanner_output.json`) — the payload consumed by the registry's `import_baseline`.

Run:
```
python tools/registry/tm_facts.py        # -> .claude-local/translation_matrix/scanner_output.json
python tools/registry/tm_registry.py     # -> .claude-local/translation_matrix/registry.json (proof-of-shape)
```
Generated output is written to `.claude-local/translation_matrix/` (a private working dir,
gitignored). The **published** registry is produced separately, from the registry tool's own
validated `export_full` — not by committing this tool's raw output.

## The frozen anchor

The baseline corresponds to a fixed public-production commit (recorded in `tm_registry.py`):
`origin/main @ 7075d4abfe49b81c0080166d848e08579f1cafb7` (tree `eacbc513a541d465b9937b33a53f923d3e9ea4b6`).
Re-running the extractor against that tree reproduces the same inventory (currently **1025**
declarations across 136 declaration-bearing files).

## Identifier handling (why the count is what it is)

Declaration names are captured with full Unicode fidelity. Lean names in this corpus routinely use
non-ASCII characters — subscripts (`c₀`, `T₂`, `nmul_nadd_lt₃`), Greek initials (`σ`, `ωeval`) — so
the identifier capture is Lean/Unicode-aware rather than ASCII-only. (An earlier ASCII-only pass
silently truncated subscripted names and dropped Greek-initial names entirely; that is fixed here.)

## What is EXCLUDED, and why (both logged, never silent)

The registry tracks *Zero Paradox framework* declarations — the things that get cited, renamed, and
restructured. Two categories are excluded by explicit policy, and the excluded counts are printed on
every run:

1. **Vendored external code** (`EXCLUDE_DIRS` — `ZeroParadox/Vendored/`). These files
   (`NaturalOps.lean`, `NaturalOpsPow.lean`) are Mathlib / Combinatorial-Game-Theory code
   (Violeta Hernández, Apache-2.0), vendored because the upstream copy was removed after Mathlib
   v4.28. They are not Zero Paradox original work, are never cited by name in the framework, and are
   never restructured — registering them would only add infrastructure noise and misattribute
   provenance.

2. **Source-unnamed anonymous instances** (`INCLUDE_ANON = False`). `instance : Foo` declarations
   whose names Lean generates at compile time have no citable source name and no stable identity to
   track across a move, so they are excluded by default. The flag can flip to include them (as
   null-named, file+line-keyed entries) if a complete census is ever wanted.

Both policies must be applied consistently by every scan for the conservation guarantee to hold.

## The published registry (`registry_export.json`) and its vocabulary (`tag_vocab.json`)

`registry_export.json` is the validated, byte-stable `export_full` output of the SSOT registry. As of
the claims-layer work it is a **multi-collection envelope**, not a bare declaration list:

```
{ "collections": {
    "declarations": { "entries": [...], "vocab": {...}, "anchor": {...}, "counts": {...} },
    "claims":       { "entries": [...], "vocab": {...} } },
  "store_version": "2" }
```

- **`collections.declarations.entries`** — the ~1012-declaration inventory enriched with an **ontology
  overlay**: per-declaration `object` / `domain` / `role` tags (each a controlled, multi-valued list).
- **`collections.claims.entries`** — the curated **claim graph**: ⊥-face domain nodes, the adjudicated
  inter-domain edges, and the free-standing keystones. Each claim carries a `status`
  (`proved`/`deep`/`corr`/`conj`/`commitment`), and a declaration links back to a claim via its
  `claims.witness_of`. The store enforces a cross-collection invariant: a `proved`/`deep` claim is
  refused unless a sorry-free declaration witnesses it, so the published graph cannot overstate the
  formal evidence.

`tag_vocab.json` is the controlled vocabulary the declaration tags are drawn from — the allowed values
for each axis, their cardinalities, and one-line glosses. (Consumers should read the
`collections.declarations.entries` path; the legacy top-level `entries` shape is superseded. The
`tools/render/` extractor handles both shapes transparently.)

**Status: work in progress (this is a dedicated working branch).** The ontology tagging is mid-pass —
domains are largely assigned, roles partially, and a batch of experimental-campaign results are
provisionally marked `scaffolding` pending a load-bearing/decorative reclassification. It is a snapshot of
active work, not a finalized layer.
