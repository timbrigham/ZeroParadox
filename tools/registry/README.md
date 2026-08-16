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
Re-running the extractor against that tree reproduces that inventory exactly. ⚠ **The count is deliberately not written here.** It read `1025` while line 78 of this same file read `~1012`, and an independent re-run at the pinned tree measured 1012 — so the figure was both wrong and self-contradictory, and an earlier edit made it worse by removing the `currently` hedge that had at least flagged it as volatile.
Per this project's standing rule, **measure it rather than quoting it**: run the extractor against the pinned commit and read the number from `tm_registry.py`.

## Identifier handling (why the count is what it is)

Declaration names are captured with full Unicode fidelity. Lean names in this corpus routinely use
non-ASCII characters — subscripts (`c₀`, `T₂`, `nmul_nadd_lt₃`), Greek initials (`σ`, `ωeval`) — so
the identifier capture is Lean/Unicode-aware rather than ASCII-only. (An earlier ASCII-only pass
silently truncated subscripted names and dropped Greek-initial names entirely; that is fixed here.)

## What is EXCLUDED, and why (both logged, never silent)

The registry tracks *Zero Paradox framework* declarations — the things that get cited, renamed, and
restructured. Two categories are excluded by explicit policy, and the excluded counts are printed on
every run:

1. **Vendored external code** (`EXCLUDE_DIRS` — `ZeroParadox/Vendored/`). **One file:
   `NaturalOps.lean`**, verbatim Mathlib / Combinatorial-Game-Theory code
   (Violeta Hernández, Apache-2.0), vendored because the upstream copy was removed after Mathlib
   v4.28. It is not Zero Paradox original work, is never cited by name in the framework, and is
   never restructured — registering it would only add infrastructure noise and misattribute
   provenance. **Measured: 0 declarations from `ZeroParadox/Vendored/` are in the store.**

   ⚠ **`ZeroParadox/Ordinal/NaturalOpsPow.lean` IS NOT IN THIS CATEGORY, AND THIS PARAGRAPH SAID IT
   WAS.** It is a **PORT**, not a verbatim copy — Hernández's `CombinatorialGames` proof adapted to
   the vendored v4.28 API, with every port change marked `-- [ZP]`. Measured 2026-08-16, both of the
   reasons given above are false of it: **20 of its declarations are registered**, and
   `Ordinal/KirbyParis.lean` cites `NaturalOpsPow.nadd_lt_omega0_opow` **by name**. Its only
   exemption is from the PROSE checkers, via `vendored.py`'s content allowlist, on the ground that
   its header and proof commentary are upstream's.

   ⚠ **That leaves it in an incoherent middle, and the inconsistency is OPEN rather than resolved:**
   it is exempt like vendored code, but registered and cited like framework code, and filed like
   framework code. Two of those three have to agree. Do not read this paragraph as ratifying the
   current arrangement.

2. **Source-unnamed anonymous instances** (`INCLUDE_ANON = False`). `instance : Foo` declarations
   whose names Lean generates at compile time have no citable source name and no stable identity to
   track across a move, so they are excluded by default. The flag can flip to include them (as
   null-named, file+line-keyed entries) if a complete census is ever wanted.

Both policies must be applied consistently by every scan for the conservation guarantee to hold.

## The published SSOT (`ssot.json`) and its vocabulary (`tag_vocab.json`)

**The canonical SSOT is `ssot.json` at the repo root** — the single, authoritative export every consumer
reads. It is the validated, byte-stable `export_full` output of the SSOT registry (SJV), and it is
produced **only** by `mcp__sjv__export_full` written to the **absolute** repo-root path
(`.../ZeroParadox/ssot.json`) — never hand-edited, never copied, and never read from a second location.
(SJV resolves a *relative* `dest` against its own working directory, so the absolute path is required to
land the file at the repo root; passing a bare `ssot.json` writes it beside the MCP instead.) As of
the claims-layer work it is a **multi-collection envelope**, not a bare declaration list:

```
{ "collections": {
    "declarations": { "entries": [...], "vocab": {...}, "anchor": {...}, "counts": {...} },
    "claims":       { "entries": [...], "vocab": {...} },
    "deps":         { "entries": [...] } },
  "store_version": "2" }
```

- **`collections.declarations.entries`** — the declaration inventory enriched with an **ontology
  overlay**: per-declaration `object` / `domain` / `role` tags (each a controlled, multi-valued list).
  ⚠ This line read `~1012-declaration` — a **fourth** wrong value for the figure line 29 of this same
  file already forbids writing down, 48 lines above it. Measured on the live store it is 1676. The
  count is not recorded here; measure it.
- **`collections.claims.entries`** — the curated **claim graph**: ⊥-face domain nodes, the adjudicated
  inter-domain edges, and the free-standing keystones. Each claim carries a `status`
  (`proved`/`deep`/`corr`/`conj`/`commitment`), and a declaration links back to a claim via its
  `claims.witness_of`. The store enforces a cross-collection invariant: a `proved`/`deep` claim is
  refused unless a sorry-free declaration witnesses it, so the published graph cannot overstate the
  formal evidence.
- **`collections.deps.entries`** — the declaration-level **dependency graph**: directed edges
  `{from, to, kind}` where `from` compiles-depends on `to` (`kind` = `type` if the dependency appears in
  the dependent's signature, else `proof`). Extracted mechanically from the Lean environment
  (`ZeroParadox/Meta/ExtractDeps.lean` → `deps_build.py`), it is derived data — re-extracted and
  whole-collection-replaced, never hand-curated. Endpoints reference declaration `qualified` names; the
  store refuses any edge whose endpoint is not a live declaration (no dangling edges). This is the backbone
  for the eventual codebase restructure (validating a proposed `new.*` module layout against the import DAG).

`tag_vocab.json` is the controlled vocabulary the declaration tags are drawn from — the allowed values
for each axis, their cardinalities, and one-line glosses. (Consumers should read the
`collections.declarations.entries` path; the legacy top-level `entries` shape is superseded. The
`tools/render/` extractor handles both shapes transparently.)

## Refactor-support tooling (the codebase restructure will be verified, not trusted)

The registry is the blueprint for an eventual reorganization of the Lean sources into a legible,
mathematician-facing structure. That restructure is done **incrementally and content-preservingly** —
every cut is checked against a baseline, because a refactor can compile cleanly and still drop a
declaration, change what a theorem proves, or introduce an axiom. The tooling:

- **`ZeroParadox/Meta/ExtractDeps.lean`** — the dependency extractor (env-walk metaprogram) → `deps_build.py`
  → the `deps` collection above. Run: `lake build ZeroParadox.Meta.ExtractDeps`.
- **`ZeroParadox/Meta/Snapshot.lean`** — the **golden-master** metaprogram: per declaration, a structural
  fingerprint of its TYPE (`Expr.hash`) and its transitive AXIOM profile. Run:
  `lake build ZeroParadox.Meta.Snapshot`.
- **`refactor_check.py`** — the differential content-preservation checker. Diffs a frozen baseline snapshot
  against the current state across four layers: inventory (drops/adds, renames inferred by type-hash),
  STATEMENTS (a changed type-hash = an altered statement), PURITY (a changed axiom profile = a regression),
  DEPENDENCY (edge diff = the structural change the cut made). Exit 0 = content preserved, 1 = changed.
- **`regen_meta_imports.py`** — regenerates the two metaprograms' import headers (they import every ZP module
  by a fixed list); run after any file add/move/delete, before re-snapshotting.
- **`deps_build.py`** — intersects the raw extractor output with the registry's tracked qualified set,
  assigns `kind` (type/proof), and emits the final dependency edge list.

The workflow per cut: freeze a baseline once → make ONE incremental cut → rebuild → re-snapshot →
`refactor_check.py`. Because cuts are done one at a time, any content change is localized to the last one.
(`ZeroParadox/Meta/*` is not imported by `Basic`, so a normal `lake build` skips these metaprograms.)

**Status: work in progress (this is a dedicated working branch).** The ontology tagging is mid-pass —
domains are largely assigned, roles partially, and a batch of experimental-campaign results are
provisionally marked `scaffolding` pending a load-bearing/decorative reclassification. It is a snapshot of
active work, not a finalized layer.
