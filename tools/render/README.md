# tools/render — registry-driven diagram generators

Source-visibility copy of the tooling that draws the Zero Paradox "web" diagrams from the SSOT
registry. Like `tools/registry/` (the extractor) and `scripts/` (the PDF-build copy), this folder
exists so the provenance of a generated figure is inspectable: you can see exactly how each diagram
is built and re-run it to check that every line on the canvas is backed by a tagged declaration.

## The honest-by-construction property

These renderers read the registry export (`tools/registry/registry_export.json`) and draw **only what
the register sanctions**. A domain node appears iff some declaration realizes ⊥ (or an edge references
it); an edge appears iff ≥1 declaration tagged `bridge` / `core` / `no-go` spans those two domains. The
diagram *cannot* draw a relation the register does not carry — so it cannot overstate the framework.
The two "hubs" are the two highest-degree domains **derived from the data**, not asserted.

## Scripts

- `web_data.py` — the shared extractor. Reads the export, returns nodes (domain faces of ⊥), edges
  (`bridge` = directional transform, `core` = cross-domain identity, `no-go` = obstruction; each with
  its backing decl names), and the data-derived hubs. Run standalone to print the graph summary.
- `make_web_diagram.py` — the ring map: ⊥ at the centre, domain faces on a ring, status-coded edges.
- `make_web_tree.py` — the tree/DAG view: domains (top) descend through the two hubs into ⊥ (bottom).

The gloss that prettifies each domain's label (e.g. valuation → "p-adic floor v₂(0)=∞") is the only
hand-written content; the *structure* (which nodes, which edges) is entirely registry-derived.

## Run

```
python tools/render/web_data.py                 # print the extracted graph (nodes / edges / hubs)
python tools/render/make_web_diagram.py          # -> tools/render/the_web_honest_map.svg
python tools/render/make_web_tree.py             # -> tools/render/the_web_tree.svg
```

Both accept an optional export path argument (defaults to `../registry/registry_export.json`) and are
deterministic — the same export produces byte-identical SVGs. The generated `.svg` files are artifacts
(gitignored); re-run to regenerate against the current register. Pure standard-library Python, no deps.
