# tools/render — registry-driven diagram generators

Source-visibility copy of the tooling that draws the Zero Paradox "web" diagrams from the SSOT
registry. Like `tools/registry/` (the extractor) and `scripts/` (the PDF-build copy), this folder
exists so the provenance of a generated figure is inspectable: you can see exactly how each diagram
is built and re-run it to check that every line on the canvas is backed by a tagged declaration.

## The honest-by-construction property

These renderers read the SSOT export (`ssot.json` at the repo root) and draw **only what
the register sanctions**. A domain node appears iff some declaration realizes ⊥ (or an edge references
it); an edge appears iff ≥1 declaration tagged `bridge` / `core` / `no-go` spans those two domains. The
diagram *cannot* draw a relation the register does not carry — so it cannot overstate the framework.
The two "hubs" are the two highest-degree domains **derived from the data**, not asserted.

## Two graphs: the derived web, and the curated claim graph

- **The decl-derived web** (`make_web_diagram.py`, `make_web_tree.py`) is *descriptive* — it draws a
  node for every domain some declaration realizes ⊥ in, and an edge for every `bridge`/`core`/`no-go`
  declaration spanning two domains. It shows the whole tagged surface.
- **The claim graph** (`make_claim_graph.py`) is the *curated, adjudicated* layer — the 9 ⊥-face domain
  nodes, the hand-adjudicated inter-domain edges, and the free-standing keystones, drawn from the SSOT
  `claims` collection and status-coded (`proved`/`deep`/`corr`/`conj`/`commitment`). A `proved`/`deep`
  edge is drawn only because a sorry-free Lean declaration witnesses it — the store's cross-collection
  invariant refuses a witnessless proved/deep claim, so the map's colours cannot outrun the evidence.

## Scripts

- `web_data.py` — the shared extractor. `load()` returns the decl-derived web (nodes = domain faces of
  ⊥; edges = `bridge` / `core` / `no-go`; data-derived hubs). `load_claims()` returns the curated claim
  graph (domain nodes, adjudicated edges, keystones) with live sorry-free witness counts recomputed from
  the declarations. Handles BOTH export shapes — the legacy decl-only `{entries}` and the current
  multi-collection envelope `{collections: {declarations, claims}}` — so a republish never breaks the
  renderers. Run standalone to print the decl-graph summary.
- `make_web_diagram.py` — the ring map: ⊥ at the centre, domain faces on a ring, role-coded edges.
- `make_web_tree.py` — the tree/DAG view: domains (top) descend through the two hubs into ⊥ (bottom).
- `make_claim_graph.py` — the claim graph: ⊥ at the centre, the 9 domain nodes on a ring, status-coded
  adjudicated edges, plus a keystones panel. Reads the `claims` collection.

The gloss that prettifies each domain's label (e.g. valuation → "p-adic floor v₂(0)=∞") is the only
hand-written content; the *structure* (which nodes, which edges) is entirely registry-derived.

## Run

```
python tools/render/web_data.py                 # print the extracted decl-graph (nodes / edges / hubs)
python tools/render/make_web_diagram.py          # -> tools/render/the_web_honest_map.svg
python tools/render/make_web_tree.py             # -> tools/render/the_web_tree.svg
python tools/render/make_claim_graph.py          # -> tools/render/the_claim_graph.svg
```

Both accept an optional export path argument (defaults to `../../ssot.json`) and are
deterministic — the same export produces byte-identical SVGs. The generated `.svg` files are artifacts
(gitignored); re-run to regenerate against the current register. Pure standard-library Python, no deps.
