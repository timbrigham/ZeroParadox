# Why Q₂ rather than a discrete two-point space

Argument for the modelling choice in `ZeroParadox/Valuation/Padic.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The three reasons

T0 fixes the representational base at p = 2. The full Q₂ structure (p-adic field,
ultrametric, clopen ball hierarchy) is not uniquely forced by AX-B1 alone — a
discrete two-point space {0, 1} would also satisfy the binary distinction. Q₂ is
chosen for three motivated reasons beyond the binary count:

- **Hierarchical approximation**: Q₂ contains nested clopen balls B(0, 2⁻ⁿ) ↘ {0}
  — a countably infinite depth hierarchy converging to 0 of Q₂. A two-point
  discrete space has no such hierarchy. This is the geometric substrate for ZPC's
  surprisal field (depth n ↦ n bits) and for L-INF (surprisal unbounded in depth).
- **Ultrametric geometry**: The strong triangle inequality (T1) and clopen ball
  structure (T2) give non-trivial topology — disjoint balls cannot be continuously
  connected (C2). Discrete spaces make this claim vacuous (no non-constant paths exist).
- **Irreversibility content**: C3 (no continuous path from x ≠ 0 to 0) uses the
  genuine total disconnectedness of Q₂ via the ultrametric; in a finite discrete
  space the argument carries no structural weight.

The formal connection from Q₂'s topology to ZPC's surprisal field and ZPD's basis
assignment is a design identification — those layers do not import ZPB as a Lean
dependency. The choice of Q₂ is a motivated modelling commitment, not a uniquely
forced consequence of AX-B1.
