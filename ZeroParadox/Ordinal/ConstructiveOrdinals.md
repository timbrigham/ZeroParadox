# ZP-N, the ε₀ snap on ordinal notations: the probe, the result and its fences

Ride-along documentation for [`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`](ConstructiveOrdinals.lean).
The Lean file holds the declarations, the Engineer's Take and a statement per declaration; this file holds
the probe, the result, its fences and the scope. Where the two would overlap, **the Lean is
authoritative**.

## The probe

The probe (`.claude-local/notes/choice_probe_ordinal_2026-06-15.md`) showed that ZP-L's
`Classical.choice` at ε₀ is *inherited* from Mathlib's classically-built `Ordinal` machinery — the order
instance and the operations, NOT the type, which measures `[propext, Quot.sound]` — but the
syntactic notation substrate (`ONote.cmp`) is choice-free (`propext`-only). ZP-N rebuilds the
snap-from-below **syntactically**, never touching `repr`/`Ordinal`, so the results are choice-free.

Key move: ω^x at the notation level is just `oadd x 1 0` (the CNF term with leading exponent x,
coefficient 1, remainder 0) — no general `opow` needed. ε₀ itself is NOT an `ONote` element (the
notations name exactly the ordinals < ε₀); ε₀ is their limit. So the snap threshold is characterised
*from below*: the ω-tower climbs without bound, and **no notation is a fixed point of ω^·** — the fixed
point (ε₀) is precisely what the notation system cannot reach.

## Result (proved, this build)

The snap-from-below is **choice-free**: `exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono` all
report `[propext]` only — no `Classical.choice` — in contrast to every ε₀ result in ZP-L (all carry
`Classical.choice`, inherited from Mathlib's `Ordinal` machinery). What that shows is narrow and worth
stating narrowly: **the snap's downward structure is constructive** (the ω-tower climbs without bound; no
notation is a fixed point of `ω^·`).

**It does NOT classify ZP-L's footprint as "representational, not intrinsic"** — an earlier version of
this paragraph said exactly that, and it is retracted (2026-07-19). That is an *eliminability* claim, and
it cannot be asked of those ε₀ results as stated: they are **STATEMENT-CARRIED**
(`ZeroParadox/Category/ChoiceCannotBe.md`). `epsilon0_ne_zero`, `epsilon0_ne_bot`, `epsilon0_eq_nfp_bot`
and `epsilon0_is_fixedpoint`, each only assumed in a theorem that proves `True`, already report
`Classical.choice` (statement control, measured 2026-10-08), so no re-proof of them can drop it. The open
question is a restatement on a carrier whose statements are choice-free, such as ZP-N's `ONote`: the
statements of `omegaPow_no_fixedpoint` and `tower_strictMono`, measured the same way, report `[propext]`
only. Two corrections belong with it:
`Ordinal` itself is `[propext, Quot.sound]` — **choice is not in the type**; it enters through
`Ordinal.instLinearOrder`, `nfp`, `omega0`, `epsilon`. And a choice-free result *about the ascent* is
suggestive for the ε₀ results without being a re-proof of them.

Side finding: `tower_NF` (well-formedness) *does* carry `Classical.choice` — because Mathlib's `NF`
predicate is defined through `repr` into `Ordinal`. The snap facts do not depend on `NF`, so they stay
choice-free; but even "this notation is well-formed" inherits choice in Mathlib — corroborating that
choice lives precisely at the syntax→semantics bridge.

## Scope

Scope: this is the snap *from below* (ε₀ is the unreachable fixed point). The matching *minimality*
("ε₀ is the LEAST fixed point") is the natural next target and is harder — it quantifies over the limit,
which no notation names.
