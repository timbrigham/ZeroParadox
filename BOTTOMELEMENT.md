# The Bottom Element (⊥) - Dictionary and Map

*A dictionary and map of the framework's bottom element ⊥ - what it is, what it is not, and where each characterization is established, most with a machine-checked Lean witness linked to the source.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For the formal framework index and Lean verification, see [README](README.md). For plain-language introductions, companions, and reading paths, see [GUIDE](GUIDE.md). For the claim-by-claim status of every result, see the [Claims Ledger](CLAIMS.md).

---

## What this is

This is a **reference** for the framework's bottom element ⊥: a **dictionary** (what ⊥ is and is not) and a
**map** (where each characterization is established). It is a **beginning, not a resolution.** What is
*proved* is that each construction's bottom belongs to the family and that the slot structure recurs; the
reading that the various bottoms are *one object* is retired as ill-typed - they are provably distinct as
structures (the "walls"). It closes a standing gap: a framework built on ⊥ that had not yet characterized ⊥ itself.

---

## The short version: concepts that should not coincide, but do

One self-referential structure - a thing that is its own fixed point - keeps turning up in fields that do not expect to meet. Here is each coincidence, ordered by how sure we are of it. Everything provable is checkable: clone the repo and run `#print axioms <name>`.

**Proved, with one commitment - the same element.** In any ZP lattice carrying an AFA structure, the *Quine atom* (a set that is its own only member, set theory / AFA), the *order-bottom* ⊥, and the *algebraic join-identity* are proved to be the **same element** - the three-name core, **axiom-free** ([`t_exec_triple_iff`](ZeroParadox/Settheory/SetTheoryAFA.lean)). The fourth name, the *Kleene fixed point* (a program that reproduces itself, computability), is *joined* to the other three by an explicit structural commitment: the [`KleeneStructure`](ZeroParadox/Computability/Kleene.lean) typeclass names the computational fixed point as the same role - the motivating commitment, not a derived theorem. So the set that is its own only member is identified with the program that prints itself by that commitment, not proved equal. The computational witness rests on Mathlib's recursion theorem, which carries `Classical.choice`; the three-name core needs none.

**Proved - each field's own floor.** 0 in the 2-adics, where v₂(0) = ∞ ([`padic_addVal_bot`](ZeroParadox/Valuation/ValuationAFA_Padic.lean)); unbounded surprisal, the state with no finite description ([`t2_diverges`](ZeroParadox/Information/Surprisal.lean)); the categorical bottom of each real Mathlib category, an inverse limit or initial object ([`fD_zero_isInitial`](ZeroParadox/State/HilbFunctor.lean), [`fC_zero_isInitial`](ZeroParadox/Multihomed/InfoFunctor.lean) and [`fB_bottom_is_limit`](ZeroParadox/Valuation/TopFunctor.lean), collected in [`mc1_correspondence`](ZeroParadox/Multihomed/MC1Bridge.lean)); and the case where the coincidence *fails*, ℝ vs ℚ₂ by Ostrowski ([`completions_exhaustive`](ZeroParadox/Valuation/Ostrowski.lean), [`real_not_equiv_padic`](ZeroParadox/Valuation/Ostrowski.lean)). They share a SHAPE (`Statement:` COINCIDENCE, per field's own witness above) - one object carrying both extremal characterisations at once - and a shared shape across distinct structures is a type boundary, never a common theorem. (The order-theoretic form of that shape is [`fork_collapse_iff`](ZeroParadox/Settheory/FixedPointFork.lean), choice-free, but none of these satisfies its hypotheses of a complete lattice and a monotone map, so none is an instance of it.) ε₀ is co-witnessed with the 2-adic limit and the machine snap ([`zpm_triangle`](ZeroParadox/Ordinal/Incompleteness.lean)).

**Mostly proved - a narrow residue argued.** The framework's set-theoretic *commitment* is not *AFA specifically* but a fragment it assumes of its host theory: a unique Quine atom ⊥ = {⊥}. That fragment is a checkable object, the [`QuineHost`](ZeroParadox/Settheory/QuineHost.lean) typeclass. Foundation-freeness is *forced* by the Quine atom ([`quineHost_not_wellFounded`](ZeroParadox/Settheory/QuineHost.lean), axiom-free - a self-loop cannot live in a well-founded world); ordinary set theory (Foundation) is excluded in-kernel about the real theory ([`zfSet_no_quine_bottom`](ZeroParadox/Settheory/QuineHost.lean) - no set is self-membered under Foundation); Boffa's axiom is set aside because it admits a proper class of Quine atoms rather than one (Boffa 1968), a gap a toy model makes concrete ([`boffa_fails_unique`](ZeroParadox/Settheory/QuineHost.lean)) rather than an in-kernel fact about Boffa's axiom; and AFA is exhibited as the example meeting all three ([`afaStructure_isQuineHost`](ZeroParadox/Settheory/QuineHost.lean)). What remains argued is only that a Quine atom and its uniqueness are the right two requirements - a Forced Metatheoretic Commitment with a named falsifier, stronger than a free choice and weaker than a theorem. The set-membership face ⊥ ∈ ⊥ stays metatheoretic; the structural fixed point is machine-checked and axiom-free ([`t_exec`](ZeroParadox/Settheory/SetTheoryAFA.lean)).

**The family - MC-1.** MC-1 names not one object but one **family**. Each of these floors is a member: it satisfies the shared criteria mapped in the slots below, with per-domain membership machine-verified where marked (the categorical criterion is carried by the per-domain witnesses [`fD_zero_isInitial`](ZeroParadox/State/HilbFunctor.lean), [`fC_zero_isInitial`](ZeroParadox/Multihomed/InfoFunctor.lean) and [`fB_bottom_is_limit`](ZeroParadox/Valuation/TopFunctor.lean), collected in [`mc1_correspondence`](ZeroParadox/Multihomed/MC1Bridge.lean)). The *choice* of criteria is a design principle; that they characterize the family is an argument. The cross-category numerical identity - that the bottoms are *one and the same object* - is **retired** as ill-typed (`x = y` across distinct categories is not a well-formed proposition), and the members are **distinct as structures**, proved pairwise wherever a wall has been built (below). What survives is the proved leaves and the proved walls; the only oneness is the shared self-referential *shape* - the diagonal fixed point - which lives in the apophatic register, never as a formal identity. Within-frame identities stand: the three-name core above ([`t_exec_triple_iff`](ZeroParadox/Settheory/SetTheoryAFA.lean), axiom-free), and in ℚ₂ the equality v₂(0) = ∞ ([`padic_addVal_bot`](ZeroParadox/Valuation/ValuationAFA_Padic.lean)) - an equality of *values* in the value monoid, not of points of ℚ₂. The 2-adic **pole** is a claim of a different kind: 0 and ∞ are provably distinct points of the sphere which inversion *exchanges* (`Statement:` INVERSION, [`point_and_field_at_the_poles`](ZeroParadox/Valuation/PoleCornersBridge.lean)), so calling the two one pole is a chart claim rather than an identity of points.

---

## Reading key (for a reader with no prior context)

**Slot codes** (the map columns, and the positive dictionary entries):

| code | what it means |
|---|---|
| CANT | **cannot-have** - what ⊥ provably is NOT (its exclusions) |
| NARR | **narrow** - ⊥ is a single, unique point |
| MEAS | **measure** - some quantity becomes infinite at ⊥, and in ℚ₂ exactly there |
| INV | **inversion** - the map z↦1/z swaps ⊥ (which is 0) with infinity (the two poles of a Riemann sphere) |
| CONC | **concurrency** - applying ⊥'s own operation returns ⊥ unchanged (a fixed point: operation and result coincide) |
| SELF | **self-reference** - ⊥ is defined by referring to itself (a self-reproducing / self-containing object) |
| GEN | **generation** - ⊥ generates the structure built above it (for example, the ordinal ε₀ generated from 0) |
| DYN | **dynamics** - how ⊥ is approached and departed, one directional axis with two sub-senses: **↓ inbound** (orbits converge *to* ⊥ - a sink) and **↑ outbound** (structure departs *from* ⊥ irreversibly - a source). ↕ = both, which happens only at a seam (μ=ν). Single-directional, set by whether ⊥ is a sink or a source |

**Constructions** (the map rows). A `#N` prefix (#2 Markov, #3 TopCat/p-adic limit, #4 Kleisli, #5 Hilbert
seam) cross-references the **bottom-diagram-tree nodes** used throughout the Lean source (`node #4`,
`seam node #5`, …). Only those four appear as numbered rows; the tree's order-floor node #1 is the abstract
`Lat ⊥` row (shown here without the number), and the other rows (Info, Kleene, ε₀, selfApp, the p-adic
valuation) come from other layers. The partial numbering is scoped, not missing data:

| construction (map row) | what it means |
|---|---|
| Lat ⊥ (ZPA/ZPE) | the abstract order bottom: ⊥ as the least element of the framework's lattice |
| p-adic (ℚ₂/ℤ₂) | the number 0 in the 2-adic numbers (the floor of the 2-adic distance) |
| Info (ZPC) | the information-theoretic bottom, where surprisal / information grows without bound |
| #4 Kleisli (Fin 0) | the empty type, as the initial object of a probability (Kleisli) category |
| #5 Hilbert (zero obj/seam) | the zero vector space, as the zero object of a linear category (the 'seam') |
| #3 TopCat ({0} limit) | the one-point space {0}, obtained as a topological limit of shrinking balls |
| #2 Markov (attractor) | the stationary distribution a random walk settles into |
| Kleene (quine, ZPK) | the self-reproducing program (Kleene fixed point) of computability |
| ε₀ (ordinal, ZPL/M) | the ordinal ε₀, generated from 0 by iterating omega-to-the-power |
| selfApp (abstract ⊥) | the abstract self-application ⊥: the unique fixed point of a self-map |

**A few recurring terms:**

| term | plain meaning |
|---|---|
| apophatic | characterizing something by what it is NOT (definition by exclusion) |
| μ / ν | least fixed point (μ, built up from the floor) vs greatest fixed point (ν, closed down) |
| Quine atom / Kleene quine | a self-containing set (x = {x}) / a program that prints itself |
| the snap | the framework's discrete jump off ⊥ into the first structured state |
| ε₀ | the fixed point of omega-to-the-power reached from 0 - both min and max at once (`Statement:` COINCIDENCE, [`epsilon0_min_eq_max`](ZeroParadox/Ordinal/Epsilon0MinMax.lean)): the least such fixed point (the minimum closure, a floor in the fixed-point order) and the supremum of the ascending tower (a ceiling) - never only a ceiling |
| v₂ → ∞ | the 2-adic valuation going to infinity at 0 (0 is infinitely divisible by 2) |

---

## Dictionary

### ⊥ cannot be (characterization by exclusion)

| ⊥ cannot be... | witness (links to Lean source) |
|---|---|
| a Lean term or otherwise finitely written down - this is the *apophatic* ⊥, the descriptionless limit-notion, distinct from the algebraic bottom element the Lean manipulates as a finite, decidable term. The two share the symbol ⊥, not an identity: any written form is a description, so it captures an interpretation of ⊥, never the descriptionless limit itself | *meta (no Lean witness)* |
| anything that keeps time, space, description, measure or structure (that would be an *interpretation* of ⊥, not ⊥) | *meta (no Lean witness)* |
| finite: ⊥ is by definition the point where every finite measure diverges to infinity | *meta (no Lean witness)* |
| the same object as both the proof-theory floor and the attractor floor (one is well-founded, the other is not) | [`no_strictMono_real_to_ordinal`](ZeroParadox/Multihomed/TreeObstructions.lean), [`simplex_antichain`](ZeroParadox/Multihomed/TreeObstructions.lean) |
| the same object as a categorical initial bottom, if it is a topological limit bottom (their universal properties point opposite ways) | [`padic_bottom_not_initial`](ZeroParadox/Multihomed/TreeObstructions.lean), [`split_kleisli_vs_hilbert`](ZeroParadox/Multihomed/TreeObstructions.lean) |
| reached by a comparison that preserves the 'closed-down' (ν) structure - you can only get to ⊥ by forgetting that structure | [`faithful_iff_descending`](ZeroParadox/Multihomed/WallSpanRobust.lean) |
| unified with its self-referential face in a structure-preserving way - the two coincide only as a bare point | [`faces_iso_unique`](ZeroParadox/Multihomed/TwoFacesBot.lean) |
| forced to a single point as a Markov bottom (#2): a reducible chain settles into a whole family of distributions, not one | [`markov_node_no_universal_property`](ZeroParadox/Computability/MarkovNuUniversal.lean) |
| an *initial* object of the category of spaces (the p-adic floor behaves like a limit / terminal object, the opposite) | [`padic_bottom_not_initial`](ZeroParadox/Multihomed/TreeObstructions.lean) |
| a *zero object* (both initial and terminal) of the Kleisli or p-adic categories | [`kleisli_bottom_not_zero`](ZeroParadox/Category/SeamUniqueness.lean), [`padic_bottom_not_zero`](ZeroParadox/Category/SeamUniqueness.lean) |
| a *greatest* element (it is the floor, not the top) | [`zpa_bot_not_greatest`](ZeroParadox/Category/SeamUniqueness.lean) |
| an inhabited least-fixed-point for the identity functor: that least fixed point is provably empty | [`strict_fix_isEmpty`](ZeroParadox/Computability/RootCutTrichotomy.lean), [`fix_isEmpty_constructive`](ZeroParadox/Computability/ChoicePurityInvariant.lean) |
| recovered by mapping the least fixed point onto the greatest: the comparison map is not onto | [`fixToCofix_not_surjective`](ZeroParadox/Computability/NatListRegime.lean) |
| reached by a non-contracting orbit: unit-norm and swap orbits provably do not converge to ⊥ | [`unit_orbit_not_tendsto_zero`](ZeroParadox/Valuation/ContractionRate.lean), [`swap_orbit_not_convergent`](ZeroParadox/Order/MarkovContractionDual.lean) |

### ⊥ is (positive handles - the slots)

The handles sort by **aspect**: what ⊥ *is* (**noun**), what ⊥ *does* (**verb**), or **both at once**
(**hinge**). The hinge is ⊥'s signature: at the floor the two collapse - the fixed point that *is* a thing
and *acts on itself* in one step (operation = result). *This noun-and-verb reading, and the claim that they
collapse at ⊥, is the framework's interpretation; the slot witnesses below are proved, the lens over them is
not.*

| slot | aspect | characterization of ⊥ | witness (links to Lean source) |
|---|---|---|---|
| narrow | noun | the single, unique pinned point | [`q2_unique_fp`](ZeroParadox/Computability/SelfApp.lean), [`fB_bottom_is_limit`](ZeroParadox/Valuation/TopFunctor.lean) |
| measure | noun | a quantity that becomes infinite at ⊥ - in ℚ₂ exactly there and nowhere else | [`t2_diverges`](ZeroParadox/Information/Surprisal.lean), [`padic_addVal_eq_top_iff`](ZeroParadox/Valuation/ValuationAFA_Padic.lean) |
| inversion | verb | `Statement:` INVERSION - the two poles, named the 0 = ∞ pole: the map z↦1/z EXCHANGES 0 and infinity, which leaves them distinct | [`rInv_swaps`](ZeroParadox/Valuation/RiemannSphere.lean), [`point_and_field_at_the_poles`](ZeroParadox/Valuation/PoleCornersBridge.lean) |
| concurrency | hinge | the fixed point where least and greatest coincide (operation = result) - `Statement:` COINCIDENCE | [`unique_fp`](ZeroParadox/Computability/SelfApp.lean) *(class field of AbstractSelfApp - assumed by the class, discharged by each instance)*, [`selfApp_bot_is_both_extremal`](ZeroParadox/Multihomed/SelfAppSeam.lean) |
| self-reference | hinge | the self-reproducing / self-containing fixed point (Quine / Kleene) | [`kleene_quine_is_bot`](ZeroParadox/Computability/Kleene.lean), [`quine_period_is_goedel`](ZeroParadox/Computability/Kleene.lean) |
| generation | verb | the floor generates the tower above it (ε₀ is the least fixed point of α ↦ ω^α seeded at the base, and equally that tower's supremum) | [`epsilon0_min_eq_max`](ZeroParadox/Ordinal/Epsilon0MinMax.lean), [`epsilonZero_eq_nfp`](ZeroParadox/Ordinal/Gentzen.lean) |
| dynamics | verb | ⊥'s one-way approach and departure - two sub-senses: **inbound** (↓, orbits converge *to* ⊥ - a sink) and **outbound** (↑, structure departs *from* ⊥ irreversibly - a source); ↕ = both, only at a seam (μ=ν) | [`contraction_orbit_tendsto_zero`](ZeroParadox/Valuation/ContractionRate.lean), [`t_snap_derived`](ZeroParadox/Order/Snap.lean), [`c3_irreversible`](ZeroParadox/Valuation/Padic.lean), [`fC_no_return`](ZeroParadox/Multihomed/InfoFunctor.lean) |

---

## Map - slot × construction

Where each characterization stands. Most columns are a **claim with a status**, not a checkbox: `✓` the witness states a proposition and the kernel checked it · `≝` **the cell's own sentence in *Why each cell* below says what the witness is** ·
`✗` refuted (a proved obstruction) · `∅` not-applicable by structure (a category
error - e.g. asking a ν-limit for a μ-generation property - not a gap). A trailing `*` (`✓*`, `≝*`, `↑*`, `↓*`) means conditional - established via a bridge or inherited from a sibling layer, a separate axis from `✓`/`≝`. The last column,
**dynamics**, is DIRECTIONAL instead: `↓` inbound (converges *to* ⊥ - a sink), `↑` outbound (departs *from* ⊥
irreversibly - a source), `↕` both (a seam). (The dictionary above links the witnesses it cites; each
map cell's own witness, or the reason it has none, is in *Why each cell* below.)

| construction | CANT | NARR | MEAS | INV | CONC | SELF | GEN | DYN |
|---|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| Lat ⊥ (ZPA/ZPE) | ✓ | ✓ | ∅ | ∅ | ✓* | ✓* | ∅ | ↑ |
| p-adic (ℚ₂/ℤ₂) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓* | ∅ | ↓ |
| Info (ZPC) | ✓* | ∅ | ✓ | ∅ | ∅ | ✓* | ∅ | ↑* |
| #4 Kleisli (Fin 0) | ✓ | ≝ | ∅ | ≝ | ∅ | ∅ | ✓ | ↑ |
| #5 Hilbert (zero obj/seam) | ✓ | ✓ | ∅ | ✓ | ✓ | ✓ | ∅ | ↕ |
| #3 TopCat ({0} limit) | ✓ | ≝ | ∅ | ∅ | ∅ | ∅ | ∅ | ↓* |
| #2 Markov (attractor) | ✓ | ✓* | ∅ | ∅ | ✓ | ∅ | ∅ | ↓ |
| Kleene (quine, ZPK) | ✓ | ✓ | ✓ | ∅ | ✓ | ✓ | ∅ | ↓ |
| ε₀ (ordinal, ZPL/M) | ✓* | ✓ | ✓ | ∅ | ✓ | ✓* | ✓ | ↕ |
| selfApp (abstract ⊥) | ✓ | ✓ | ∅ | ∅ | ≝ | ✓ | ∅ | ↑* |

The informative content is in the non-`✓` cells, and splitting them is the point: a `∅`
is a settled structural fact (a category error, not a gap), a `✗` is news (a proved obstruction), a `✓*` holds only via a bridge, and a `≝` sends you to that cell's sentence. Two things worth reading off the table:
(1) **generation** (GEN) is the μ / build-up-from-the-floor side, so the ν-bottoms (p-adic, Markov, the TopCat
point-limit) read `∅` there - a ν-object has no μ-property - and the self-coincident fixed points (Kleene,
selfApp) carry SELF rather than GEN; the live GEN cells are the ones marked in the column above, and ε₀ is the one this section turns on, where the floor generates the tower above it - and ε₀ is both that tower's supremum and its least fixed point, never only the top.
(2) The **dynamics** column is single-directional - `↓` for a sink (ν), `↑` for a source (μ) - and `↕` (both)
appears *only* at a seam (μ=ν): the zero-object seam **#5 Hilbert**, and **ε₀**, whose row is itself the snap-arc
0→ε₀. So ⊥'s dynamics has one direction, fixed by whether ⊥ is a source or a sink.

**The structural reading is in the non-`✓` cells** - the proved obstructions (`✗`), the structural non-applicabilities (`∅`), the `✓*` cells that are conditional, and the `≝` cells, whose witness is named in its own sentence - not the filled count. The reason or witness behind *every* mark is below.

### Why the cell vocabulary has states rather than a checkbox

A relationship between a construction and an aspect is a **claim with a status**, not a yes/no box. A blank
would conflate three different situations - an open question, a settled structural non-applicability, and a
proved impossibility - so the matrix distinguishes them. These are the states actually in use, with their live
counts:

- **✓ established** (30) - a sorry-free Lean witness.
- **∅ n/a, structural** (28) - not a gap: either a category error (a ν-object asked for a μ-property; a bare order asked for a metric), or the property holds only DEGENERATELY and carries no content about this bottom.
- **✓* conditional** (8) - holds under a modelling commitment or bridge, or is cited from a library.
- **≝ definitional** (4) - the witness is a `def` whose type is not a proposition, because an initiality witness must CARRY the mediating morphism. ⚠ An established result, never a weaker one.

### The one axis behind two columns: μ and ν

Every fixed point of a construction sits on a fork. **μ** is the *least* fixed point, built **up from** ⊥ -
the initial-object / colimit / generation side. **ν** is the *greatest*, closed **down to** ⊥ - the
terminal-object / limit / attractor side. A construction's bottom is a **source** (μ), a **sink** (ν), or,
where the two coincide, a **seam** (μ = ν). `GEN` and `dynamics` are not independent slots: they are two
readings of that single polarity.

**GEN is the μ face.** Its precise content is the least-fixed-point-by-iteration schema `lfp F = ⊔ₙ Fⁿ(⊥)` -
iterate the operator from the floor and take the supremum - which is **Kleene's fixed-point theorem**, the
founding construction of domain theory. It appears at three levels: order-theoretic, as Mathlib's
`fixedPoints.lfp_eq_sSup_iterate`, cited rather than rebuilt (⚠ the ω-Scott-continuity hypothesis is the whole
content and must not be softened to monotonicity - a bundled `F : α →o α` is monotone already, and monotone
alone gives only Knaster-Tarski's *existence* somewhere, where continuity is what buys the ω-indexed formula,
that ω steps suffice); ordinal, as `ε₀ = nfp(ω^·)(0) = ⊔ₙ (ω^·)ⁿ(0)`; and categorical, as Adámek's initial
algebra as the colimit of `0 → F0 → F²0 → …`. The categorical form was not located in Mathlib as of
2026-08-08, searched along three axes (the proper name; the nouns *initial algebra* / *terminal coalgebra*, both
polarities; and the verb *transfinite*), so the matrix builds a concrete instance instead: `node4_generates_nat`
makes ℕ the colimit of the successor chain rooted at the empty type, the initial algebra of `X ↦ X + 1`,
choice-free.

**So `GEN` is a μ-only column, and its emptiness elsewhere is the fork showing through rather than missing
work.** The ν-bottoms - the p-adic inverse limit, the Markov attractor, the topological `{0}`-limit - are the
opposite pole: they are *reached*, they do not *generate*. And the self-coincident fixed points are their own
fixed point, so there is no distinct level above to generate; they carry `SELF` and `CONC`, the still point.

**Dynamics is single-directional, set by the same polarity.** `↓` inbound means orbits converge *to* ⊥, a
sink (ν); `↑` outbound means structure departs *from* ⊥ irreversibly, a source (μ); `↕` means both, which
happens only at a seam. ⚠ **The implication runs one way: a seam gives `↕`, and `↕` does not by itself give a
seam** - ε₀ shows `↕` for a different reason, because its row *is* the transition arc, spanning a floor and a
level above rather than sitting at one point.

**The correction that reading forced.** Two constructions, p-adic and Markov, *looked* two-directional because
two irreversibility theorems sat in the outbound column and do not belong there. `c3_irreversible` says there is
no continuous path *to* 0 - that is the **arrival** being a discontinuous jump, an inbound fact.
`fullMix_not_injective` says mixing *toward* the stationary state loses information - again inbound. Re-sorted,
both are pure sinks, and `↕` becomes a seam diagnostic. The reach-in / cannot-return-out asymmetry is ⊥'s
one-way irreversibility: you can reach ⊥, and the snap off it does not reverse. (Physics calls one-wayness an
arrow of time; the framework is inspired by the analogy and claims nothing about physics - the irreversibility
lemmas are the statements, the analogy is not one.)

<details>
<summary><b>Why each cell</b> - the reason or witness behind every mark (click to expand)</summary>

**Lat ⊥ (ZPA/ZPE)**
- `CANT` ✓ - [`zpa_bot_not_greatest`](ZeroParadox/Category/SeamUniqueness.lean)
- `NARR` ✓ - [`da2_bottom_characterization`](ZeroParadox/Order/Snap.lean)
- `MEAS` ∅ - bare [`ZPSemilattice`](ZeroParadox/Order/Lattice.lean) has no metric/valuation scalar to diverge
- `INV` ∅ - [`ZPSemilattice`](ZeroParadox/Order/Lattice.lean) states no INVOLUTION and no ∞-counterpart, so there is nothing for z↦1/z to swap ⊥ WITH. ⚠ NOT that no member has a top: `[`trivialZPSemilattice`](ZeroParadox/Valuation/Scale.lean) : [`ZPSemilattice`](ZeroParadox/Order/Lattice.lean) Unit` has ⊥=⊤ - the earlier reason said so and was refuted 2026-08-29 by the corpus's own standing control. ⚠ An earlier draft of THIS text also cited Bool, which is not a `[`ZPSemilattice`](ZeroParadox/Order/Lattice.lean)` member at all
- `CONC` ✓* - [`selfApp_bot_is_both_extremal`](ZeroParadox/Multihomed/SelfAppSeam.lean)
- `SELF` ✓* - [`derived_bot_self_mem`](ZeroParadox/Computability/SelfApp.lean)
- `GEN` ∅ - [`ZPSemilattice`](ZeroParadox/Order/Lattice.lean) STATES no infinite joins, so ⊔ₙfⁿ(⊥) is not expressible from the class alone; ε₀-generation lives in the ordinal row. ⚠ NOT that no member has them: ``CompleteLattice` Unit` exists and `[`trivialZPSemilattice`](ZeroParadox/Valuation/Scale.lean)` is a member - the class/member slip corrected in the INV cell above, swept here 2026-08-29
- `DYN` ↑ - [`t_snap_derived`](ZeroParadox/Order/Snap.lean) (⊥=c₀ departs to c₁ - source/μ)

**p-adic (ℚ₂/ℤ₂)**
- `CANT` ✓ - [`padic_bottom_not_initial`](ZeroParadox/Multihomed/TreeObstructions.lean)
- `NARR` ✓ - [`fB_bottom_is_limit`](ZeroParadox/Valuation/TopFunctor.lean)
- `MEAS` ✓ - [`addVal_bot`](ZeroParadox/Valuation/FloorWitness.lean)
- `INV` ✓ - [`rInv_swaps`](ZeroParadox/Valuation/RiemannSphere.lean) (Riemann sphere 0↔∞)
- `CONC` ✓ - [`q2_zero_is_fixed`](ZeroParadox/Computability/SelfApp.lean)
- `SELF` ✓* - [`valuation_bot_is_quine`](ZeroParadox/Valuation/ValuationAFA.lean)
- `GEN` ∅ - ν-limit (inverse limit of balls) - carries inbound dynamics, not GEN (μ/ν fork)
- `DYN` ↓ - [`contraction_orbit_tendsto_zero`](ZeroParadox/Valuation/ContractionRate.lean) (converge) + [`c3_irreversible`](ZeroParadox/Valuation/Padic.lean) (arrival is a jump) - sink/ν

**Info (ZPC)**
- `CANT` ✓* - [`description_instantiation_gap_closed`](ZeroParadox/Computability/Kleene.lean)
- `NARR` ∅ - the info bottom is the n→∞ surprisal limit, not a pinned carrier point
- `MEAS` ✓ - [`t2_diverges`](ZeroParadox/Information/Surprisal.lean)
- `INV` ∅ - −log prob↔info is a coordinate change, not a ⊥↔∞ involution
- `CONC` ∅ - no self-application operation on surprisal / distributions
- `SELF` ✓* - [`da1_closed_concrete`](ZeroParadox/Computability/Kleene.lean)
- `GEN` ∅ - unbounded ascent, with no distinct level above it constructed - GEN asks the floor to generate the tower over it, and nothing here builds one
- `DYN` ↑* - [`t_snap_derived`](ZeroParadox/Order/Snap.lean) (snap off the machine null c₀; ZP-E bridge)

**#4 Kleisli (Fin 0)**
- `CANT` ✓ - [`kleisli_bottom_not_zero`](ZeroParadox/Category/SeamUniqueness.lean)
- `NARR` ≝ - [`fC_zero_isInitial`](ZeroParadox/Multihomed/InfoFunctor.lean) *(a `def`, and its type is not a proposition)*
- `MEAS` ∅ - the empty type carries no distribution at all, so no scalar exists to diverge. ⚠ ``IsEmpty` (PMF (Fin 0))` elaborates, so the stronger mark - a proved obstruction (✗) rather than a category error - is AVAILABLE and unbuilt as of 2026-08-29. Upgrading it costs one theorem; the mark stays ∅ until that theorem exists, because a cell may not cite a witness the corpus does not contain
- `INV` ≝ - `IsInitial.op` *(a `def`, and its type is not a proposition)* (Mathlib)
- `CONC` ∅ - DEGENERATE on an empty carrier - there are no points, so every endomorphism fixes every point vacuously and CONC carries no content here. ⚠ This cell previously cited `[`kleisli_bottom_not_zero`](ZeroParadox/Category/SeamUniqueness.lean)` as a refutation; that theorem proves the Kleisli bottom is not a ZERO OBJECT (not terminal), which is a mu/nu DIRECTION fact and belongs to DYN. It addresses neither of CONC's two propositions
- `SELF` ∅ - DEGENERATE, and that is the finding. `Fin 0` is EMPTY, so the Kleisli endomorphism `Fin 0 -> PMF (Fin 0)` is the unique empty map and every diagonal/self-application statement about it holds VACUOUSLY, carrying no content about this bottom. ⚠ Not that no self-map exists - the same correction the `TopCat` cells took 2026-08-29. No ZP witness is cited because none is owed for a degeneracy
- `GEN` ✓ - [`node4_generates_nat`](ZeroParadox/Category/Node4Generation.lean)
- `DYN` ↑ - [`fC_no_return`](ZeroParadox/Multihomed/InfoFunctor.lean) (initial source; nothing returns to ⊥ - μ)

**#5 Hilbert (zero obj/seam)**
- `CANT` ✓ - [`seam_not_mu_colimit_apex`](ZeroParadox/Category/SeamNotColimit.lean)
- `NARR` ✓ - [`hilbert_bottom_isZero`](ZeroParadox/Category/TreeSeam.lean)
- `MEAS` ∅ - the zero space has finrank 0 - every attached scalar is 0/finite
- `INV` ✓ - `hasZeroObject_op` *(an `instance`, and its type is a proposition - so a proof)* (Mathlib)
- `CONC` ✓ - [`seam_is_mu_nu_coincidence_SeamCoincidence`](ZeroParadox/Category/SeamCoincidence.lean)
- `SELF` ✓ - [`biprod_diagonal_only_zero`](ZeroParadox/Multihomed/HilbertDiagonal.lean) (self-similarity)
- `GEN` ∅ - μ=ν self-coincident (seam⊔seam≅seam) - it generates no level distinct from itself
- `DYN` ↕ - [`seam_has_Pin`](ZeroParadox/Category/SeamArrowSignature.lean) (terminal: maps in) ; [`hilbert_bottom_isZero`](ZeroParadox/Category/TreeSeam.lean).isInitial (maps out) - the SEAM (μ=ν)

**#3 TopCat ({0} limit)**
- `CANT` ✓ - [`padic_bottom_not_initial`](ZeroParadox/Multihomed/TreeObstructions.lean)
- `NARR` ≝ - [`floorConeIsLimit`](ZeroParadox/Order/PadicLimitCone.lean) *(a `def`, and its type is not a proposition)*
- `MEAS` ∅ - `TopCat` forgets the scalar; divergence-at-⊥ is the p-adic/info sibling
- `INV` ∅ - `TopCat` forgets field mult; z↦1/z is the ℚ₂ Riemann sibling
- `CONC` ∅ - DEGENERATE, and that is the finding. The cone apex is a SUBSINGLETON, so ``ContinuousMap`.id` is an intrinsic self-map and EVERY self-map fixes every point - CONC holds VACUOUSLY, carrying no content about this bottom. ⚠ The earlier reason claimed no self-map exists; that was refuted by compilation 2026-08-29. No ZP witness is cited because none is owed for a degeneracy
- `SELF` ∅ - SELF asks for a DIAGONAL (a self-application whose fixed point is the object), which the limit object does not carry. ⚠ Not that it has no self-map at all - the apex is a subsingleton and ``ContinuousMap`.id` is one; that degeneracy is recorded under CONC
- `GEN` ∅ - ν-limit ({0} as a topological limit) - carries inbound dynamics, not GEN (μ/ν fork)
- `DYN` ↓* - [`c3_irreversible`](ZeroParadox/Valuation/Padic.lean) (topological no-return; stated on ambient Q₂) - sink/ν

**#2 Markov (attractor)**
- `CANT` ✓ - [`markov_node_no_universal_property`](ZeroParadox/Computability/MarkovNuUniversal.lean)
- `NARR` ✓* - [`markov_node_irreducible_rescue`](ZeroParadox/Computability/StationaryUnique.lean)
- `MEAS` ∅ - a probability distribution - no finite value diverges at it
- `INV` ∅ - the simplex carries no 0↔∞ POLE for an inversion to swap, which is what INV asks. ⚠ NOT that no involution exists: `PMF.map (Equiv.swap 0 1)` on `PMF (Fin 2)` is one, exchanging the vertices - compiled 2026-08-29, refuting the earlier wording
- `CONC` ✓ - [`exists_stationary`](ZeroParadox/Reals/PerronFrobenius.lean)
- `SELF` ∅ - no self-application; its fixed point is CONC, no self-similarity
- `GEN` ∅ - ν-attractor - carries inbound dynamics, not GEN (μ/ν fork)
- `DYN` ↓ - [`doubly_stochastic_mean_ergodic`](ZeroParadox/State/MeanErgodic.lean) (converge) + [`fullMix_not_injective`](ZeroParadox/Reals/MarkovSpectralGap.lean) (mixing is lossy) - sink/ν

**Kleene (quine, ZPK)**
- `CANT` ✓ - [`self_halting_undecidable`](ZeroParadox/Computability/Kleene.lean)
- `NARR` ✓ - [`kleene_quine_is_bot`](ZeroParadox/Computability/Kleene.lean)
- `MEAS` ✓ - [`infinite_quine_family`](ZeroParadox/Computability/Kleene.lean)
- `INV` ∅ - programs carry no ∞-counterpart for an inversion to swap the bottom WITH. ⚠ NOT that no involution exists - `Equiv.swap` on two distinct codes is one, compiled 2026-08-29. Narrowed to the half that stands, matching the Markov INV correction
- `CONC` ✓ - [`computational_quine_exists`](ZeroParadox/Computability/Kleene.lean)
- `SELF` ✓ - [`quine_period_is_goedel`](ZeroParadox/Computability/Kleene.lean)
- `GEN` ∅ - self-coincident fixed point (⊥ = the quine itself) - carries SELF, not floor-generates-tower
- `DYN` ↓ - [`quine_encodings_approach_bot`](ZeroParadox/Multihomed/PadicBridge.lean) (encodings approach ⊥; a static point)

**ε₀ (ordinal, ZPL/M)**
- `CANT` ✓* - [`kruskal_is_wqo_not_descent`](ZeroParadox/Ordinal/ProofFloorCanonical.lean)
- `NARR` ✓ - [`epsilonZero_le_fixedPoint`](ZeroParadox/Ordinal/Gentzen.lean)
- `MEAS` ✓ - [`cnfToZp2_valuation_unbounded`](ZeroParadox/Ordinal/Gentzen.lean)
- `INV` ∅ - a well-order has a floor but no ∞-pole / order-reversing z↦1/z
- `CONC` ✓ - [`epsilonZero_fixedPoint`](ZeroParadox/Ordinal/Gentzen.lean)
- `SELF` ✓* - [`both_fixed_points_exist`](ZeroParadox/Ordinal/Incompleteness.lean)
- `GEN` ✓ - [`epsilonZero_eq_nfp`](ZeroParadox/Ordinal/Gentzen.lean)
- `DYN` ↕ - [`tower_converges_to_zero`](ZeroParadox/Ordinal/Gentzen.lean) (floor 0) ; [`snap_exactly_at_epsilon_zero`](ZeroParadox/Ordinal/Gentzen.lean) (the level above, ε₀) - the snap-ARC

**selfApp (abstract ⊥)**
- `CANT` ✓ - [`scale_ne_fixed`](ZeroParadox/Valuation/Scale.lean)
- `NARR` ✓ - [`selfApp_fp_set_eq_singleton`](ZeroParadox/Multihomed/SelfAppForkPlace.lean)
- `MEAS` ∅ - [`AbstractSelfApp`](ZeroParadox/Computability/SelfApp.lean) abstracts away valuation (ℚ₂ deliberately not an instance)
- `INV` ∅ - no ∞-pole; qua μ=ν seam the point is the inversion-FIXED centre
- `CONC` ≝ - [`unique_fp`](ZeroParadox/Computability/SelfApp.lean) *(class field of [`AbstractSelfApp`](ZeroParadox/Computability/SelfApp.lean) - assumed by the class, discharged by each instance)*
- `SELF` ✓ - [`derived_bot_self_mem`](ZeroParadox/Computability/SelfApp.lean)
- `GEN` ∅ - self-coincident (μ=ν seam, ⊥ = the least fixed point) - carries SELF/CONC, not GEN
- `DYN` ↑* - [`t_snap_derived`](ZeroParadox/Order/Snap.lean) (inherited; the static seam-point does not itself move)

</details>

---

## The diagonal family - the self-reference arguments as one fixed point

The classical self-reference arguments are not separate theorems that happen to rhyme; they are one diagonal fixed point seen under different conditions (Lawvere 1969; Yanofsky 2003). The framework maps the full roster against ⊥, organized by the μ/ν fork and built off a single engine - [`negation_no_fixedpoint`](ZeroParadox/Settheory/Wall.lean) / [`lawvere_fixedpoint`](ZeroParadox/Settheory/Wall.lean), both axiom-free. On the **wall** side (μ) self-reference cannot close: the argument runs as a proof that no reflexive object exists. On the **floor** side (ν) it does close - the fixed point is genuinely produced, and lands at ⊥. Cantor, Russell, Turing, Tarski, Curry, Löb, and Gödel's second incompleteness are all **axiom-free**; only the two computability floor faces (the Kleene quine and Rice's exists-but-undecidable) carry `Classical.choice`, inherited from Mathlib's recursion theory. This roster is ZP-R (the Cross-Category Fixed Point layer and its Diagonal Family Addendum) - a *placement* of ⊥ among recognized results, not a new theorem; the cross-face identity stays a type boundary, the same walls the map above records.

**See it:** the interactive [Diagonal Family](diagonal-family.html) map renders this roster as one engine forking into walls (μ) and floors (ν), each node linking its Lean witness and axiom footprint.

| face | side | what it says | witness | axioms |
|---|---|---|---|---|
| Cantor | μ wall | no surjection onto its own power set - the reflexive object is refuted | [`cantor_via_engine`](ZeroParadox/Settheory/Wall.lean) | (none) |
| Russell | μ wall | membership is not surjective - no set of all non-self-membered sets | [`russell_via_engine`](ZeroParadox/Settheory/Wall.lean) | (none) |
| Turing | μ wall | no machine decides its own halting - no self-decider | [`no_self_decider`](ZeroParadox/Settheory/Wall.lean) | (none) |
| Tarski | μ wall | no internal truth predicate - the liar sentence has no witness | [`tarski_no_internal_truth`](ZeroParadox/Settheory/Tarski.lean) | (none) |
| Curry | μ wall | no naming surjection - Curry's paradox forces any conclusion | [`curry_no_bottom`](ZeroParadox/Settheory/Curry.lean) | (none) |
| the wall | μ | no well-founded relation admits a self-loop (the engine's floor) | [`wf_no_selfloop`](ZeroParadox/Settheory/Wall.lean) | (none) |
| Gödel 1st | between | the undecidable diagonal sentence, built by the shared engine | [`lawvere_fixedpoint`](ZeroParadox/Settheory/Wall.lean) | (none) |
| Quine atom | ν floor | the self-containing set ⊥ = {⊥} - executable self-reference, landing at ⊥ | [`t_exec`](ZeroParadox/Settheory/SetTheoryAFA.lean) | (none) |
| Löb | ν floor | provability of (□A → A) yields A - the provability-logic fixed point | [`loeb`](ZeroParadox/Settheory/Loeb.lean) | (none) |
| Gödel 2nd | ν floor | no consistent system proves its own consistency | [`godel_two`](ZeroParadox/Settheory/Loeb.lean) | (none) |
| Kleene quine | ν floor | a program that reproduces itself - the recursion theorem fires | [`computability_face_fixedPoint`](ZeroParadox/Category/Lawvere.lean) | `[propext, Classical.choice, Quot.sound]` |
| Rice | ν floor | the fixed point provably exists, yet its membership is undecidable | [`rice_face_has_bottom`](ZeroParadox/Computability/Rice.lean) | `[propext, Classical.choice, Quot.sound]` |

---

*Generated from `bottom_cannot_be.md` and the matrix data by `build_dictionary_map.py`. Witness names are
resolved against the Lean source at generation time and link to the file that declares them; the `meta`
entries (marked as such) have no Lean witness. To update: edit a source and rerun. The links render
natively on GitHub.*
