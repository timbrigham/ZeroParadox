# The NO-GO gauge on the attractor reading, and what the capstone does not claim

Argument, pre-registered gauge and scope for `ZeroParadox/Order/WellFoundedObstruct.lean`. The Lean
file holds the declarations, the Engineer's Take and the per-declaration commentary — the results are
described at each declaration, not listed again here.

## The question, and the complementary test it forms

This is the **complementary test to `ZeroParadox/Valuation/PadicAttractor.lean`**, refining **Axis I**
of the bottom-diagram tree (`.claude-local/notes/thread_obstruction_table_2026-06-29.md`).
`PadicAttractor.lean` gave node #3 (the p-adic floor `{0} ⊆ Q₂`) a genuine **dynamical attractor**
character: `0` is the global attractor of the doubling map `x ↦ 2·x`, because `‖2‖₂ = ½ < 1` makes the
map a strict contraction, so every orbit `2ⁿ·x` is an **infinite, non-terminating** sequence converging
to `0` *in the limit topology* — and (for `x ≠ 0`) it never actually reaches `0`. That is a ν-flavoured
(limit / contraction) character.

The question: does the **well-founded μ floor** (node #1 — the floor `0` of ℕ, base of the proof-theory
descent the framework uses for Goodstein / Kirby–Paris / Kruskal) carry the *same* attractor/contraction
character in its own ambient? If it did, the dynamical (ν) and well-founded (μ) characters would
collapse and the Axis-I cut between #1 and the ν-dynamical nodes #2/#3 would be undermined.

## The pre-registered gauge

**GO conjecture (the deflation side):** the well-founded floor admits descent maps that reach `0` from
every point, but every orbit hits `0` in **finitely many steps** and is then constant — there is no
infinite non-terminating orbit converging to `0` in `PadicAttractor.lean`'s sense, so the "attractor"
character is *vacuous* on the μ floor.

**NO-GO obstruction:** a genuine contraction/attractor with infinite non-terminating orbits converging
to `0`, matching `PadicAttractor.lean`'s topological `Tendsto`, IS constructible on the ℕ/Ordinal floor
— collapsing the μ/ν distinction.

**Verdict: GO.** The NO-GO is *refuted at the structural level*: well-foundedness of ℕ forbids the
infinite descending orbit that the contraction produces.

## Honest framing of the capstone

`floor_reach_separates_mu_nu` is, syntactically, a conjunction (`μ-side ∧ ν-side`). Its content is not
"two unrelated facts": both sides are stated under the *same* predicate `ReachesFloorInFiniteTime`, and
the in-statement contrast is sharpened from the weak "eventually 0 vs never 0" to the real dynamical
contrast — the ν side carries `PadicAttractor.lean`'s topological `Tendsto … (nhds 0)` *together with*
`¬ ReachesFloorInFiniteTime`, so the separation read in the statement is "reaches the floor in finite
time" (μ) vs "converges to the floor as a limit it never reaches" (ν). That `ReachesFloorInFiniteTime`
is *the* formalization of "attractor character" remains the framework reading, not a Lean claim.

## Honest scope — interpretation, NOT proved

"Attractor" and "contraction" remain the *framework reading*. The Lean file does not build a full
dynamical-systems contraction framework, nor does it prove that `ReachesFloorInFiniteTime` is the unique
formalization of "attractor character". What is proved in-statement is the concrete, single-definition
separation, with the ν side additionally carrying `PadicAttractor.lean`'s topological convergence. The
claim that this separation *is* the μ/ν cut of Axis I is the framework reading; the Lean proves the
separation under the stated predicate, with the well-foundedness obstruction in the proof term of the
μ side.

## Where the same question is asked in the other formal faces

The question *"can the floor be departed?"* is asked in more than one carrier, and the answers are not
interchangeable. A related question — *can the structureless referent ⊥ move?* — is formalized over a
single-valued **step function** at `ZeroParadox/Computability/Occurrence.lean`, over `f : σ → Option σ`,
where `machine_snap_impossible` and `deterministic_has_no_fanout` derive an **obstruction**: such a step
admits at most one successor, so nothing is both its own fixed point and departed from. That side and
this one formalize **approach to** a floor versus **departure from** one, and neither derives motion:
the step side derives the obstruction, this side takes the orbit as given. Both modes here run inward.

Prior art for both sides: Benedetto, *Non-Archimedean Dynamics in Dimension One* (2010), Def 4.1 p. 28
and Prop 4.3(a) p. 29, whose argument `|φⁿ(z)| = |λ|ⁿ·|z| → 0` is this side's; and Kahrs, *Infinitary
Rewriting: Foundations Revisited*, RTA 2010, where a step relation and a metric limit do live over one
carrier.
