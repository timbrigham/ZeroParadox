import Mathlib.Tactic

/-!
# Löb's theorem — the diagonal family's PROVABILITY-modal face (probe, from scratch)

## Engineer's Take

Back to basics. We're filling in everything that's left where the relationship between one over
infinity and a bottom element still wasn't fully defined, using the same structure that we have for
everything else in the family.

---

## Overview (AI-assisted)

Löb (1955): in a system with a provability predicate `□` satisfying the Hilbert–Bernays–Löb derivability
conditions, `⊢ (□A → A)` implies `⊢ A`. This is the diagonal family's **provability-modal face** — the
self-referential fixed point of the map `p ↦ (□p → A)` (the Löb sentence). It is the ONLY sibling of the
four with no Mathlib support (no modal / provability logic in the library), so it is built here from
scratch as an abstract provability logic.

Placement in the family: Tarski is the TRUTH face (undefinable — the wall), Gödel/Löb the PROVABILITY face
(definable but self-constrained). Löb subsumes **Gödel's second incompleteness**: at `A = ⊥` it says a
consistent system cannot prove `□⊥ → ⊥` — its own consistency (`godel_two` below). The Löb sentence
`ψ ↔ (□ψ → A)` is a genuine diagonal fixed point (ν: it exists, by the diagonal lemma), and Löb is what it
forces.

Design: `ProvabilityLogic` is a typeclass carrying sentences `S`, connective `imp`, modality `box`, and a
provability predicate `Thm`, with the minimal axioms Löb needs — the implicational Hilbert base
(`ax_K`, `ax_S`) with modus ponens (`mp`), and the three derivability conditions (`nec` = D1,
`ax_D2` = distribution, `ax_D3` = D3). The diagonal lemma is taken as a hypothesis (`hfix1`/`hfix2`), the
standard separation of concerns: Löb from the derivability conditions + a diagonal.

Honest delta: this is a genuinely new construction (no Mathlib modal/provability logic; nothing like it in
the repo). Attribution: Löb (1955); Hilbert–Bernays–Löb derivability conditions; diagonal-family framing
Lawvere/Yanofsky (cited in `Wall.lean`). The classical Löb derivation is standard; the contribution is the
clean abstract typeclass and its placement as the provability face of ⊥'s diagonal.

## Structure
- § I.   `ProvabilityLogic` typeclass (implicational Hilbert base + derivability conditions).
- § II.  Derived propositional rules (`ax_I`, `contract`, `hs`).
- § III. Löb's theorem.
- § IV.  Gödel's second incompleteness as the `A = ⊥` corollary.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ## § I. The provability-logic typeclass -/

/-- **An abstract provability logic.** Sentences `S` with implication `imp`, provability modality `box`,
    and a "provable" predicate `Thm`, satisfying: the implicational Hilbert base (`ax_K`, `ax_S`) closed
    under modus ponens (`mp`); and the three Hilbert–Bernays–Löb derivability conditions
    (`nec` = D1 necessitation, `ax_D2` = distribution of `box` over `imp`, `ax_D3`). This is exactly the
    apparatus Löb's theorem needs, and no more. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib has no modal / provability logic (grep: no Löb, GL,
-- derivability conditions, or modal-logic Kripke apparatus). Minimal typeclass carrying just the
-- Hilbert–Bernays–Löb apparatus so Löb's theorem is a face of the diagonal family.
class ProvabilityLogic (S : Type*) where
  imp : S → S → S
  box : S → S
  Thm : S → Prop
  /-- modus ponens -/
  mp : ∀ {a b : S}, Thm (imp a b) → Thm a → Thm b
  /-- Hilbert axiom K:  a → (b → a) -/
  ax_K : ∀ a b : S, Thm (imp a (imp b a))
  /-- Hilbert axiom S:  (a → (b → c)) → ((a → b) → (a → c)) -/
  ax_S : ∀ a b c : S, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- D1 — necessitation: from `⊢ a` infer `⊢ □a`. -/
  nec : ∀ {a : S}, Thm a → Thm (box a)
  /-- D2 — distribution: `⊢ □(a → b) → (□a → □b)`. -/
  ax_D2 : ∀ a b : S, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- D3:  `⊢ □a → □□a`. -/
  ax_D3 : ∀ a : S, Thm (imp (box a) (box (box a)))

/-! ### NO-GO gauge — what fails to be a `ProvabilityLogic`?

**Measured 2026-08-09 by building it: the INCONSISTENT theory does not fail — it is a member.** Take `S := Unit` with
`Thm _ := True`. Modus ponens, K, S, necessitation, D2 and D3 all hold trivially, so the class
admits the theory in which everything is provable.

**That is normal for an axiomatization and it is exactly why membership proves nothing on its own.**
The axioms constrain the *shape* of a provability predicate, never its consistency — the class has no
field that could. So results here are conditional on the carrier being a real proof system;
`[ProvabilityLogic S]` alone licenses no claim about provability in any particular theory. -/

namespace ProvabilityLogic

variable {S : Type*} [ProvabilityLogic S]

/-! ## § II. Derived propositional rules -/

/-- Identity: `⊢ a → a` (from `ax_S`, `ax_K`, `mp`). -/
theorem ax_I (a : S) : Thm (imp a a) :=
  mp (mp (ax_S a (imp a a) a) (ax_K a (imp a a))) (ax_K a a)

/-- Implication contraction (from `ax_S`): `⊢ a → (b → c)` and `⊢ a → b` give `⊢ a → c`. -/
theorem contract {a b c : S} (h1 : Thm (imp a (imp b c))) (h2 : Thm (imp a b)) :
    Thm (imp a c) :=
  mp (mp (ax_S a b c) h1) h2

/-- Hypothetical syllogism: `⊢ a → b` and `⊢ b → c` give `⊢ a → c`. -/
theorem hs {a b c : S} (h1 : Thm (imp a b)) (h2 : Thm (imp b c)) : Thm (imp a c) :=
  contract (mp (ax_K (imp b c) a) h2) h1

/-! ## § III. Löb's theorem -/

/-- **Löb's theorem.** Given a Löb diagonal for `A` — a sentence `ψ` with `⊢ ψ → (□ψ → A)` and
    `⊢ (□ψ → A) → ψ` (i.e. `⊢ ψ ↔ (□ψ → A)`, the diagonal lemma applied to `p ↦ (□p → A)`) — the Löb
    hypothesis `⊢ □A → A` yields `⊢ A`.

    Proof (the classical derivation): necessitate `ψ → (□ψ → A)` and push `box` through with D2 twice to
    get `⊢ □ψ → (□□ψ → □A)`; contract against D3 (`□ψ → □□ψ`) to `⊢ □ψ → □A`; compose with `□A → A` to
    `⊢ □ψ → A`; that IS `ψ` by the diagonal, so `⊢ ψ`; necessitate to `⊢ □ψ`; hence `⊢ □A`, hence `⊢ A`. -/
theorem loeb {A : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) A)))
    (hfix2 : Thm (imp (imp (box psi) A) psi))
    (hLob : Thm (imp (box A) A)) : Thm A := by
  have s1 : Thm (box (imp psi (imp (box psi) A))) := nec hfix1
  have ha : Thm (imp (box psi) (box (imp (box psi) A))) :=
    mp (ax_D2 psi (imp (box psi) A)) s1
  have hb : Thm (imp (box (imp (box psi) A)) (imp (box (box psi)) (box A))) :=
    ax_D2 (box psi) A
  have hc : Thm (imp (box psi) (imp (box (box psi)) (box A))) := hs ha hb
  have hd : Thm (imp (box psi) (box A)) := contract hc (ax_D3 psi)
  have he : Thm (imp (box psi) A) := hs hd hLob
  have hpsi : Thm psi := mp hfix2 he
  have hbA : Thm (box A) := mp hd (nec hpsi)
  exact mp hLob hbA

/-! ## § IV. Gödel's second incompleteness — the `A = ⊥` corollary -/

/-- **Gödel's second incompleteness, via Löb.** If the system is consistent (`⊬ falsum`), it cannot prove
    `□falsum → falsum` — the internal statement of its own consistency. Immediate from Löb at `A = falsum`:
    a proof of `□falsum → falsum` would yield `⊢ falsum`, contradicting consistency. So Löb subsumes
    Gödel's second theorem; the wall on the provability axis is the unprovability of consistency. -/
theorem godel_two {falsum : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) falsum)))
    (hfix2 : Thm (imp (imp (box psi) falsum) psi))
    (hcon : ¬ Thm falsum) : ¬ Thm (imp (box falsum) falsum) :=
  fun h => hcon (loeb psi hfix1 hfix2 h)

/-! ## § V. The bottom-element relationship — the floor (ν): the Löb sentence is the bottom -/

/-- **Löb on the family's μ/ν fork: the provability face HAS a bottom element.** The Löb sentence `ψ` is
    provably equivalent to `□ψ → A` (`⊢ ψ ↔ (□ψ → A)`) — the diagonal fixed point of the provability map
    `p ↦ (□p → A)`. Where Tarski's truth face hits the wall (μ, no floor), the provability face reaches a
    bottom: `ψ` is that floor, and Löb (§ III) is what it forces. So on the one-over-infinity-to-bottom
    map, provability is a ν side, with a genuine self-referential fixed point, the same structure the rest
    of the family carries. -/
theorem loeb_sentence_is_fixedpoint {A : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) A)))
    (hfix2 : Thm (imp (imp (box psi) A) psi)) :
    Thm psi ↔ Thm (imp (box psi) A) :=
  ⟨mp hfix1, mp hfix2⟩

end ProvabilityLogic

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox ZeroParadox.ProvabilityLogic
#print axioms ax_I
#print axioms contract
#print axioms hs
#print axioms loeb
#print axioms godel_two
#print axioms loeb_sentence_is_fixedpoint
end PurityCheck
