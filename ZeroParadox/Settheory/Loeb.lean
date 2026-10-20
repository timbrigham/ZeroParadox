import ZeroParadox.Die
import Mathlib.Tactic

/-!
# Löb's theorem — the diagonal family's PROVABILITY-modal face (probe, from scratch)

## Engineer's Take

Back to basics. We're filling in everything that's left where the relationship between one over
infinity and a bottom element still wasn't fully defined, using the same structure that we have for
everything else in the family.

---

## Formal Overview
`⊢ (□A → A)` implies `⊢ A`, from the Hilbert–Bernays–Löb derivability conditions plus a diagonal taken
as a hypothesis — built from scratch; no modal or provability logic located in the pin (2026-08-17). Design,
placement and the Gödel-second corollary: `ZeroParadox/Settheory/Loeb.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ## § I. The provability-logic typeclass -/

/-- **An abstract provability logic.** Sentences `S` with implication `imp`, provability modality `box`,
    and a "provable" predicate `Thm`, satisfying: the implicational Hilbert base (`ax_K`, `ax_S`) closed
    under modus ponens (`mp`); and the three Hilbert–Bernays–Löb derivability conditions
    (`nec` = D1 necessitation, `ax_D2` = distribution of `box` over `imp`, `ax_D3`). This is exactly the
    apparatus Löb's theorem needs, and no more. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: no modal or provability logic was located in the pinned Mathlib as of 2026-08-30, searched on three axes (Löb/GL; Kripke and modal logic;
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

/-- **Gödel's second incompleteness, via Löb.** If the system is consistent (`⊬ falsum`) and has a Löb
    diagonal for falsum (`hfix1`, `hfix2`), it cannot prove `□falsum → falsum` — the internal statement of its own consistency. Immediate from Löb at `A = falsum`:
    a proof of `□falsum → falsum` would yield `⊢ falsum`, contradicting consistency. So Löb subsumes
    Gödel's second theorem; the wall on the provability axis is the unprovability of consistency. -/
theorem godel_two {falsum : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) falsum)))
    (hfix2 : Thm (imp (imp (box psi) falsum) psi))
    (hcon : ¬ Thm falsum) : ¬ Thm (imp (box falsum) falsum) :=
  fun h => hcon (loeb psi hfix1 hfix2 h)

/-! ## § V. The bottom-element relationship: an assumed Löb sentence is a provability fixed point -/

/-- **Given a Löb sentence `ψ` (the hypotheses `hfix1`, `hfix2`), `ψ` is a fixed point, up to
    provability, of `p ↦ (□p → A)`; reading it as the face's bottom is the family's criterion, not
    this theorem.** `⊢ ψ` iff `⊢ (□ψ → A)`; with `⊢ □A → A` it yields `⊢ A` (`loeb`, § III). The
    statement names no bottom. -/
theorem loeb_sentence_is_fixedpoint {A : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) A)))
    (hfix2 : Thm (imp (imp (box psi) A) psi)) :
    Thm psi ↔ Thm (imp (box psi) A) :=
  ⟨mp hfix1, mp hfix2⟩

/-! ## § VI. The Löb diagonal in the die's motion, on the Lindenbaum quotient -/

-- Reading (cited, not claimed): Yanofsky 2003 proves the diagonalization lemma on Lindenbaum classes
-- (Theorem 4, pp. 15–16) and derives "Löb's paradox" from it (p. 18); here the diagonal is a
-- hypothesis, as in `loeb`. On PA's Lindenbaum algebra `φ ↦ ¬φ` has no fixed point (Barendregt and
-- Terwijn 2018, arXiv:1809.06233, p. 3), so such fixed points are map by map.

/-- `Statement:` `a` and `b` are provably equivalent: `⊢ a → b` and `⊢ b → a`. -/
def ProvEquiv (a b : S) : Prop := Thm (imp a b) ∧ Thm (imp b a)

/-- `Statement:` provable equivalence is an equivalence relation on `S`. -/
def provSetoid (S : Type*) [ProvabilityLogic S] : Setoid S where
  r := ProvEquiv
  iseqv := ⟨fun a => ⟨ax_I a, ax_I a⟩, fun h => ⟨h.2, h.1⟩,
    fun h1 h2 => ⟨hs h1.1 h2.1, hs h2.2 h1.2⟩⟩

/-- `Statement:` the Lindenbaum quotient: sentences up to provable equivalence. -/
abbrev Lindenbaum (S : Type*) [ProvabilityLogic S] := Quotient (provSetoid S)

/-- `Statement:` `⊢ a → b` gives `⊢ □a → □b` (D1, then D2). -/
theorem box_mono {a b : S} (h : Thm (imp a b)) : Thm (imp (box a) (box b)) :=
  mp (ax_D2 a b) (nec h)

/-- `Statement:` `⊢ x → y` gives `⊢ (y → A) → (x → A)`. -/
theorem imp_antitone {x y : S} (A : S) (h : Thm (imp x y)) : Thm (imp (imp y A) (imp x A)) := by
  have s1 : Thm (imp (imp y A) (imp (imp x (imp y A)) (imp (imp x y) (imp x A)))) :=
    mp (ax_K _ _) (ax_S x y A)
  have s2 : Thm (imp (imp y A) (imp (imp x y) (imp x A))) := contract s1 (ax_K (imp y A) x)
  exact contract s2 (mp (ax_K (imp x y) (imp y A)) h)

/-- `Statement:` the Löb map `p ↦ (□p → A)` respects provable equivalence. -/
theorem loebMap_respects (A : S) {a b : S} (h : ProvEquiv a b) :
    ProvEquiv (imp (box a) A) (imp (box b) A) :=
  ⟨imp_antitone A (box_mono h.2), imp_antitone A (box_mono h.1)⟩

/-- `Statement:` the Löb map `p ↦ (□p → A)`, induced on the Lindenbaum quotient. -/
def loebMapQuot (A : S) : Lindenbaum S → Lindenbaum S :=
  Quotient.map (fun p => imp (box p) A) (fun _ _ h => loebMap_respects A h)

/-- `Statement:` the class of `ψ` steps to itself only in `Motion.ofFun (loebMapQuot A)` iff
    `⊢ ψ → (□ψ → A)` and `⊢ (□ψ → A) → ψ`, the hypotheses of `loeb`; both directions. -/
theorem selfOnlyAt_loebMapQuot_iff (A psi : S) :
    (Motion.ofFun (loebMapQuot A)).SelfOnlyAt (⟦psi⟧ : Lindenbaum S) ↔
      Thm (imp psi (imp (box psi) A)) ∧ Thm (imp (imp (box psi) A) psi) := by
  refine (Motion.selfOnlyAt_ofFun_iff _ _).trans ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ProvEquiv (imp (box psi) A) psi := Quotient.exact h
    exact ⟨h'.2, h'.1⟩
  · exact Quotient.sound (show ProvEquiv (imp (box psi) A) psi from ⟨h.2, h.1⟩)

/-- `Statement:` if the class of `ψ` steps to itself only in `Motion.ofFun (loebMapQuot A)` and
    `⊢ □A → A`, then `⊢ A`; one way (`loeb`). -/
theorem loeb_of_selfOnlyAt {A : S} (psi : S)
    (hy : (Motion.ofFun (loebMapQuot A)).SelfOnlyAt (⟦psi⟧ : Lindenbaum S))
    (hLob : Thm (imp (box A) A)) : Thm A :=
  let h := (selfOnlyAt_loebMapQuot_iff A psi).1 hy
  loeb psi h.1 h.2 hLob

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
#print axioms ProvEquiv
#print axioms provSetoid
#print axioms Lindenbaum
#print axioms box_mono
#print axioms imp_antitone
#print axioms loebMap_respects
#print axioms loebMapQuot
#print axioms selfOnlyAt_loebMapQuot_iff
#print axioms loeb_of_selfOnlyAt

end PurityCheck
