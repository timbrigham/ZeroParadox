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
    (`nec` = D1 necessitation, `ax_D2` = distribution of `box` over `imp`, `ax_D3`). -/
-- [ZP-CUSTOM] no Mathlib analog | reason: no modal or provability logic was located in the pinned Mathlib as of 2026-08-30, searched on three axes (Löb / GL; Kripke and modal logic;
-- provability / derivability), as recorded in `LEAN_CUSTOM_REGISTRY.md`. A typeclass carrying the
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

/-- **Löb's principle at `A` makes `□A → A` a Löb diagonal for `A`.**
    `Statement:` if `⊢ □(□A → A) → □A`, then `ψ := □A → A` satisfies both hypotheses of `loeb`,
    `⊢ ψ → (□ψ → A)` and `⊢ (□ψ → A) → ψ`; one way. The second conjunct does not use `hL` (`example`
    below); the first does, and without `hL` it is false in the class (§ IV, the `example` after the
    one-point control). Its converse is `loeb_axiom_of_loeb_diagonal` (§ VI): some Löb diagonal for `A`
    exists iff Löb's principle holds at `A` (the `example` after it). This is not the converse of `loeb`,
    which concludes Löb's RULE at `A`; that converse is false in the class (§ IV, the last `example`).
    `Reading:` it trades one input of `loeb` for another; it constructs no arithmetic diagonal. -/
theorem loeb_diagonal_of_loeb_axiom (A : S)
    (hL : Thm (imp (box (imp (box A) A)) (box A))) :
    Thm (imp (imp (box A) A) (imp (box (imp (box A) A)) A)) ∧
      Thm (imp (imp (box (imp (box A) A)) A) (imp (box A) A)) := by
  -- `hB x y : ⊢ (y → A) → ((x → y) → (x → A))`, from `ax_S` and `ax_K`
  have hB : ∀ x y : S, Thm (imp (imp y A) (imp (imp x y) (imp x A))) := fun x y =>
    contract (mp (ax_K _ _) (ax_S x y A)) (ax_K (imp y A) x)
  -- `⊢ □A → □(□A → A)`: necessitate `ax_K`, distribute with D2
  have hbox : Thm (imp (box A) (box (imp (box A) A))) :=
    mp (ax_D2 A (imp (box A) A)) (nec (ax_K A (box A)))
  exact ⟨contract (hB _ _) (mp (ax_K _ _) hL), contract (hB _ _) (mp (ax_K _ _) hbox)⟩

-- Statement: the second conjunct of `loeb_diagonal_of_loeb_axiom` holds with no Löb hypothesis.
example (A : S) : Thm (imp (imp (box (imp (box A) A)) A) (imp (box A) A)) :=
  contract (contract (mp (ax_K _ _) (ax_S _ _ A)) (ax_K _ _))
    (mp (ax_K _ _) (mp (ax_D2 A (imp (box A) A)) (nec (ax_K A (box A)))))

/-! ## § IV. Gödel's second incompleteness — the `A = falsum` corollary -/

/-- **Gödel's second incompleteness, via Löb.** If the system is consistent (`⊬ falsum`) and has a Löb
    diagonal for falsum (`hfix1`, `hfix2`), it cannot prove `□falsum → falsum` — the internal statement of its own consistency. Immediate from Löb at `A = falsum`:
    a proof of `□falsum → falsum` would yield `⊢ falsum`, contradicting consistency. So Löb subsumes
    Gödel's second theorem; the wall on the provability axis is the unprovability of consistency.
    `Statement:` it holds for every unprovable `falsum` with a Löb diagonal (bound universally; § I has no
    falsum constant); the first `example` below is one that does not imply every sentence (no ex-falso).
    `Reading:` when the class is instantiated at a theory of arithmetic and `falsum` is its falsum,
    the diagonal lemma supplying `hfix1`, `hfix2`, this is Gödel's second theorem; the floor reading
    beside this wall one is in `ZeroParadox/Settheory/Loeb.md`. -/
theorem godel_two {falsum : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) falsum)))
    (hfix2 : Thm (imp (imp (box psi) falsum) psi))
    (hcon : ¬ Thm falsum) : ¬ Thm (imp (box falsum) falsum) :=
  fun h => hcon (loeb psi hfix1 hfix2 h)

-- Reading: the propositions of the Kripke frame on the two-element strict chain, the frame of a finite
-- GL-model (Saitou & Noguchi, arXiv:2609.13780, Def. 3.4). Statement: with `box (a, b) = (b, true)`,
-- `F = (false, true)` is unprovable, is its own Löb diagonal, and `⊢ F → (false, false)` fails; Löb's
-- principle `⊢ □(□p → p) → □p` holds for every `p`; and `godel_two` applies at `F`, giving `⊬ □F → F`.
example :
    let _ : ProvabilityLogic (Bool × Bool) :=
      { imp := fun a b => (!a.1 || b.1, !a.2 || b.2)
        box := fun a => (a.2, true)
        Thm := fun a => a = (true, true)
        mp := by intro a b; revert a b; decide
        ax_K := by decide
        ax_S := by decide
        nec := by intro a; revert a; decide
        ax_D2 := by decide
        ax_D3 := by decide }
    ¬ Thm ((false, true) : Bool × Bool) ∧
      Thm (imp ((false, true) : Bool × Bool) (imp (box (false, true)) (false, true))) ∧
      Thm (imp (imp (box ((false, true) : Bool × Bool)) (false, true)) (false, true)) ∧
      ¬ Thm (imp ((false, true) : Bool × Bool) (false, false)) ∧
      (∀ p : Bool × Bool, Thm (imp (box (imp (box p) p)) (box p))) ∧
      ¬ Thm (imp (box ((false, true) : Bool × Bool)) (false, true)) := by
  intro _
  exact ⟨fun h => Bool.false_ne_true (congrArg Prod.fst h), rfl, rfl,
    fun h => Bool.false_ne_true (congrArg Prod.snd h),
    fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl,
    godel_two (falsum := ((false, true) : Bool × Bool)) (false, true) rfl rfl
      (fun h => Bool.false_ne_true (congrArg Prod.fst h))⟩

-- Reading: the one-point reflexive frame.
-- Statement: CONTROL, with `box = id` on `Bool`: `⊬ false` and `⊢ □false → false`, so `godel_two`'s
-- conclusion fails; `⊢ □p → p` for every `p`; Löb's principle fails at `false`; and no sentence is a
-- Löb diagonal for `false`.
example :
    letI : ProvabilityLogic Bool :=
      { imp := fun a b => !a || b
        box := id
        Thm := fun a => a = true
        mp := by intro a b; revert a b; decide
        ax_K := by decide
        ax_S := by decide
        nec := by intro a; revert a; decide
        ax_D2 := by decide
        ax_D3 := by decide }
    ¬ Thm false ∧ Thm (imp (box false) false) ∧ (∀ p : Bool, Thm (imp (box p) p)) ∧
      ¬ Thm (imp (box (imp (box false) false)) (box false)) ∧
      ¬ ∃ psi : Bool, Thm (imp psi (imp (box psi) false)) ∧ Thm (imp (imp (box psi) false) psi) :=
  ⟨Bool.false_ne_true, rfl, fun p => by cases p <;> rfl, Bool.false_ne_true,
    fun ⟨psi, h1, h2⟩ => by
      cases psi
      · exact Bool.false_ne_true h2
      · exact Bool.false_ne_true h1⟩

-- Statement: `loeb_diagonal_of_loeb_axiom` needs `hL`: without it its first conjunct is false in the
-- class, failing in the one-point control above at `A = false`.
example : ¬ ∀ (S : Type) [ProvabilityLogic S] (A : S),
    Thm (imp (imp (box A) A) (imp (box (imp (box A) A)) A)) := fun h =>
  Bool.false_ne_true <| @h Bool
    { imp := fun a b => !a || b
      box := id
      Thm := fun a => a = true
      mp := by intro a b; revert a b; decide
      ax_K := by decide
      ax_S := by decide
      nec := by intro a; revert a; decide
      ax_D2 := by decide
      ax_D3 := by decide } false

-- Reading: one reflexive world and one dead-end world. Statement: CONTROL, with `box (a, b) = (a, true)`
-- and `A = (false, false)`: Löb's rule at `A` holds (`⊢ □A → A` implies `⊢ A`, vacuously) and no
-- sentence is a Löb diagonal for `A`.
example :
    let _ : ProvabilityLogic (Bool × Bool) :=
      { imp := fun a b => (!a.1 || b.1, !a.2 || b.2)
        box := fun a => (a.1, true)
        Thm := fun a => a = (true, true)
        mp := by intro a b; revert a b; decide
        ax_K := by decide
        ax_S := by decide
        nec := by intro a; revert a; decide
        ax_D2 := by decide
        ax_D3 := by decide }
    (Thm (imp (box ((false, false) : Bool × Bool)) (false, false)) → Thm ((false, false) : Bool × Bool)) ∧
      ¬ ∃ psi : Bool × Bool, Thm (imp psi (imp (box psi) (false, false))) ∧
          Thm (imp (imp (box psi) (false, false)) psi) := by
  intro _
  refine ⟨fun h => ?_, ?_⟩
  · exact absurd (congrArg Prod.snd h) Bool.false_ne_true
  · rintro ⟨⟨a, b⟩, h1, h2⟩
    cases a <;> cases b <;>
      first
      | exact Bool.false_ne_true (congrArg Prod.fst h1)
      | exact Bool.false_ne_true (congrArg Prod.snd h1)
      | exact Bool.false_ne_true (congrArg Prod.fst h2)

-- Statement: the converse of `loeb` at one `A` (Löb's rule at `A` gives a Löb diagonal for `A`) is false
-- in the class, failing in the control above at `A = (false, false)`.
example : ¬ ∀ (S : Type) [ProvabilityLogic S] (A : S), (Thm (imp (box A) A) → Thm A) →
    ∃ psi : S, Thm (imp psi (imp (box psi) A)) ∧ Thm (imp (imp (box psi) A) psi) := fun h => by
  obtain ⟨⟨a, b⟩, h1, h2⟩ := @h (Bool × Bool)
    { imp := fun a b => (!a.1 || b.1, !a.2 || b.2)
      box := fun a => (a.1, true)
      Thm := fun a => a = (true, true)
      mp := by intro a b; revert a b; decide
      ax_K := by decide
      ax_S := by decide
      nec := by intro a; revert a; decide
      ax_D2 := by decide
      ax_D3 := by decide } (false, false)
    (fun h => absurd (congrArg Prod.snd h) Bool.false_ne_true)
  cases a <;> cases b <;>
    first
    | exact Bool.false_ne_true (congrArg Prod.fst h1)
    | exact Bool.false_ne_true (congrArg Prod.snd h1)
    | exact Bool.false_ne_true (congrArg Prod.fst h2)

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

/-- `Statement:` if `ψ` is a Löb diagonal for `A` (`hfix1`, `hfix2`), then Löb's principle holds at `A`:
    `⊢ □(□A → A) → □A`; one way. Converse of `loeb_diagonal_of_loeb_axiom` (§ III). -/
theorem loeb_axiom_of_loeb_diagonal {A : S} (psi : S)
    (hfix1 : Thm (imp psi (imp (box psi) A)))
    (hfix2 : Thm (imp (imp (box psi) A) psi)) :
    Thm (imp (box (imp (box A) A)) (box A)) := by
  have hd : Thm (imp (box psi) (box A)) :=
    contract (hs (box_mono hfix1) (ax_D2 (box psi) A)) (ax_D3 psi)
  exact hs (box_mono (hs (imp_antitone A hd) hfix2)) hd

-- Statement: some sentence is a Löb diagonal for `A` iff Löb's principle holds at `A`; both directions.
example (A : S) :
    (∃ psi : S, Thm (imp psi (imp (box psi) A)) ∧ Thm (imp (imp (box psi) A) psi)) ↔
      Thm (imp (box (imp (box A) A)) (box A)) :=
  ⟨fun ⟨psi, h1, h2⟩ => loeb_axiom_of_loeb_diagonal psi h1 h2,
    fun hL => ⟨_, (loeb_diagonal_of_loeb_axiom A hL).1, (loeb_diagonal_of_loeb_axiom A hL).2⟩⟩

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

-- Statement: on the Lindenbaum quotient the Löb diagonal is a literal fixed point: `⟦ψ⟧` is fixed by
-- `loebMapQuot A` iff `hfix1` and `hfix2` hold; both directions.
example (A psi : S) :
    loebMapQuot A ⟦psi⟧ = ⟦psi⟧ ↔
      Thm (imp psi (imp (box psi) A)) ∧ Thm (imp (imp (box psi) A) psi) :=
  (Motion.selfOnlyAt_ofFun_iff _ _).symm.trans (selfOnlyAt_loebMapQuot_iff A psi)

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
#print axioms loeb_diagonal_of_loeb_axiom
#print axioms godel_two
#print axioms loeb_sentence_is_fixedpoint
#print axioms ProvEquiv
#print axioms provSetoid
#print axioms Lindenbaum
#print axioms box_mono
#print axioms imp_antitone
#print axioms loeb_axiom_of_loeb_diagonal
#print axioms loebMap_respects
#print axioms loebMapQuot
#print axioms selfOnlyAt_loebMapQuot_iff
#print axioms loeb_of_selfOnlyAt

end PurityCheck
