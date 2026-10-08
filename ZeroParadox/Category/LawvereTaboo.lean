import ZeroParadox.Category.Lawvere
import ZeroParadox.Category.LawvereDecidable
import ZeroParadox.Category.ExcludedMiddleBridge

set_option maxHeartbeats 400000

/-!
# The diagonal engine's supplier is a constructive taboo

## Engineer's Take

We could only say the framework essentially never introduces choice. I wanted to know whether there
was a lever we could press on to make it actually never.

There was, and pressing it gave the opposite answer to the one I expected. The general statement is
not something we failed to prove cheaply. It is a place where proof cannot cross, and now we know
exactly where the line is.

That is the goal, not a gap. The edge of provability is what we are looking for.

I am leaving the design question open. The answer is the Lean itself.

---

`wem_of_fixedPointFree`: the ∀-closed general form of `fixedPointFree_of_nontrivial`
(`ZeroParadox/Category/Lawvere.lean`) implies weak excluded middle, with no `Classical.choice`; its
consequence is stated in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV. The result, what is not
claimed, the prior art and the section map are in `ZeroParadox/Category/LawvereTaboo.md`, beside this file.
-/

namespace ZeroParadox

/-! ## § I — Weak excluded middle

`ZeroParadox/Category/ExcludedMiddleBridge.lean` supplies `ExcludedMiddle : ∀ p : Prop, p ∨ ¬p`.
The taboo below lands on the strictly weaker principle, stated here in the same hypothesis form:
never an `axiom`, always discharged by the caller. -/

/-- **Weak excluded middle** (equivalently De Morgan's law), as a hypothesis rather than an axiom.
Strictly weaker than `ExcludedMiddle` intuitionistically; `wem_of_excludedMiddle` records the one
implication that is immediate. -/
def WeakExcludedMiddle : Prop := ∀ p : Prop, ¬p ∨ ¬¬p

/-- Excluded middle implies weak excluded middle. Recorded so the two principles sit in a stated
order rather than an assumed one. The converse is not provable intuitionistically and is not
asserted here. -/
theorem wem_of_excludedMiddle (h : ExcludedMiddle) : WeakExcludedMiddle := by
  intro p
  rcases h p with hp | hnp
  · exact Or.inr (fun hn => hn hp)
  · exact Or.inl hnp

/-! ## § II — The witness

Three tokens, and a relation that glues the third to the first **when `p` holds** and to the second
**when `¬p` holds**. Whichever way `p` goes, the third token collapses onto one of the other two —
but constructively it collapses onto neither, and the first two never collapse onto each other.

That last point is what the whole argument turns on, and it is why the witness has three tokens
rather than two: a fixed-point-free `g` must move the third token *somewhere*, and the only places
available are the first two. Which one it picks is exactly a decision about `¬p` versus `¬¬p`.

Compare `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`'s `Two p`, which is empty-or-two-element.
The move is the same in spirit — build a type out of a proposition and let a general principle
inspect it — but the witness is different, because the principle being tested is different. -/

/-- Three tokens. `tx` is the one that gets glued. -/
inductive Tok : Type
  | t0 : Tok
  | t1 : Tok
  | tx : Tok

/-- The gluing relation: `tx` is identified with `t0` under `p`, and with `t1` under `¬p`. `t0` and
`t1` are never identified — no clause relates them, and § II's `glue_b0_ne_b1` proves the generated
equivalence does not either. -/
def tokRel (p : Prop) : Tok → Tok → Prop := fun a b =>
  (a = Tok.t0 ∧ b = Tok.tx ∧ p) ∨ (a = Tok.tx ∧ b = Tok.t0 ∧ p) ∨
  (a = Tok.t1 ∧ b = Tok.tx ∧ ¬p) ∨ (a = Tok.tx ∧ b = Tok.t1 ∧ ¬p)

/-- The witness type: three tokens modulo the gluing. Classically this is a two-element type
whichever way `p` goes; constructively its element count is undetermined, while `b₀ ≠ b₁` holds
unconditionally. -/
def Glue (p : Prop) : Type := Quot (tokRel p)

/-- The first distinguished point. -/
def gb0 (p : Prop) : Glue p := Quot.mk _ Tok.t0

/-- The second distinguished point. -/
def gb1 (p : Prop) : Glue p := Quot.mk _ Tok.t1

/-- The glued point: equal to `gb0` under `p`, equal to `gb1` under `¬p`, provably equal to neither
without deciding `p`. -/
def gx (p : Prop) : Glue p := Quot.mk _ Tok.tx

/-- The separating invariant. `t0` gets `False`, `t1` gets `True`, and `tx` gets `¬p` — which is
`False` exactly when `p` holds (so it may be glued to `t0`) and `True` exactly when `¬p` holds (so
it may be glued to `t1`). This is what makes the invariant survive both gluing clauses. -/
def tokInv (p : Prop) : Tok → Prop
  | Tok.t0 => False
  | Tok.t1 => True
  | Tok.tx => ¬p

theorem tokInv_respects (p : Prop) : ∀ a b : Tok, tokRel p a b → tokInv p a = tokInv p b := by
  rintro a b (⟨rfl, rfl, hp⟩ | ⟨rfl, rfl, hp⟩ | ⟨rfl, rfl, hnp⟩ | ⟨rfl, rfl, hnp⟩)
  · exact propext ⟨fun h => h.elim, fun h => h hp⟩
  · exact propext ⟨fun h => h hp, fun h => h.elim⟩
  · exact propext ⟨fun _ => hnp, fun _ => trivial⟩
  · exact propext ⟨fun _ => trivial, fun _ => hnp⟩

/-- The invariant, transported to the quotient. -/
def glueInv (p : Prop) : Glue p → Prop := Quot.lift (tokInv p) (tokInv_respects p)

/-- **The two distinguished points are distinct, unconditionally** — no assumption on `p`. The
invariant sends them to `False` and `True`. -/
theorem glue_b0_ne_b1 (p : Prop) : gb0 p ≠ gb1 p := by
  intro h
  have : (False : Prop) = True := congrArg (glueInv p) h
  exact this.mpr trivial |>.elim

/-- Under `p`, the glued point *is* the first point. -/
theorem gx_eq_gb0 (p : Prop) (hp : p) : gx p = gb0 p :=
  Quot.sound (Or.inr (Or.inl ⟨rfl, rfl, hp⟩))

/-- Under `¬p`, the glued point *is* the second point. -/
theorem gx_eq_gb1 (p : Prop) (hnp : ¬p) : gx p = gb1 p :=
  Quot.sound (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hnp⟩)))

/-- **Every element of the witness is one of the three tokens.** This is `Quot.ind` — an eliminator
into `Prop`, so it is available with no classical input, and it is the step that turns "`g` moved
`gx` somewhere" into a usable three-way disjunction. -/
theorem glue_cases (p : Prop) (z : Glue p) : z = gb0 p ∨ z = gb1 p ∨ z = gx p := by
  refine Quot.inductionOn z ?_
  rintro (_ | _ | _)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ## § III — The taboo

Feed the witness to the general principle. It returns some fixed-point-free `g`, and `g (gx p)` must
be one of the three tokens; it cannot be `gx p` itself, because `g` is fixed-point-free. So it is
`gb0 p` or `gb1 p` — and each branch decides a side of `¬p ∨ ¬¬p`:

* if `g (gx p) = gb0 p` then `p` must fail, since `p` would make `gx p = gb0 p` and hence `g` fix it;
* if `g (gx p) = gb1 p` then `¬p` must fail, for the mirror-image reason.

Both branches are informative, which is the same design requirement as in
`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` and the reason the witness is glued on both
sides. -/

-- Prior art, cited not claimed, all read from source.
-- Bauer, "On fixed-point theorems in synthetic computability", Tbilisi Math. J. 10(3) (2017), Cor 4.3,
-- p. 175: every endomap on a countably generated ωcppo has a fixed point, and after it, "Because Σ has
-- the fixed point property but 2 and Ω do not (consider negation), there is a chain of proper
-- inclusions 2 ⊊ Σ ⊊ Ω." Σ contains 2's two distinct truth values, so in synthetic computability the
-- hypothesis below fails at Σ: a counter-model for the hypothesis, not for the implication, which runs
-- from the hypothesis to weak excluded middle.
-- de Jong–Escardó, arXiv:2102.08812, Cor 39(iii)-(iv), p. 11: a nontrivial locally small sup-lattice
-- (or bounded complete poset, or dcpo) with decidable equality exists iff weak excluded middle holds,
-- and a positive one iff excluded middle holds. The same landing principle for a different hypothesis.
-- Booij–Escardó–Lumsdaine–Shulman, "Parametricity, automorphisms of the universe, and excluded middle",
-- arXiv:1701.05617, Thm 3, p. 4: a function `f : ∏ X : U, X → X`, natural under equivalence, with
-- `f_X(x) ≠ x` for some isolated point `x : X`, gives excluded middle. A different statement: one
-- uniform natural family moving one isolated point lands on full excluded middle, while the
-- hypothesis below asks for one fixed-point-free map per type with two distinct points, with no
-- naturality, and lands on weak excluded middle. Their Thm 5 (Simpson), p. 5: assuming function
-- extensionality for 0-valued functions, an extensional, strongly non-constant `f : U → 2` exists iff
-- weak excluded middle holds. The proof technique below is Simpson's (pp. 5-6): build a type from a
-- proposition, "Z = ¬A × X + ¬¬A × Y", and case-split a value computed on it, "If it is tt, then it
-- is not ff, and so ¬A; while if it is ff, then it is not tt, and so ¬¬A." The witness here differs:
-- a quotient glued under `p` and under `¬p` (§ II), not a sum over `¬A` and `¬¬A`.
/-- **The general fixed-point-free statement implies weak excluded middle.**

The hypothesis is the ∀-closure of `fixedPointFree_of_nontrivial`
(`ZeroParadox/Category/Lawvere.lean`) at `Type`.

Choice-free: the footprint is `[propext, Quot.sound]`, both of which are used to build the
*witness*, not to make the decision. The classical content is entirely in the hypothesis. -/
theorem wem_of_fixedPointFree
    (H : ∀ (β : Type) (b₀ b₁ : β), b₀ ≠ b₁ → ∃ g : β → β, ∀ x, g x ≠ x) :
    WeakExcludedMiddle := by
  intro p
  obtain ⟨g, hg⟩ := H (Glue p) (gb0 p) (gb1 p) (glue_b0_ne_b1 p)
  have hgx : g (gx p) ≠ gx p := hg (gx p)
  rcases glue_cases p (g (gx p)) with h0 | h1 | hx
  · exact Or.inl fun hp => hgx (h0.trans (gx_eq_gb0 p hp).symm)
  · exact Or.inr fun hnp => hgx (h1.trans (gx_eq_gb1 p hnp).symm)
  · exact absurd hx hgx

/-! ## § IV — Non-vacuity, and the consequence for the ledger

The hypothesis of § III is not an unsatisfiable antecedent: the framework's own
`fixedPointFree_of_nontrivial` supplies it. That theorem is classical, which is the point — it is
the source end of the arrow, exactly as `comparable_of_classical` is in
`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`. -/

/-- **The hypothesis is not vacuous** — `fixedPointFree_of_nontrivial`
(`ZeroParadox/Category/Lawvere.lean`) supplies it. Classical by construction; that is what § III is
measuring the price of. -/
theorem fixedPointFree_of_classical :
    ∀ (β : Type) (b₀ b₁ : β), b₀ ≠ b₁ → ∃ g : β → β, ∀ x, g x ≠ x :=
  fun _ _ _ hne => fixedPointFree_of_nontrivial hne

/-- **The composite, stated once.** Read together with `fixedPointFree_of_classical`: the general
statement is available in Lean, and it is available only at the price § III names.

This is the ledger entry. `ZeroParadox/Category/LawvereDecidable.lean` shows the `Classical.choice`
on `fixedPointFree_of_nontrivial` **disappears** under `[DecidableEq β]`; this file shows that removing
it without that instance would prove weak excluded middle without choice, a non-removability result on
the premise stated in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV. The two together locate the cost exactly: not in the diagonal, and
not in the two-point swap, but in stating the swap over types where it is not computable. -/
theorem wem_of_classical_supplier
    (H : ∀ (β : Type) (b₀ b₁ : β), b₀ ≠ b₁ → ∃ g : β → β, ∀ x, g x ≠ x) :
    ∀ p : Prop, ¬p ∨ ¬¬p :=
  wem_of_fixedPointFree H

/-- **The decidable route is untouched by the taboo**, and this is the fence on it.

`fixedPointFree_of_nontrivial_decidable` (`ZeroParadox/Category/LawvereDecidable.lean`) is
`[propext]`, and § III does not contradict that: `Glue p` has no `DecidableEq` instance, and giving
it one would decide `p`. So the taboo says nothing about the decidable statement — it says the
*generality* is what costs the choice. Recorded as a theorem rather than a comment so the claim is
checked rather than asserted.

Building this emits the same `does not use the following hypothesis in its type: [DecidableEq β]`
warning as its source file, and for the same reason: the instance is used in the proof term, not in
the statement. It is left unsuppressed here exactly as
`ZeroParadox/Category/LawvereDecidable.lean` leaves it, and that file's docstring explains why. -/
theorem decidable_route_unaffected {β : Type} [DecidableEq β] {b₀ b₁ : β} (hne : b₀ ≠ b₁) :
    ∃ g : β → β, ∀ x, g x ≠ x :=
  fixedPointFree_of_nontrivial_decidable hne

end ZeroParadox

/-! ## Axiom Purity Check

§ I-III must be choice-free: the classical content is the hypothesis, not the proof.
`fixedPointFree_of_classical` is classical by construction (the source end of the arrow) and is not
a purity claim — it is the theorem whose price is being measured.

Read `wem_of_fixedPointFree` and `fixedPointFree_of_classical` as a **pair**. The first says the
general statement costs weak excluded middle; the second says the framework is paying it. -/

section PurityCheck
open ZeroParadox

-- § I.
#print axioms WeakExcludedMiddle
#print axioms wem_of_excludedMiddle

-- § II — the witness. `propext` and `Quot.sound` are expected and are used to *build* the witness
-- (the invariant is a `Prop`-valued `Quot.lift`; the gluing is `Quot.sound`). Neither is choice.
#print axioms glue_b0_ne_b1
#print axioms gx_eq_gb0
#print axioms gx_eq_gb1
#print axioms glue_cases

-- § III — the taboo. MUST NOT carry `Classical.choice`.
#print axioms wem_of_fixedPointFree
#print axioms wem_of_classical_supplier

-- § IV — classical by design; the source end of the arrow.
#print axioms fixedPointFree_of_classical

-- The decidable counterpart, reprinted from `ZeroParadox/Category/LawvereDecidable.lean` so the
-- contrast sits in one place: the taboo above and this `[propext]` reading are compatible, and
-- together they localize the cost.
#print axioms decidable_route_unaffected
#print axioms fixedPointFree_of_nontrivial

end PurityCheck
