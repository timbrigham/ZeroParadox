import ZeroParadox.Ordinal.SnapNucleusConstructive
import ZeroParadox.Information.Surprisal
import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 1000000

/-!
# A priced interface: notations denoting the ordinals up to ε₀, a map into `Ordinal`, and both sides' axiom footprints

The axiom price of crossing from ordinal notations into Mathlib's `Ordinal`, measured by the purity
block at the end. Argument, prior art and fences: `ZeroParadox/Ordinal/PricedInterface.md`.

## Engineer's Take

If ZP-N is unclassified, we should reevaluate the Lean and see if we can get it right before bumping the
version.

I was hoping this was one of those cases where you take the entire class and make it an instance of that,
the same as we have for other solutions where the scope was one order of magnitude too high or too low.
In programming terms it is the initialization of a class you did not need.

The idea is to build it using this framework and then cross reference it to the more general category.
That looks like an interface between constructive and choice based logic, and that in itself is valuable
even if it means going single instance versus general. I think that is exactly how this interface is
going to have to work.

---
-/

namespace ZeroParadox

open Ordinal

/-! ### The carrier

`SynONote` with one point adjoined on top: the shape of Castéran's `ON_plus` (sum of notation systems)
with a one-point right summand, not an instance of it, because `SynONote`'s order is not well-founded
(the `example` after `e0Repr_not_injective`). The order, lattice and decidability structure below is all
Mathlib's `WithTop` machinery, not built here. -/

/-- **The carrier: ordinal notations with a single adjoined top.**

`⊤` is the intended denotation site for ε₀, and `e0Repr` sends it there. Everything below `⊤` is an
ordinal notation carrying the choice-free comparator order of `SynONote`.

Its denotations are the ordinals below **ε₀ + 1** (the segment below ε₀, plus ε₀ itself). Its own
order is not a well-order, so it is not a notation system for ε₀ + 1 in the well-ordered sense. -/
abbrev E0Note : Type := WithTop SynONote

/-- The notations, viewed inside the carrier. -/
def e0Coe (x : ONote) : E0Note := (toSyn x : SynONote)

/-- Comparison on the carrier is decidable — inherited from Mathlib's `WithTop.decidableLE` applied to
the comparator-derived order on `SynONote`. This is Castéran's `lt_eq_lt_dec` (decidability survives
adjunction) at instance level; nothing is proved here. -/
@[reducible] def e0DecidableLE : DecidableLE E0Note := inferInstance

/-- Strict comparison on the carrier is decidable. -/
@[reducible] def e0DecidableLT : DecidableLT E0Note := inferInstance

/-- Equality on the carrier is decidable. -/
@[reducible] def e0DecidableEq : DecidableEq E0Note := inferInstance

/-- Every notation sits strictly below the adjoined top. -/
theorem e0Coe_lt_top (x : ONote) : e0Coe x < (⊤ : E0Note) := WithTop.coe_lt_top _

/-- The adjoined top bounds the whole carrier. -/
theorem e0_le_top (a : E0Note) : a ≤ (⊤ : E0Note) := le_top

/-! ### The tower operator, and the stipulated fixed point

`e0OmegaPow` extends `omegaPow` by *defining* it to fix `⊤`. The fixed point exists by that definition.
Only its uniqueness is a theorem. -/

/-- **The tower operator on the carrier.** Below the top it is `omegaPow`; at the top it is **defined**
to be the identity.

The value at `⊤` is a stipulation. It is not derived, not forced, and defeats no obstruction. -/
def e0OmegaPow : E0Note → E0Note :=
  WithTop.recTopCoe ⊤ fun x => ((toSyn (omegaPow (ofSyn x)) : SynONote) : E0Note)

/-- **The fixed point, by definition.** `⊤` is fixed because `e0OmegaPow` was written that way. -/
@[simp] theorem e0OmegaPow_top : e0OmegaPow ⊤ = ⊤ := rfl

/-- Below the top, the tower operator is the syntactic `omegaPow`. -/
@[simp] theorem e0OmegaPow_coe (x : ONote) :
    e0OmegaPow (e0Coe x) = e0Coe (omegaPow x) := rfl

/-- **Uniqueness of the fixed point — this half is a theorem.** `⊤` is the *only* fixed point of
`e0OmegaPow`, because below the top `omegaPow` moves everything (`omegaPow_ne_self`).

Read together with `e0OmegaPow_top`: existence is by fiat at the adjoined point, uniqueness is proved. -/
theorem e0OmegaPow_fixedpoint_iff (a : E0Note) : e0OmegaPow a = a ↔ a = ⊤ := by
  constructor
  · induction a using WithTop.recTopCoe with
    | top => intro _; rfl
    | coe x =>
        intro h
        have h' : (toSyn (omegaPow (ofSyn x)) : SynONote) = x := WithTop.coe_injective h
        exact absurd h' (omegaPow_ne_self (ofSyn x))
  · rintro rfl; rfl

/-! ### The map into `Ordinal` — the crossing

This is where the classical assumption is paid. `ONote.repr` is Mathlib's denotation map, and it is
`noncomputable` there for exactly the reason its docstring gives. -/

/-- **Every ordinal notation denotes strictly below ε₀.**

The first of `ON_correct`'s three fields (Castéran, `ON_Generic.v`), here for Mathlib's `ONote` and
Mathlib's ε₀. Structural induction: ε₀ is a fixed point of `ω ^ ·`, hence both additively and
multiplicatively principal, which is exactly what closes the `oadd` case.

Stated for **all** of `ONote`, including notations not in normal form. -/
theorem repr_lt_epsilon0 : ∀ x : ONote, ONote.repr x < ε₀ := by
  have hfp : ω ^ ε₀ = ε₀ := omega0_opow_epsilon 0
  have hadd : IsPrincipal (· + ·) ε₀ := by
    have := isPrincipal_add_omega0_opow ε₀
    rwa [hfp] at this
  have hmul : IsPrincipal (· * ·) ε₀ := by
    have := isPrincipal_mul_omega0_opow_opow ε₀
    rwa [hfp, hfp] at this
  intro x
  induction x with
  | zero => simp
  | oadd e n a ihe iha =>
      have hpow : ω ^ ONote.repr e < ε₀ := by
        rw [← hfp]
        exact (opow_lt_opow_iff_right one_lt_omega0).2 ihe
      have hn : ((n : ℕ) : Ordinal) < ε₀ := natCast_lt_epsilon n 0
      have hmulp : ω ^ ONote.repr e * ((n : ℕ) : Ordinal) < ε₀ := hmul hpow hn
      simpa using hadd hmulp iha

/-- **`Statement:` every ordinal below ε₀ is denoted by a normal-form notation.** The second of
`ON_correct`'s fields, on `NF` notations. Strong induction on `o`, split as
`ω ^ log ω o * m + o % ω ^ log ω o`. Not located in the Mathlib pin as of 2026-10-04 (searched
`Notation.lean` for ε₀ / epsilon / surj / lt_epsilon / `∃ o`; the corpus for `repr` with ε₀).

`Reading:` each address is a finite term; the addresses fill the ordinals below ε₀ (the order-type
`example` below), and ε₀ itself has no address (`repr_lt_epsilon0`). -/
theorem repr_surj_below_epsilon0 : ∀ o < ε₀, ∃ x : ONote, x.NF ∧ x.repr = o := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro ho
  rcases eq_or_ne o 0 with h0 | h0
  · exact ⟨0, ONote.NF.zero, by simp [h0]⟩
  have hpow : ω ^ log ω o ≤ o := opow_log_le_self ω h0
  have helt : log ω o < o := by
    by_contra hc
    have : ω ^ o ≤ o := (opow_le_opow_right omega0_pos (not_lt.mp hc)).trans hpow
    exact absurd (epsilon_zero_le_of_omega0_opow_le this) (not_le.mpr ho)
  obtain ⟨e', he'NF, he'⟩ := IH _ helt (helt.trans ho)
  obtain ⟨m, hm⟩ := lt_omega0.mp (div_opow_log_lt o one_lt_omega0)
  have hrlt : o % ω ^ log ω o < ω ^ log ω o := mod_lt o (opow_pos _ omega0_pos).ne'
  have hrlto : o % ω ^ log ω o < o := hrlt.trans_le hpow
  obtain ⟨r', hr'NF, hr'⟩ := IH _ hrlto (hrlto.trans ho)
  have hdm := div_add_mod o (ω ^ log ω o)
  rw [hm] at hdm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hdm
    exact absurd (lt_of_eq_of_lt hdm.symm hrlt) (not_lt.mpr hpow)
  refine ⟨ONote.oadd e' ⟨m, Nat.pos_of_ne_zero hm0⟩ r', ?_, ?_⟩
  · have hb : ONote.repr r' < ω ^ ONote.repr e' := by rw [hr', he']; exact hrlt
    exact ONote.NF.oadd he'NF _ (ONote.NF.below_of_lt' hb hr'NF)
  · simp only [ONote.repr, he', hr', PNat.mk_coe]
    exact hdm

-- `Statement:` the normal-form notations, ordered by denotation, have order type exactly ε₀.
example : typeLT NONote = ε₀ := by
  have e : NONote ≃o Set.Iio (ε₀ : Ordinal.{0}) :=
    StrictMono.orderIsoOfSurjective (fun x => ⟨x.repr, repr_lt_epsilon0 x.1⟩)
      (fun _ _ h => h) (fun y => by
        obtain ⟨x, hNF, hx⟩ := repr_surj_below_epsilon0 y.1 y.2
        exact ⟨⟨x, hNF⟩, Subtype.ext hx⟩)
  have h := e.toRelIsoLT.ordinal_lift_type_eq
  rw [Ordinal.type_lt_Iio, Ordinal.lift_lift] at h
  exact Ordinal.lift_inj.1 h

/-- **The crossing.** The carrier's denotation map into Mathlib's classical `Ordinal`: notations go by
`ONote.repr`, and the adjoined top goes to ε₀.

An instance of Castéran's `ON_correct` shape (`Schutte/Correctness_E0.v` is the existing ε₀
instantiation), with Mathlib's constructed `Ordinal` as the classical target instead of Schütte's
axiomatized `Ord`. Two of its three fields are established here, the comparator field is not: see
`ZeroParadox/Ordinal/PricedInterface.md` § *What is NOT proved here*. -/
noncomputable def e0Repr : E0Note → Ordinal :=
  WithTop.recTopCoe ε₀ fun x => ONote.repr (ofSyn x)

/-- The adjoined top denotes ε₀. -/
@[simp] theorem e0Repr_top : e0Repr ⊤ = ε₀ := rfl

/-- Notations denote by Mathlib's `ONote.repr`. -/
@[simp] theorem e0Repr_coe (x : ONote) : e0Repr (e0Coe x) = ONote.repr x := rfl

/-- The whole carrier denotes at or below ε₀. -/
theorem e0Repr_le_epsilon0 (a : E0Note) : e0Repr a ≤ ε₀ := by
  induction a using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe x => exact (repr_lt_epsilon0 (ofSyn x)).le

/-- **ε₀ is denoted by the adjoined point and by nothing else.** The fibre of the map over ε₀ is
exactly `{⊤}` — which is the precise sense in which "the top is ε₀". -/
theorem e0Repr_eq_epsilon0_iff (a : E0Note) : e0Repr a = ε₀ ↔ a = ⊤ := by
  constructor
  · induction a using WithTop.recTopCoe with
    | top => intro _; rfl
    | coe x => intro h; exact absurd h (repr_lt_epsilon0 (ofSyn x)).ne
  · rintro rfl; rfl

-- `Statement:` `e0Repr` is onto the ordinals at or below ε₀ (from `repr_surj_below_epsilon0`).
example (o : Ordinal) (ho : o ≤ ε₀) : ∃ a : E0Note, e0Repr a = o := by
  rcases ho.lt_or_eq with h | rfl
  · obtain ⟨x, -, hx⟩ := repr_surj_below_epsilon0 o h
    exact ⟨e0Coe x, (e0Repr_coe x).trans hx⟩
  · exact ⟨⊤, rfl⟩

/-- **The fence: the map is not injective, so this carrier is NOT `ON_correct` at ε₀ + 1.**

`ON_correct` additionally requires the syntactic comparator to agree with the semantic order. That
fails on raw `ONote`, because distinct notations that are not in normal form can denote the same
ordinal — `1 + ω` and `ω` are the smallest witness (the same one used by
`mathlib_ONote_order_not_antisymm` in `ZeroParadox/Ordinal/SnapNucleusConstructive.lean`). Ontoness
does not fail: `e0Repr` is onto the ordinals at or below ε₀ (the `example` above).

Restricting the carrier to `NF` notations is the standard repair and is **not** performed here; `NF` is
defined through `repr` and would import the choice-carrying side into the constructive development.
`repr_surj_below_epsilon0` uses `NF` on the crossing side only.

⚠ **AND THE SAME FACT READS THE OTHER WAY — added 2026-08-05 (Tim).** A failure of faithfulness is an
availability of **uncertainty**. The fiber this non-injectivity creates — two notations, one denotation —
carries a genuinely non-degenerate distribution (`repr_collision`,
`exists_fiber_supported_non_pure_pmf` below).

⚠ **State the fiber's role correctly; a first draft did not.** It is NOT that the fiber "lifts
`pmf_subsingleton_isPure`'s obstruction" — `E0Note` is already non-subsingleton (`⊤` and `e0Coe 0`
differ), so that obstruction was **never binding here**. What the collision supplies is the strictly
stronger fact: a spread distribution **confined to a single denotation**. Any two distinct notations
give a non-degenerate distribution; only a *collision* gives one whose entire support denotes one
ordinal.

**AND THE COLLISION IS NECESSARY — measured, not assumed.**
`confined_non_pure_refutes_injective` (`ZeroParadox/Information/Surprisal.lean`) proves the converse:
under an *injective* map a confined distribution collapses to one support point, so a spread one
refutes injectivity outright. Measured at round-3 revalidation, after the sentence had been re-worded
three times without anyone asking whether the claim underneath was true.

**The IN-FIELD name is already in the ride-along: `ONote.repr_inj`.** Mathlib's
`ONote.repr_inj` (`Mathlib/SetTheory/Ordinal/Notation.lean`) requires `NF` on both arguments, and
`ZeroParadox/Ordinal/PricedInterface.md` § *What is NOT proved here* already says *"restricting to normal forms is the standard fix."*
That is **stronger** than naming the defect: it characterizes exactly when injectivity is **restored**,
and the `1 + ω` vs `ω` witness is precisely a non-normal-form term. Use it first.

`Reading:` (conjectural, and **an earlier draft asserted this as a flat identification, which was an
over-reach**) the framework reads the fiber as an instance of the **shape** that statistics calls
*identifiability* — the parameter-to-observable map failing to be injective. ⚠ **Do not write
"structural identifiability" for this.** Both sources on disk (Villaverde 2016; Castro & de Boer 2020,
`.claude-local/papers/`) scope that term to **parametrized dynamic models**, where "structural"
contrasts with *practical* identifiability limited by data. `e0Repr` has no data, no dynamics and no
such contrast, so the modifier does no work here. And `CLAIMS.md`'s use of the term is about **ZP-B's
real-valued threshold** under Buckingham π — a different object, and that row's own 2026-07-30 scope
correction states the term does *not* apply to ε₀ — so "it had never reached the Lean" claims a
continuity that is not there.

**NO POV KIND is claimed here, and that is deliberate** — none of the five (COINCIDENCE / INVERSION /
DRIFT / CARRIER / INVARIANT) describes "two structures share a shape". What is asserted is only the
**shape**, never an instance-of relation, which is the same fence this project keeps for the min≡max
family (whose own coincidences are separately labelled where they live). Citing that fence here is a
pointer to the precedent, not a POV claim about `e0Repr`.

`Reading:` (conjectural) the framework reads this as where statistics enters, under Tim's framing that
**succession is a state of representation**: what is uncertain is *which representation*, never *what
happened*. ⚠ **Nothing here posits that anything moved** — the no-traversal commitment is untouched, and
the distribution below is over notations, not over histories. Long form:
`.claude-local/notes/future-research/offset_from_the_origin_2026-08-05.md`. -/
theorem e0Repr_not_injective : ¬ Function.Injective e0Repr := by
  intro hinj
  obtain ⟨x, y, hne, hrepr⟩ := mathlib_ONote_order_not_antisymm
  exact hne (congrArg ofSyn (WithTop.coe_injective (hinj (a₁ := e0Coe x) (a₂ := e0Coe y) hrepr)))

-- `Statement:` the comparator field fails: two points of the carrier are strictly ordered by its
-- order and have the same denotation, so `<` on `E0Note` does not track `<` on `Ordinal`.
example : ∃ x y : E0Note, (x < y ∨ y < x) ∧ e0Repr x = e0Repr y := by
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.1 e0Repr_not_injective
  exact ⟨x, y, lt_or_gt_of_ne hne, hxy⟩

-- `Statement:` the carrier's order is not well-founded: on raw notations `oadd 0 1 x < x`, so the
-- sequence `ω, oadd 0 1 ω, oadd 0 1 (oadd 0 1 ω), …` descends forever.
example : ¬ WellFoundedLT E0Note := by
  let c : ℕ → ONote := fun k => Nat.rec (ONote.oadd 1 1 0) (fun _ x => ONote.oadd 0 1 x) k
  have hcmp : ∀ k, ONote.cmp (c (k + 1)) (c k) = .lt := by
    intro k
    induction k with
    | zero =>
      show ONote.cmp (ONote.oadd 0 1 (ONote.oadd 1 1 0)) (ONote.oadd 1 1 0) = .lt
      decide
    | succ k ih =>
      show ONote.cmp (ONote.oadd 0 1 (c (k + 1))) (ONote.oadd 0 1 (c k)) = .lt
      simp only [ONote.cmp]
      rw [ih]
      decide
  have hne : ∀ k, c (k + 1) ≠ c k := by
    intro k
    induction k with
    | zero =>
      show ONote.oadd 0 1 (ONote.oadd 1 1 0) ≠ ONote.oadd 1 1 0
      decide
    | succ k ih => exact fun h => ih (by injection h)
  intro h
  obtain ⟨m, ⟨k, rfl⟩, hmin⟩ := h.wf.has_min (Set.range fun k => e0Coe (c k)) ⟨_, ⟨0, rfl⟩⟩
  refine hmin _ ⟨k + 1, rfl⟩ (WithTop.coe_lt_coe.2 (lt_iff_le_and_ne.2 ⟨?_, fun h' => hne k h'⟩))
  show ONote.cmp (c (k + 1)) (c k) ≠ Ordering.gt
  rw [hcmp]
  decide

/-- **`Statement:` the fiber, exhibited.** Two distinct notations with one denotation — the unfolding of
`e0Repr_not_injective`, with `1 + ω` and `ω` as the underlying witness. -/
theorem repr_collision : ∃ x y : E0Note, x ≠ y ∧ e0Repr x = e0Repr y := by
  have h := e0Repr_not_injective
  rw [Function.not_injective_iff] at h
  obtain ⟨x, y, heq, hne⟩ := h
  exact ⟨x, y, hne, heq⟩

/-- **`Statement:` a non-degenerate distribution confined to a SINGLE fiber.** There is an ordinal `o`
and a distribution on notations which is **not** a point mass, yet **every** notation in its support
denotes `o`. Uncertainty about the representation; none whatsoever about the object.

Assembled from `repr_collision` (the fiber, new here), `exists_spread_pmf` (new, in
`ZeroParadox/Information/Surprisal.lean`), and `not_pure_of_two_support` (**pre-existing** in that same
file, cited rather than re-proved).

⚠ **Do not read this as a distribution over pasts.** The support is a set of *notations*; the theorem
says they are indistinguishable by `e0Repr`, not that one preceded another. -/
theorem exists_fiber_supported_non_pure_pmf :
    ∃ (o : Ordinal) (p : PMF E0Note),
      (∀ a, p ≠ PMF.pure a) ∧ ∀ x ∈ p.support, e0Repr x = o := by
  obtain ⟨x, y, hne, hxy⟩ := repr_collision
  obtain ⟨p, hx, hy, hsub⟩ := exists_spread_pmf x y
  refine ⟨e0Repr x, p, not_pure_of_two_support hx hy hne, ?_⟩
  intro z hz
  rcases hsub hz with rfl | hz'
  · rfl
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz', ← hxy]

/-- **`Statement:` the round trip closes.** `e0Repr_not_injective` — the fence this section is built on
— is **round-tripped** through the statistical side: take the collision, spread a distribution across it,
observe that the distribution is confined to one denotation, and `confined_non_pure_refutes_injective`
returns the non-injectivity.

**Why this exists (round-4 gate finding).** The necessity theorems were stated and never *applied*, and
an unapplied theorem is one whose non-vacuity nobody has exercised. This composition exercises it: the
implication runs both ways, so the identification of "failure of faithfulness" with "room for a
confined distribution" is not an interpretation laid over the theorems — it is a round trip through
them. ⚠ **This consumes its own conclusion and is not an independent second proof** — `repr_collision` is
itself derived from `e0Repr_not_injective`. What it establishes is exactly that the converse's
hypotheses are **satisfiable at a concrete `f`**, and nothing further about `e0Repr`. Recorded as
next-touch debt: an `example` would exercise that identically without minting a second citable
`theorem` whose statement duplicates one already in this file. -/
theorem e0Repr_not_injective_via_confinement : ¬ Function.Injective e0Repr := by
  obtain ⟨x, y, hne, hxy⟩ := repr_collision
  obtain ⟨p, hx, hy, hsub⟩ := exists_spread_pmf x y
  refine confined_non_pure_refutes_injective e0Repr p (e0Repr x) ?_ ⟨x, hx, y, hy, hne⟩
  intro z hz
  rcases hsub hz with rfl | hz'
  · rfl
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz', ← hxy]

/-- **`Statement:` COINCIDENCE kind — one distribution, spread in the source and a POINT MASS in the
target, both at once.** This is the composite the KIND tag needs: `confined_map_eq_pure` alone carries
**no spread hypothesis** (it holds at `p = PMF.pure x`, where nothing coincides), so the tag is only
earned once the two halves are conjoined on a single `p`.

**Origin (Tim, 2026-08-06):** *"this zero and infinity boundary likely is going to run multiple
directions concurrently."* This is that, on one object. ⚠ The **necessity** half — *"I think it has
to"* — is NOT proved and is not claimed. -/
theorem repr_spread_source_certain_target :
    ∃ (o : Ordinal) (p : PMF E0Note), (∀ a, p ≠ PMF.pure a) ∧ p.map e0Repr = PMF.pure o := by
  obtain ⟨o, p, hnp, hconf⟩ := exists_fiber_supported_non_pure_pmf
  exact ⟨o, p, hnp, confined_map_eq_pure e0Repr p o hconf⟩

/-! ### Where the ambiguity ISN'T — both poles are faithful

**Origin (Tim, 2026-08-06): "almost like the roles of zero and infinity are reversed."** Chasing that
produced a result, and the result **did not match the prediction** — which is why it is worth stating.

**What holds.** The representation map has a singleton fiber at *each* end and is genuinely ambiguous
in between: `e0Repr_fiber_at_bot_singleton` below at the bottom, the pre-existing
`e0Repr_eq_epsilon0_iff` (§ above, same file) at the top, and `repr_collision` between them.

⚠ **At the top, EXISTENCE is stipulated**: `⊤` is *adjoined*, so `e0Repr_top` is `rfl` and there is
exactly one of it by construction. Nothing at the bottom is adjoined. **No comparative is drawn
between the two uniqueness proofs** — an earlier draft called the bottom "the earned one" on the
strength of a positivity argument that is Mathlib's, and restoring that framing after it had been
retracted in this same file is the error this note now exists to prevent.

⚠ **ONLY THE BOTTOM HALF IS NEW, and a first draft of this block claimed both.** The top half was
already proved 200 lines above — its docstring says *"the fibre of the map over ε₀ is exactly `{⊤}`"*
in those words. A duplicate `e0Repr_fiber_at_top_singleton` was written here and **deleted**; the
Trigger-0 step that would have caught it is *grep your own corpus*, and it was not run against this
file. Do not re-add it.

⚠ **THE "POLARITY REVERSAL" READING IS NOT WITNESSED HERE, and an earlier draft asserted it as a DRIFT
against complexity. That was wrong twice over.**
1. **Cross-carrier.** The complexity results (`infinitude_forces_infinite_complexity`,
   `member_cx_lt_top`, `ZeroParadox/Valuation/InfinitudeFloor.lean`) are stated over
   `[InfinitudeFloor α]`. **`E0Note` carries no such instance, and this file does not import that
   module** — the two citations were not even in scope where they were written. "The same point is
   extremal in both measures" named a point of one type and a point of another: the MC-1
   cross-category identity, retired as ill-typed.
2. **And the measure has no direction to reverse.** Ambiguity here is minimal at **both** ends. A DRIFT
   needs two measures running *opposite along* a structure; a quantity that is symmetric at the two
   poles cannot run opposite to anything.

`Reading:` **INVARIANT kind** (conjectural) — fiber cardinality is **one quantity measured at two
points of one carrier**, and it takes the same value at both, so exchanging the poles gains nothing.
That is the INVARIANT row, not COINCIDENCE (which needs two readings of one object) and not DRIFT
(which needs a direction).

⚠ **An earlier draft tagged this COINCIDENCE and borrowed the "shared shape, never an instance-of
relation" fence from § *What is NOT proved here* above. That fence belongs to a different
comparison** — `e0Repr` against the identifiability literature, which genuinely is two structures
sharing a shape and is correctly tagged with no KIND at all. The INVARIANT claim is not of that
form — it is one quantity at two points of one carrier. (The **retracted** DRIFT paragraph above did
compare two carriers, which is precisely why it failed.)

⚠ **Two fences.**
1. **No monotonicity is proved**, and none is claimed: two endpoint values plus one positive instance
   between them (`repr_collision`, whose witness is exhibited at
   `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` — the existential statement itself names no
   value, so do not attribute one to it).
2. **This closes a door.** Because the fiber at the bottom is a single point, the statistics of the
   section above lives **strictly between** the poles and cannot be seeded at the bottom by this
   route. -/

/-- **`Statement:` zero is uniquely denoted, and NO normal-form hypothesis is needed.** Structural:
`repr (oadd e n a) = ω ^ repr e * n + repr a` with `n ≥ 1`, so it is strictly positive.

**Prior art — and the positivity argument is MATHLIB'S, not this file's.** `ONote.oadd_pos (e n a) :
0 < oadd e n a` together with `ONote.lt_def : x < y ↔ repr x < repr y`
(`Mathlib/SetTheory/Ordinal/Notation.lean`) *is* `0 < repr (oadd e n a)`, so this derives from the
library in a few lines. Corpus citations of `oadd_pos` before this one: **none**. The hand proof is
kept (identical footprint measured, so no purity reason to swap) and the standard lemma is cited —
the `CovBy` pattern. ⚠ An earlier draft called this result "the earned one" on the strength of *"it
needs a positivity argument"*; the argument is Mathlib's and was uncited.

`ONote.repr_inj` gives injectivity but requires `NF` on **both** arguments; no `repr = 0`
characterization was located in the pin as of `9dffe26` (`exact?` closes neither the iff nor the bare
positivity form). This is the one point where faithfulness is free. -/
theorem onote_repr_eq_zero_iff (x : ONote) : x.repr = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases x with
    | zero => rfl
    | oadd e n a =>
      exfalso
      rw [ONote.repr] at h
      have hmul := Ordinal.left_eq_zero_of_add_eq_zero h
      rcases mul_eq_zero.mp hmul with hz | hz
      · exact absurd hz (Ordinal.opow_pos _ Ordinal.omega0_pos).ne'
      · have : (n : ℕ) = 0 := by exact_mod_cast hz
        exact absurd this n.pos.ne'
  · rintro rfl; rfl

/-- **`Statement:` the fiber over the BOTTOM is a singleton.** Zero representational ambiguity at the
floor. The adjoined top is excluded because it denotes the top value, which is
strictly positive — by Mathlib's own `Ordinal.epsilon_pos` (`Mathlib/SetTheory/Ordinal/Veblen.lean`),
adopted rather than routing through the corpus's `epsilon0_ne_zero` canary, which would have cost an
import for a fact the library already states. -/
theorem e0Repr_fiber_at_bot_singleton :
    {x : E0Note | e0Repr x = 0} = {e0Coe 0} := by
  ext x
  constructor
  · intro hx
    induction x using WithTop.recTopCoe with
    | top => exact absurd hx (Ordinal.epsilon_pos 0).ne'
    | coe y =>
      simp only [Set.mem_setOf_eq, e0Repr] at hx
      simp only [Set.mem_singleton_iff, e0Coe]
      congr 1
      have := (onote_repr_eq_zero_iff (ofSyn y)).mp hx
      rw [← this]; rfl
  · rintro rfl; rfl

end ZeroParadox

/-! ## Axiom Purity Check — this block IS the deliverable

The two sides of the interface, measured. Observed: the carrier side is choice-free, ranging from no
axioms at all up to `[propext, Quot.sound]`; the map side is uniformly
`[propext, Classical.choice, Quot.sound]`. **The per-declaration numbers live HERE and nowhere else** —
`ZeroParadox/Ordinal/PricedInterface.md` states only the shape, deliberately, because an enumeration
duplicated into prose is what went stale once already. If this block ever prints something outside
that shape, the ride-along is wrong and must be corrected to match the instrument — the instrument is
the deliverable. -/

section PurityCheck
open ZeroParadox

-- Constructive side: the carrier, its decidable order, and the tower operator on it.
#print axioms E0Note
#print axioms e0Coe
#print axioms e0DecidableLE
#print axioms e0DecidableLT
#print axioms e0DecidableEq
#print axioms e0Coe_lt_top
#print axioms e0_le_top
#print axioms e0OmegaPow
#print axioms e0OmegaPow_top
#print axioms e0OmegaPow_coe
#print axioms e0OmegaPow_fixedpoint_iff

-- The crossing, and statements mentioning `Ordinal`'s order. This is where the price is paid.
#print axioms repr_lt_epsilon0
#print axioms repr_surj_below_epsilon0
#print axioms e0Repr
#print axioms e0Repr_top
#print axioms e0Repr_coe
#print axioms e0Repr_le_epsilon0
#print axioms e0Repr_eq_epsilon0_iff
#print axioms e0Repr_not_injective
#print axioms repr_collision
#print axioms exists_fiber_supported_non_pure_pmf
#print axioms e0Repr_not_injective_via_confinement
#print axioms repr_spread_source_certain_target
#print axioms onote_repr_eq_zero_iff
#print axioms e0Repr_fiber_at_bot_singleton

-- The ε₀-producing operations themselves, measured here because this file already imports Veblen.
-- ZP-N's prose names these (with `typein` and `omega0`, printed in
-- `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`) as where `Classical.choice` actually enters
-- Mathlib's ordinals. Printed rather than asserted: naming a site without measuring it is exactly
-- the error ZP-N v1.0 made, and a claim about where choice lives should be reproducible.
#print axioms Ordinal.nfp
#print axioms Ordinal.deriv
#print axioms Ordinal.epsilon
end PurityCheck
