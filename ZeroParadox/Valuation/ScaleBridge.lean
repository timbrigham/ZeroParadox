import ZeroParadox.Valuation.Scale
import Mathlib.Tactic

/-!
# ZPJ — Scale Bridge: AFA Content from Valuation Without ZPSemilattice

## Engineer's Take

This file represents a common ancestor between semilattice and p-adic valuation
on our continuing hunt for the most basic structures to hold the bottom element.

## The question

ZeroParadox/Valuation/Scale.lean defines ValuationStructure over `[ZPSemilattice L]`, but the four
axioms (scale_bot, val_bot, val_unique, val_scale) only ever use `bot` — the
join operation ⊔ never appears. This means ZPSemilattice is an over-strong
constraint, and ℤ_[2] cannot be a formal ValuationStructure instance despite
satisfying all four axioms (proved as standalone theorems in ZeroParadox/Valuation/Scale.lean §V).

This file tests the conjecture that the constraint is an encoding artefact, not
a mathematical gap. It defines ValBridge — the same four axioms with `bot` as a
plain field rather than a ZPSemilattice bottom — and builds a formal ℤ_[2]
instance using the theorems already proved in ZeroParadox/Valuation/Scale.lean.

If the instance builds and the AFA content chain follows, the formal bridge is
complete: ℤ_[2] carries the LATTICE SHADOW of AFA content as a theorem of ZFC, rather
than as an import from Aczel. ⚠ Read that with the fence
ZeroParadox/Computability/SelfApp.lean applies to the same gloss: what is proved here is that the
scale map has `bot` as its unique fixed point (`z2_selfMem_singleton`), which is the one-relation
shadow of the Quine atom — NOT literal set-membership `⊥ ∈ ⊥`, which is a statement of the ZF+AFA
metatheory and is not expressible on this carrier.

## The chain

  ValBridge (scale + val axioms, bot as plain field)
    → scale_ne_fixed_free
    → scale_unique_fp_free
    → selfMem_eq_singleton_free  ({x | scale x = x} = {bot})

This is the same chain as ZeroParadox/Valuation/Scale.lean §II–IV, without the ZPSemilattice dependency.
-/

namespace ZeroParadox

open ZeroParadox

/-! ## § I. ValBridge — The Unconstrained Typeclass -/

/-- Same four axioms as ValuationStructure, but `bot` is a plain field.
    No ZPSemilattice required — the join operation ⊔ never appears in any axiom. -/
-- [ZP-CUSTOM] replaces: ValuationStructure (ZeroParadox/Valuation/Scale.lean) | reason: ValuationStructure required [ZPSemilattice L] but the join operation ⊔ never appears in any of its four axioms — the constraint was an encoding artefact. ValBridge carries the same four axioms with bot as a plain field, allowing ℤ_[2] (a ring, not a ZPSemilattice) to be a formal instance. Unifies both tracks under one ancestor.
class ValBridge (L : Type*) where
  bot : L
  scale : L → L
  val : L → ℕ∞
  scale_bot : scale bot = bot
  val_bot : val bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = bot
  val_scale : ∀ x : L, x ≠ bot → val (scale x) = val x + 1

/-! ## § II. Derived Theorems — Same Proofs, No ZPSemilattice -/

variable {L : Type*} [ValBridge L]

/-- val x ≠ ⊤ when x ≠ bot — contrapositive of val_unique. -/
theorem val_finite_free (x : L) (hx : x ≠ ValBridge.bot) : ValBridge.val x ≠ ⊤ :=
  fun h => hx (ValBridge.val_unique x h)

/-- scale x ≠ x for x ≠ bot.
    Proof: val (scale x) = val x + 1 ≠ val x (since val x is finite). -/
theorem scale_ne_fixed_free (x : L) (hx : x ≠ ValBridge.bot) : ValBridge.scale x ≠ x := by
  intro hfp
  have hfin := val_finite_free x hx
  have hval := ValBridge.val_scale x hx
  rw [hfp] at hval
  rcases hv : ValBridge.val x with _ | n
  · exact hfin hv
  · rw [hv] at hval
    change (n : ℕ∞) = (n : ℕ∞) + 1 at hval
    exact absurd hval.symm (by exact_mod_cast Nat.succ_ne_self n)

/-- ValBridge.bot is the unique fixed point of scale. -/
theorem scale_unique_fp_free (x : L) (hfp : ValBridge.scale x = x) : x = ValBridge.bot := by
  by_contra hne
  exact scale_ne_fixed_free x hne hfp

/-- {x | scale x = x} = {bot} — the lattice shadow of AFA uniqueness. Its measured footprint is in
    the purity block below; no purity claim is made here. -/
theorem selfMem_eq_singleton_free :
    {x : L | ValBridge.scale x = x} = ({ValBridge.bot} : Set L) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun h => scale_unique_fp_free x h, fun h => h ▸ ValBridge.scale_bot⟩

/-! ## § III. ℤ_[2] Instance — The Formal Bridge -/

/-- ℤ_[2] with scale = ×2 and val = v₂ is a ValBridge.
    bot = 0. All four axioms proved in ZeroParadox/Valuation/Scale.lean §V as standalone theorems.
    This is the formal instance that ZeroParadox/Valuation/Scale.lean could not build because
    ℤ_[2] is not a ZPSemilattice — showing the ZPSemilattice constraint
    was an encoding artefact, not a mathematical requirement. -/
-- [ZP-CUSTOM] instance: ValBridge ℤ_[2] | reason: no ZPSemilattice ℤ_[2] is defined — its ring structure supplies no natural join with 0 as bottom — so ℤ_[2] cannot be a ValuationStructure instance, which requires one. (Being a ring is not itself the obstruction: nothing in ZPSemilattice's axioms mentions a ring operation, and ZPSemilattice ℕ exists.) ValBridge's bot-as-plain-field design drops the requirement, which the four axioms never used anyway. All four delegate directly to theorems proved in ZeroParadox/Valuation/Scale.lean §V (q2Scale_bot, q2Val_bot, q2Val_unique, q2Val_scale).
noncomputable instance instZ2ValBridge : ValBridge ℤ_[2] where
  bot := 0
  scale := (2 * ·)
  val := q2Val
  scale_bot := q2Scale_bot
  val_bot := q2Val_bot
  val_unique := q2Val_unique
  val_scale := q2Val_scale

/-! ## § IV. AFA Content for ℤ_[2] — The Closed Bridge -/

/-- The unique fixed point of ×2 in ℤ_[2] is 0.
    Formal consequence of ValBridge; no sorry, no ZPSemilattice. -/
theorem z2_scale_unique_fp (x : ℤ_[2]) (h : 2 * x = x) : x = 0 :=
  scale_unique_fp_free x h

/-- {x : ℤ_[2] | 2 * x = x} = {0} — AFA self-membership content in ℤ_[2].
    A theorem of ZFC (via Mathlib's p-adic library). No AFA import. -/
theorem z2_selfMem_singleton :
    {x : ℤ_[2] | 2 * x = x} = ({0} : Set ℤ_[2]) :=
  selfMem_eq_singleton_free

/-! ## § V. Unification — ZPSemilattice+ValuationStructure is a ValBridge

    Any type carrying both ZPSemilattice and ValuationStructure satisfies ValBridge.
    Combined with the ℤ_[2] instance above, this makes ValBridge the common ancestor:
    both tracks are now instances of one structure, not parallel analogies.

    Consequence: every ValBridge theorem (scale_unique_fp_free, selfMem_eq_singleton_free,
    etc.) applies uniformly to abstract ZP semilattice types AND to ℤ_[2] — a single
    proof serves both. -/

/-- Any ZPSemilattice with a ValuationStructure is a ValBridge.
    Proof: all four fields come directly from ZPSemilattice.bot and ValuationStructure. -/
instance toValBridge (L : Type*) [ZeroParadox.ZPSemilattice L]
    [ValuationStructure L] : ValBridge L where
  bot := ZeroParadox.ZPSemilattice.bot
  scale := ValuationStructure.scale
  val := ValuationStructure.val
  scale_bot := ValuationStructure.scale_bot
  val_bot := ValuationStructure.val_bot
  val_unique := ValuationStructure.val_unique
  val_scale := ValuationStructure.val_scale

/-- Both tracks produce the same singleton theorem via a single ValBridge proof.
    For any ZPSemilattice L with ValuationStructure: {x | scale x = x} = {bot}. -/
theorem zp_selfMem_singleton (L : Type*) [ZeroParadox.ZPSemilattice L]
    [ValuationStructure L] :
    {x : L | ValuationStructure.scale x = x} =
      ({ZeroParadox.ZPSemilattice.bot} : Set L) :=
  selfMem_eq_singleton_free

/-! ## § VI. NO-GO gauge — what FAILS to be a `ValBridge`

    A requirements class carries information only where something fails to be a member, so this
    section records the failure condition instead of leaving it to be rediscovered at a use site.

    **The membership question is settled exactly** (`valBridge_nonempty_iff`):

      `Nonempty (ValBridge α) ↔ Infinite α ∨ (Nonempty α ∧ Subsingleton α)`

    The forcing half is `valBridge_forces_infinite`: from any `x ≠ bot` the scale orbit
    `scale^[k] x` never reaches `bot` and its valuation climbs by exactly one per step, so
    `k ↦ scale^[k] x` is injective. The one-point carrier is a member because `val_scale` is guarded
    by `x ≠ bot` and is vacuous there (`trivialValBridge`). Both converse directions are built:
    `nonempty_valBridge_of_infinite` places the orbit along an ℕ-embedding, and
    `nonempty_valBridge_of_inhabited_subsingleton` is the degenerate case.

    So the non-members are the finite carriers with two or more points, and also `Empty` — a
    subsingleton, but `bot : L` is a field, so a carrier is always inhabited. `valBridge_bool_isEmpty`
    records the smallest inhabited non-member.

    ⚠ **`[ValBridge L]` therefore constrains cardinality and nothing else.** It does not distinguish
    `instZ2ValBridge` from arbitrary bookkeeping, because `nonempty_valBridge_of_infinite` equips
    *any* infinite carrier. The substance of the ℤ_[2] instance is in its chosen `scale` and `val`,
    never in membership — do not cite membership as evidence that a witness is non-degenerate.

    ### Prior art

    **In this corpus, and it is the general form:** `orbit_dichotomy`
    (ZeroParadox/Order/OrbitDichotomy.lean), whose file header already names the framework's scale
    map as the checkable branch of exactly this argument. Cite that for the general pattern.
    ⚠ **`valBridge_forces_infinite` is NOT an instance of it.** That theorem assumes
    `Function.Injective s`; `ValBridge` does not supply it — take `L = {bot} ⊎ (ℕ × Bool)` with
    `val (n, b) = n` and `scale (n, b) = (n+1, false)`, which satisfies all four axioms and collapses
    `(0, true)` with `(0, false)`. `val_scale` buys injectivity *along an orbit*, which is all the
    argument consumes.

    The two-element case is older still: ZeroParadox/Settheory/OntBridge.lean records that
    `OntologicalStates` cannot satisfy `val_scale`, "a finite two-element type has no room for val to
    strictly increase".

    **Outside the corpus**, the owning branch is valuation theory, whose statements use multiplicative
    structure this class drops — **F.-V. Kuhlmann, *Valuation Theory*, Ch. 4, Corollary 4.13**: *"The
    only fields which do not admit non-trivial places are precisely the algebraic extensions of finite
    fields."* ⚠ The *setting* here is more general; the *results* are incomparable, since `F̄_p` is
    infinite and this section says nothing about it. Credit points outward.

    For the degenerate half, read the prior-art paragraph of
    ZeroParadox/Valuation/InfinitudeFloor.lean, which cites Burris & Sankappanavar on why a
    non-degeneracy condition must be an inequation rather than a further equation. ⚠ Its neighbouring
    "trivial algebras satisfy any quasi-identity" does **not** apply here: `val_scale`'s antecedent
    `x ≠ bot` is a negated atom, and a quasi-identity admits only positive ones.

    Standard names, for searching: `(L, scale)` is a **mono-unary algebra** (a **unar**), and the
    mechanism exhibiting `ℕ ↪ L` is **Dedekind-infinite**.

    `Reading:` **COINCIDENCE** — the characterisation has the same shape as
    `infinitudeFloor_nonempty_iff_infinite` (ZeroParadox/Valuation/InfinitudeFloor.lean), which pins
    that class to exactly `Infinite`; the valuation climbing without bound along the orbit and the
    floor carrying the value ⊤ read as the framework's zero and infinity poles on one carrier. **A
    reading, carrying no declaration and no import here.** The membership transfer would be witnessed
    by an arbitrary ℕ-embedding whose `floor` and `cx` are unrelated to `bot` and `val`, so it would
    not witness the coincidence it names; the canonical witness — `member` the scale orbit, `cx` the
    valuation — would, and is not built. -/

/-- The scale of a non-bottom point is never the bottom: it would force `val x = ⊤`, and
    `val_unique` then puts `x` at the bottom. -/
theorem scale_ne_bot_free (x : L) (hx : x ≠ ValBridge.bot) :
    ValBridge.scale x ≠ ValBridge.bot := by
  intro h
  have hval := ValBridge.val_scale x hx
  rw [h, ValBridge.val_bot] at hval
  have hx' : ValBridge.val x = ⊤ := by
    rcases WithTop.add_eq_top.mp hval.symm with h1 | h1
    · exact h1
    · exact absurd h1 ENat.one_ne_top
  exact hx (ValBridge.val_unique x hx')

/-- The scale orbit of a non-bottom point never reaches the bottom, and its valuation climbs by
    exactly one at each step. -/
theorem orbit_ne_bot_and_val_free (x : L) (hx : x ≠ ValBridge.bot) (k : ℕ) :
    ValBridge.scale^[k] x ≠ ValBridge.bot ∧
      ValBridge.val (ValBridge.scale^[k] x) = ValBridge.val x + k := by
  induction k with
  | zero => simpa using hx
  | succ n ih =>
      obtain ⟨hne, hv⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨scale_ne_bot_free _ hne, ?_⟩
      rw [ValBridge.val_scale _ hne, hv]
      push_cast
      ring

/-- **The gauge.** A `ValBridge` carrier holding any point other than `bot` is infinite: the scale
    orbit of that point embeds ℕ. -/
theorem valBridge_forces_infinite [Nontrivial L] : Infinite L := by
  obtain ⟨x, hx⟩ := exists_ne (ValBridge.bot : L)
  have hfin : ValBridge.val x ≠ ⊤ := val_finite_free x hx
  refine Infinite.of_injective (fun k : ℕ => ValBridge.scale^[k] x) ?_
  intro j k hjk
  dsimp only at hjk
  have hj := (orbit_ne_bot_and_val_free x hx j).2
  have hk := (orbit_ne_bot_and_val_free x hx k).2
  rw [hjk, hk] at hj
  exact Nat.cast_injective (WithTop.add_left_cancel hfin hj.symm)

/-- The gauge as an emptiness statement: a finite carrier with more than one point admits no
    `ValBridge`, since membership would make it infinite. -/
theorem no_valBridge_of_finite (N : Type*) [Finite N] [Nontrivial N] : IsEmpty (ValBridge N) :=
  ⟨fun I => by
    haveI := I
    haveI := @valBridge_forces_infinite N I _
    exact not_finite N⟩

/-- The smallest concrete non-member: two points, a bottom and one other, and no valuation can
    satisfy the four axioms. -/
theorem valBridge_bool_isEmpty : IsEmpty (ValBridge Bool) := no_valBridge_of_finite Bool

/-- The one-point carrier IS a member, so the gauge above is sharp rather than merely a bound:
    `val_scale` is guarded by `x ≠ bot` and no point of `Unit` clears the guard. -/
@[reducible] def trivialValBridge : ValBridge Unit where
  bot := ()
  scale := id
  val := fun _ => ⊤
  scale_bot := rfl
  val_bot := rfl
  val_unique := fun x _ => Subsingleton.elim x ()
  val_scale := fun x hx => absurd (Subsingleton.elim x ()) hx

/-- The same gauge for `ValuationStructure`, through the `toValBridge` instance of § V — the
    ZPSemilattice-constrained class inherits it with no separate argument. -/
theorem valuationStructure_forces_infinite (M : Type*) [ZeroParadox.ZPSemilattice M]
    [ValuationStructure M] [Nontrivial M] : Infinite M :=
  valBridge_forces_infinite

/-- The converse on the infinite side: **every** infinite carrier admits a `ValBridge`. Place the
    orbit along an ℕ-embedding `e`, take `e 0` as the bottom, give `e (n+1)` valuation `n`, and send
    every other point to valuation `0`; `scale` then steps one rung up the embedding. -/
theorem nonempty_valBridge_of_infinite (α : Type*) [Infinite α] : Nonempty (ValBridge α) := by
  classical
  set e : ℕ ↪ α := Infinite.natEmbedding α with he
  set k : α → ℕ := fun x => if h : ∃ n, e (n + 1) = x then h.choose else 0 with hk
  have hke : ∀ m : ℕ, k (e (m + 1)) = m := by
    intro m
    have h : ∃ n, e (n + 1) = e (m + 1) := ⟨m, rfl⟩
    simp only [hk, dif_pos h]
    have := e.injective h.choose_spec
    omega
  have hne : ∀ m : ℕ, e (m + 1) ≠ e 0 := by
    intro m hcon
    have := e.injective hcon
    omega
  exact ⟨{ bot := e 0
           scale := fun x => if x = e 0 then e 0 else e (k x + 2)
           val := fun x => if x = e 0 then ⊤ else (k x : ℕ∞)
           scale_bot := by simp
           val_bot := by simp
           val_unique := by
             intro x hx
             by_contra hcon
             rw [if_neg hcon] at hx
             exact (ENat.coe_ne_top _) hx
           val_scale := by
             intro x hx
             have hs : (if x = e 0 then e 0 else e (k x + 2)) = e ((k x + 1) + 1) := by
               rw [if_neg hx]
             rw [hs, if_neg (hne _), hke, if_neg hx]
             push_cast
             ring }⟩

/-- The converse on the degenerate side, stated for a general carrier rather than for `Unit`. -/
theorem nonempty_valBridge_of_inhabited_subsingleton (α : Type*) [Nonempty α] [Subsingleton α] :
    Nonempty (ValBridge α) :=
  ⟨{ bot := Classical.arbitrary α
     scale := id
     val := fun _ => ⊤
     scale_bot := rfl
     val_bot := rfl
     val_unique := fun x _ => Subsingleton.elim x _
     val_scale := fun x hx => absurd (Subsingleton.elim x _) hx }⟩

/-- **The characterisation.** `ValBridge` constrains the carrier's cardinality and nothing else:
    the members are exactly the infinite carriers and the inhabited subsingletons. -/
theorem valBridge_nonempty_iff (α : Type*) :
    Nonempty (ValBridge α) ↔ (Infinite α ∨ (Nonempty α ∧ Subsingleton α)) := by
  constructor
  · rintro ⟨I⟩
    haveI := I
    haveI : Nonempty α := ⟨ValBridge.bot⟩
    by_cases hs : Subsingleton α
    · exact Or.inr ⟨inferInstance, hs⟩
    · haveI : Nontrivial α := not_subsingleton_iff_nontrivial.mp hs
      exact Or.inl valBridge_forces_infinite
  · rintro (hi | ⟨hn, hs⟩)
    · haveI := hi; exact nonempty_valBridge_of_infinite α
    · haveI := hn; haveI := hs; exact nonempty_valBridge_of_inhabited_subsingleton α

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms scale_ne_fixed_free
#print axioms scale_unique_fp_free
#print axioms selfMem_eq_singleton_free
#print axioms z2_scale_unique_fp
#print axioms z2_selfMem_singleton
#print axioms toValBridge
#print axioms zp_selfMem_singleton

-- § VI, the NO-GO gauge.
#print axioms scale_ne_bot_free
#print axioms orbit_ne_bot_and_val_free
#print axioms valBridge_forces_infinite
#print axioms no_valBridge_of_finite
#print axioms valBridge_bool_isEmpty
#print axioms trivialValBridge
#print axioms valuationStructure_forces_infinite
#print axioms nonempty_valBridge_of_infinite
#print axioms nonempty_valBridge_of_inhabited_subsingleton
#print axioms valBridge_nonempty_iff

end PurityCheck
