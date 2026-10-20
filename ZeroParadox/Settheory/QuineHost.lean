import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.SetTheoryAFA
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Quine-Host Requirements — the AFA fragment the framework actually needs

## Engineer's Take

So this one is an interesting one. In order to connect AFA and ZFC directly, it's
impossible to do due to type mismatches. What it is possible to do is make a list of
requirements that AFA satisfies, or that in theory another framework could fill, and
match based on those attributes. That's my computer programmer logic from my day job
slipping in.

---

## Formal Overview (AI-assisted)

The framework's set-theoretic commitment (CC-2) is a fragment of what a host theory supplies,
not the full Anti-Foundation Axiom (AFA, "every graph has a unique decoration"): a Quine atom
⊥ = {⊥}, ⊥'s only member being ⊥, that is the only reflexive element (x = {x}). That is AFA's
own profile: AFA allows at most one solution of x = {x} (Aczel 1988, p. 19), while a* = {a, a*}
is self-membered for every a (Examples 1.5–1.6, pp. 7–8; 0* = {∅, 0*}). Two typeclasses, which
are incomparable (§ VII):

- `QuineAtomHost` — the commitment: (Y') `bot_mem_iff`, ⊥ = {⊥}; (Z') `reflexive_unique`.
- `QuineHost` — ⊥ ∈ ⊥ and the only self-membered element is ⊥. AFA's membership fails its
  (Z), since 0* ∈ 0*; the § VI encoding, whose membership relates no element to any other, meets it.

(X) Foundation-freeness is not assumed: either class forces it (`quineHost_not_wellFounded`,
`quineAtomHost_not_wellFounded`). ZFC + Foundation fails both (`zfSet_no_quine_bottom`,
`zfSet_no_singleton_bottom`). Boffa's BA₁ gives a proper class of reflexive sets (Aczel 1988,
Prop. 5.1, p. 57), so fails (Z'); toy model `boffa_fails_reflexive_unique`. AFA's pattern, as a
three-element toy with real ∈, meets `QuineAtomHost` and no `QuineHost` (§ VII); a model of the
pattern, not of AFA. Both classes are met on every inhabited carrier (NO-GO gauges, § I, § VII), so
realizability alone is uninformative. What remains a *modeling commitment*: that (Y') and (Z')
are the right requirements; AFA is a theory meeting them, not the commitment. (Where
AFA-specific content is used elsewhere, e.g. decoration uniqueness in
`ZeroParadox/Settheory/APG.lean`, it is proved on its own terms.)

## Structure

- § I   `QuineHost`: ⊥ ∈ ⊥ and uniqueness among self-members
- § II  (X) is forced — a `QuineHost` is Foundation-free
- § III Foundation (ZFSet) fails ⊥ ∈ ⊥
- § IV  The total relation: self-membership without uniqueness
- § V   A one-atom model
- § VI  The framework's `AFAStructure` encoding
- § VII `QuineAtomHost`: ⊥ = {⊥} and uniqueness among reflexive elements; the two classes compared
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. `QuineHost` -/

/-- `Statement:` a membership relation `mem` and a point `bot` with (Y) `mem bot bot` and (Z) every
    self-membered element is `bot`. `Reading:` (Y) is ⊥ ∈ ⊥, weaker than ⊥ = {⊥}; (Z) is
    uniqueness among self-members, which AFA's membership does not meet (§ VII). -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's ZFSet carries Foundation (ZFSet.mem_wf), which forbids x ∈ x, so it cannot host a self-membered element; and no Mathlib typeclass abstracts "a membership relation whose bottom is self-membered and the only self-member." QuineHost encodes that (fields bot_selfMem/selfMem_unique); AFA's membership fails its uniqueness field, and the framework's requirement is QuineAtomHost (§ VII). Distinct from the lattice-level AFAStructure in SetTheoryAFA.lean.
class QuineHost (L : Type*) where
  /-- The host's membership relation. -/
  mem : L → L → Prop
  /-- The distinguished bottom element. -/
  bot : L
  /-- (Y) The bottom is self-membered: `mem bot bot`. -/
  bot_selfMem : mem bot bot
  /-- (Z) Uniqueness: the only self-membered element is the bottom. -/
  selfMem_unique : ∀ x : L, mem x x → x = bot

-- Statement: CONTROL: (Y) and (Z) do not give ⊥ = {⊥}. On `Bool` with `mem x y := y = false`
-- (every `x` is a member of `false`), ⊥ is `false`, both fields hold, and `true` is a second
-- member of ⊥.
example : ∃ H : QuineHost Bool, H.bot = false ∧ H.mem true H.bot :=
  ⟨{ mem := fun _ y => y = false, bot := false, bot_selfMem := rfl,
     selfMem_unique := fun _ h => h }, rfl, rfl⟩

-- Statement: NO-GO gauge: every type with a point `b` carries a `QuineHost`
-- (`mem x y := x = b ∧ y = b`), and the empty type carries none.
example {C : Type} (b : C) : QuineHost C :=
  ⟨fun x y => x = b ∧ y = b, b, ⟨rfl, rfl⟩, fun _ h => h.1⟩
example : IsEmpty (QuineHost Empty) := ⟨fun H => H.bot.elim⟩

/-! ## § II. (X) is forced — a `QuineHost` is Foundation-free -/

/-- `Statement:` a `QuineHost`'s membership is not well-founded: (Y) is a self-loop at `bot`, and
    a well-founded relation has none (`wf_no_selfloop`); one way. -/
theorem quineHost_not_wellFounded (L : Type*) [QuineHost L] :
    ¬ WellFounded (QuineHost.mem : L → L → Prop) :=
  fun h => wf_no_selfloop h QuineHost.bot QuineHost.bot_selfMem

/-- `Statement:` in a `QuineHost`, an element is self-membered iff it is the bottom. -/
theorem quineHost_selfMem_iff (L : Type*) [QuineHost L] (x : L) :
    QuineHost.mem x x ↔ x = QuineHost.bot :=
  ⟨QuineHost.selfMem_unique x, fun h => h ▸ QuineHost.bot_selfMem⟩

/-! ## § III. Foundation fails ⊥ ∈ ⊥ -/

/-- `Statement:` no `ZFSet` is self-membered (`no_quine_atom`, Foundation via `ZFSet.mem_wf`), so
    with `mem = (· ∈ ·)` no `ZFSet` meets `QuineHost`'s (Y). -/
theorem zfSet_no_quine_bottom : ¬ ∃ b : ZFSet, b ∈ b :=
  fun ⟨b, hb⟩ => no_quine_atom b hb

/-! ## § IV. The total relation: self-membership without uniqueness -/

/-- `Statement:` the total relation on `Bool`: every element is a member of every element.
    `Reading:` it models self-membership without uniqueness. It does not model Boffa's reflexive
    sets, x = {x}: here no element is its own only member (`boffa_fails_singleton`, § VII). -/
def BoffaMem : Bool → Bool → Prop := fun _ _ => True

/-- `Statement:` every element is self-membered under `BoffaMem`. -/
theorem boffaMem_all_selfMem (x : Bool) : BoffaMem x x := trivial

/-- `Statement:` under `BoffaMem` no single element is the only self-membered one: `true` and
    `false` are both self-membered and distinct. So `QuineHost`'s (Y) does not give its (Z). -/
theorem boffa_fails_unique : ¬ ∃ b : Bool, ∀ x : Bool, BoffaMem x x → x = b := by
  rintro ⟨b, hb⟩
  have h1 : true = b := hb true trivial
  have h2 : false = b := hb false trivial
  exact Bool.noConfusion (h1.trans h2.symm)

/-! ## § V. A one-atom model -/

/-- `Statement:` two elements, `bot` and `other`. -/
inductive OneAtom where
  | bot
  | other

instance : QuineHost OneAtom where
  mem := fun x y => x = OneAtom.bot ∧ y = OneAtom.bot
  bot := OneAtom.bot
  bot_selfMem := ⟨rfl, rfl⟩
  selfMem_unique := fun _ hx => hx.1

-- Statement: in this model the only member of ⊥ is ⊥.
example (x : OneAtom) (h : QuineHost.mem x OneAtom.bot) : x = OneAtom.bot := h.1

/-- `Statement:` the one-atom model's membership is not well-founded. -/
theorem oneAtom_not_wellFounded :
    ¬ WellFounded (QuineHost.mem : OneAtom → OneAtom → Prop) :=
  quineHost_not_wellFounded OneAtom

/-! ## § VI. The framework's `AFAStructure` encoding -/

/-- `Statement:` an `AFAStructure` gives a `QuineHost` with `mem x y := selfMem x ∧ x = y`;
    (Y) is `bot_self_mem` and (Z) is `quine_unique`. `Reading:` this `mem` relates no element to
    any other, so it is not AFA's ∈, under which (Z) fails (§ VII). -/
@[reducible]
def afaStructure_isQuineHost (L : Type*) [ZPSemilattice L] [AFAStructure L] :
    QuineHost L where
  mem := fun x y => AFAStructure.selfMem x ∧ x = y
  bot := bot
  bot_selfMem := ⟨AFAStructure.bot_self_mem, rfl⟩
  selfMem_unique := fun x hx =>
    AFAStructure.quine_unique x bot hx.1 AFAStructure.bot_self_mem

-- Statement: that `mem` relates no element to any other.
example (L : Type) [ZPSemilattice L] [AFAStructure L] (x y : L)
    (h : (afaStructure_isQuineHost L).mem x y) : x = y := h.2

/-! ## § VII. `QuineAtomHost` — ⊥ = {⊥} and uniqueness among reflexive elements

Which earlier results use which class: `quineHost_not_wellFounded`, `quineHost_selfMem_iff` and
`afaStructure_isQuineHost` concern `QuineHost`; `zfSet_no_quine_bottom` and `boffa_fails_unique`
name neither class. -/

/-- `Statement:` a membership relation `mem` and a point `bot` with (Y') the members of `bot` are
    exactly `bot` (⊥ = {⊥}) and (Z') every element that is its own only member is `bot`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: a membership relation with ⊥ = {⊥} and a unique reflexive
-- element (AFA's profile); Mathlib's ZFSet carries Foundation and cannot host it.
class QuineAtomHost (L : Type*) where
  /-- The host's membership relation. -/
  mem : L → L → Prop
  /-- The distinguished bottom element. -/
  bot : L
  /-- (Y') ⊥ = {⊥}: the members of the bottom are exactly the bottom. -/
  bot_mem_iff : ∀ y : L, mem y bot ↔ y = bot
  /-- (Z') Uniqueness among reflexive elements (x = {x}). -/
  reflexive_unique : ∀ x : L, (∀ y, mem y x ↔ y = x) → x = bot

/-- `Statement:` a `QuineAtomHost`'s membership is not well-founded, since (Y') gives
    `mem bot bot`; one way. -/
theorem quineAtomHost_not_wellFounded (L : Type*) [QuineAtomHost L] :
    ¬ WellFounded (QuineAtomHost.mem : L → L → Prop) :=
  fun h => wf_no_selfloop h QuineAtomHost.bot ((QuineAtomHost.bot_mem_iff _).2 rfl)

/-! NO-GO gauge — only the EMPTY carrier fails `QuineAtomHost`: on any point `b`,
`mem x y := x = b ∧ y = b` meets every field (`trivialQuineAtomHost`). Membership is informative
only with the `mem` named. -/

/-- `Statement:` on any type with a point `b`, `mem x y := x = b ∧ y = b` is a `QuineAtomHost`. -/
@[reducible]
def trivialQuineAtomHost {C : Type*} (b : C) : QuineAtomHost C where
  mem x y := x = b ∧ y = b
  bot := b
  bot_mem_iff _ := ⟨And.left, fun h => ⟨h, rfl⟩⟩
  reflexive_unique x hx := ((hx x).2 rfl).1

-- Statement: and the empty type is not a member: the `bot` field demands a point.
example : IsEmpty (QuineAtomHost Empty) := ⟨fun S => S.bot.elim⟩

-- Statement: AFA's pattern, as a finite toy (not a model of AFA): on `Fin 3` read as Ω, ∅, 0*,
-- with Ω ∈ Ω, 0* ∈ 0* and ∅ ∈ 0* (Aczel 1988, Ex. 1.3 and 1.5, pp. 6–7), some `QuineAtomHost`
-- has this membership with ⊥ = Ω, and no `QuineHost` has it, since Ω and 0* are both self-members.
example :
    (∃ H : QuineAtomHost (Fin 3), H.bot = 0 ∧
      H.mem = fun a b => (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 2) ∨ (a = 1 ∧ b = 2)) ∧
    ¬ ∃ H : QuineHost (Fin 3),
      H.mem = fun a b => (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by
  refine ⟨⟨QuineAtomHost.mk (fun a b => (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 2) ∨ (a = 1 ∧ b = 2)) 0
    (by decide) (by decide), rfl, rfl⟩, ?_⟩
  rintro ⟨H, hH⟩
  have h0 := H.selfMem_unique 0 (by rw [hH]; exact Or.inl ⟨rfl, rfl⟩)
  have h2 := H.selfMem_unique 2 (by rw [hH]; exact Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact absurd (h0.trans h2.symm) (by decide)

-- Statement: the other direction: the `Bool` control of § I is a `QuineHost`, and no
-- `QuineAtomHost` has its membership. So neither class contains the other.
example : ∃ H : QuineHost Bool, ¬ ∃ S : QuineAtomHost Bool, S.mem = H.mem :=
  ⟨{ mem := fun _ y => y = false, bot := false, bot_selfMem := rfl,
     selfMem_unique := fun _ h => h }, fun ⟨S, hS⟩ => by
    have ht := S.bot_mem_iff true
    have hf := S.bot_mem_iff false
    rw [hS] at ht hf
    simp only at ht hf
    revert ht hf
    generalize S.bot = b
    cases b <;> decide⟩

/-- `Statement:` the one-atom model of § V meets `QuineAtomHost`. -/
@[reducible]
def oneAtom_quineAtomHost : QuineAtomHost OneAtom where
  mem x y := x = OneAtom.bot ∧ y = OneAtom.bot
  bot := OneAtom.bot
  bot_mem_iff _ := ⟨And.left, fun h => ⟨h, rfl⟩⟩
  reflexive_unique x hx := ((hx x).2 rfl).1

/-- `Statement:` the § VI encoding of an `AFAStructure` meets `QuineAtomHost`. `Reading:` the
    "member of ⊥ ⇒ = ⊥" half of (Y') comes from the encoding's `x = y` conjunct, and "⊥ ∈ ⊥" from
    `bot_self_mem`; (Z') from `quine_unique`. -/
@[reducible]
def afaStructure_isQuineAtomHost (L : Type*) [ZPSemilattice L] [AFAStructure L] :
    QuineAtomHost L where
  mem x y := AFAStructure.selfMem x ∧ x = y
  bot := bot
  bot_mem_iff y := ⟨fun h => h.2, fun h => by subst h; exact ⟨AFAStructure.bot_self_mem, rfl⟩⟩
  reflexive_unique x hx := AFAStructure.quine_unique x bot ((hx x).2 rfl).1 AFAStructure.bot_self_mem

-- Statement: that encoding's membership relates no element to any other.
example (L : Type) [ZPSemilattice L] [AFAStructure L] (x y : L)
    (h : (afaStructure_isQuineAtomHost L).mem x y) : x = y := h.2

/-- `Statement:` under `BoffaMem` no element is its own only member. -/
theorem boffa_fails_singleton : ¬ ∃ b : Bool, ∀ y, BoffaMem y b ↔ y = b := by
  rintro ⟨b, hb⟩
  cases b
  · exact absurd ((hb true).1 trivial) (by decide)
  · exact absurd ((hb false).1 trivial) (by decide)

/-- `Statement:` with `mem = Eq` on `Bool` every element is its own only member, so no
    `QuineAtomHost` has that membership: (Z') fails. `Reading:` the toy shape of Boffa's BA₁,
    under which the reflexive sets form a proper class (Aczel 1988, Prop. 5.1, p. 57). -/
theorem boffa_fails_reflexive_unique : ¬ ∃ S : QuineAtomHost Bool, S.mem = Eq := by
  rintro ⟨S, hS⟩
  have h1 := S.reflexive_unique true (fun y => by rw [hS])
  have h2 := S.reflexive_unique false (fun y => by rw [hS])
  exact absurd (h1.trans h2.symm) (by decide)

/-- `Statement:` no `ZFSet` is its own sole member, so with `mem = (· ∈ ·)` no `ZFSet` meets
    `QuineAtomHost`'s (Y'); one way from `zfSet_no_quine_bottom`. -/
theorem zfSet_no_singleton_bottom : ¬ ∃ b : ZFSet, ∀ y, y ∈ b ↔ y = b :=
  fun ⟨b, hb⟩ => zfSet_no_quine_bottom ⟨b, (hb b).2 rfl⟩

end ZeroParadox

/-! ## Axiom Purity Check

Expected footprint: none for the class facts, the toys and the encodings; `zfSet_no_quine_bottom`
and `zfSet_no_singleton_bottom` inherit `no_quine_atom`'s [propext, Quot.sound] (Foundation via
Mathlib's `ZFSet.mem_wf`; choice-free). -/

section PurityCheck
open ZeroParadox

#print axioms quineHost_not_wellFounded
#print axioms quineHost_selfMem_iff
#print axioms boffa_fails_unique
#print axioms oneAtom_not_wellFounded
#print axioms zfSet_no_quine_bottom
#print axioms afaStructure_isQuineHost
#print axioms QuineAtomHost
#print axioms quineAtomHost_not_wellFounded
#print axioms trivialQuineAtomHost
#print axioms oneAtom_quineAtomHost
#print axioms afaStructure_isQuineAtomHost
#print axioms boffa_fails_singleton
#print axioms boffa_fails_reflexive_unique
#print axioms zfSet_no_singleton_bottom

end PurityCheck
