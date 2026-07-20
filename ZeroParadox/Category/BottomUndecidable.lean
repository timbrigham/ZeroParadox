import ZeroParadox.Category.LawvereTaboo

set_option maxHeartbeats 400000

/-!
# Where the keystone's classical cost sits: unresolved identity, and NOT self-containment

`ZeroParadox/Category/LawvereTaboo.lean` proves `wem_of_fixedPointFree`: the general form of the
diagonal engine's supplier (*every type with two distinct points admits a fixed-point-free endomap*)
implies **weak excluded middle**, choice-free. The reading recorded alongside it
(`.claude-local/notes/ambiguity_is_what_choice_buys_2026-07-20.md`) is that the cost is located at
**unresolved identity** — the one step that must decide whether two things are the same.

This file tests a sharpening of that reading: **is the framework's ⊥ (the self-containing Quine atom)
essential to the obstruction, or incidental?** Tim's conjecture was that checking "is this thing ⊥?"
on a self-containing object *re-enters the object and does not resolve*, so that ⊥'s apophatic
indescribability and the keystone's classical cost would be **one obstruction, proved**.

**The measured answer is: self-containment is INESSENTIAL. The cost is decidable equality, full stop.**
This is a negative result about the ⊥-connection, and — per the framework's own discipline
(`ZeroParadox/Category/ChoiceCannotBe.lean`; the retired MC-1 cross-category identity) — a negative
result stated honestly is worth as much as the positive one it replaces. What is established:

## The result

* **§ II — the cost IS identity.** `wem_of_decidableEq_glue`: if the `LawvereTaboo` witness carrier
  `Glue p` had decidable equality for every `p`, weak excluded middle would follow. Choice-free —
  the classical content is the hypothesis. This lands the cost *directly* at `DecidableEq`, one step
  earlier than `wem_of_fixedPointFree` lands it (that route first spends a `classical` to *build* the
  fixed-point-free map; here the taboo falls straight out of the identity decision). It is the
  decidable-equality face of the same taboo.
* **§ III — self-containment sits on BOTH sides of the decidability line, so it is not what the taboo
  tracks.** `SelfContained` is the carrier-agnostic form of `AbstractSelfApp`'s three structural
  fields (`selfApp`, `fixed_bot`, `unique_fp` — `ZeroParadox/Computability/SelfApp.lean`), with the
  bottom bundled rather than taken from a `ZPSemilattice`.
    - `selfContained_glue`: the *very carrier whose identity is the taboo* is itself self-containing —
      a constant self-map (the `OntBridge` "constant-to-null" pattern) has `Glue p`'s bottom as its
      unique fixed point. So self-containment does **not prevent** the taboo.
    - `selfContained_bool`: `Bool` is self-containing the same way and has decidable equality with no
      taboo. So self-containment does **not force** the taboo.
    Together: the unique-fixed-point self-application is *orthogonal* to decidability of equality. It
    is a bolt-on; the taboo tracks the `p`-glued quotient underneath, exactly as in `LawvereTaboo`.
* **§ IV — on a decidable carrier, "is this ⊥?" resolves.** `selfContaining_iff_bot` is the
  carrier-agnostic form of the framework's `selfMem_eq_singleton_bot` (self-members `= {⊥}`): checking
  self-containment *is* checking `x = bot`, and `selfContaining_decidable` shows that decides when the
  carrier has decidable equality. So the "re-enters and does not resolve" intuition is **not a
  Lean-type phenomenon** — the tamed encoding resolves fine.

## Why the ⊥-essential version cannot even be posed in Lean (the honest boundary)

The non-termination Tim points at is a property of the *semantic* set-theoretic Quine atom: deciding
`y = ⊥` unfolds `⊥ = {⊥}` and descends forever. That object is **not a Lean type** — `Set` is
well-founded, `x = {x}` is forbidden (Cantor), which the framework already proves as
`quine_no_literal` / `nontrivial_lattice_no_witness` (`ZeroParadox/Category/Lawvere.lean`). The Lean
encoding `AbstractSelfApp` replaces the infinite descent with a *pinned unique* fixed point, and a
pinned fixed point has the most decidable identity there is. So the ⊥-essential undecidability is
**unsettled in Lean because it is unposeable in Lean**, and *inessential in the encoding we do have*.
Reporting it as proved would repeat the MC-1 over-identification the project retracted. It stays a
rhyme with a mechanism, not a theorem — the fence in the conjecture note, unmoved.

**Hedberg contributes nothing here, and the reason is instructive.** Hedberg's theorem (decidable
equality ⟹ the type is an h-set / satisfies UIP) has real content in Martin-Löf type theory, where
"UIP is not provable" (Kraus–Escardó–Coquand–Altenkirch, below). In Lean 4 UIP holds for *every* type
by definitional proof irrelevance on the `Prop`-valued `Eq`, so Hedberg's conclusion is always true
and constrains nothing. The HoTT route — "self-reference generates higher identity structure, which
blocks decidable equality" — is therefore a non-starter *in this foundation*: there are no non-h-sets
to reach. The only live object is `DecidableEq`-as-**data**, which is what § II uses.

## Prior art — the taboo is KNOWN genre and is NOT claimed as new

* **M. Hedberg, "A coherence theorem for Martin-Löf's type theory," JFP 8(4), 1998.** Decidable
  propositional equality is a sufficient condition for a type to be an h-set. The route (read from
  the Kraus et al. analysis below): "A type `X` is an h-set iff for all `x, y : X` there is a constant
  map `x = y → x = y`; if `X` has decidable equality then such constant endomaps exist."
* **N. Kraus, M. Escardó, T. Coquand, T. Altenkirch, "Generalizations of Hedberg's Theorem," TLCA
  2013.** Read from source (pp. 1–3). Verbatim: *"uniqueness of identity proofs (UIP) is not
  provable"* (abstract); and their Section 5, *"While we cannot make a strong conclusion for arbitrary
  types, such as excluded middle, we prove that the assumption [every type has a constant endomap]
  implies that all equalities are decidable."* This is the precise sense in which decidable equality
  is a classical, not a constructive, commitment — and the precise reason Hedberg is toothless in a
  UIP foundation like Lean.
* **M. Escardó, TypeTopology, `Taboos.Decomposability` and `Notation.Decidability`.** "Discrete" =
  decidable equality; the discreteness taboos are the neighbouring genre. Cited in `LawvereTaboo`.
* Weak excluded middle and the taboo methodology: **constructive reverse mathematics** (Ishihara;
  Diener–Ishihara). Cited, not claimed.

**Searched, none found** for the exact statement of § II on this witness carrier — a report of one
search, not a priority claim. The mathematics of § II is elementary and standard; its only
framework-specific content is the reuse of the `LawvereTaboo` carrier and the § III–IV refutation of
the ⊥-essential reading.

## Engineer's Take

I wanted to know whether there was a lever we could press on to turn "the framework essentially never
needs choice" into "actually never." Chasing that lever is what found the keystone cost, and the
keystone cost is unresolved identity.

That looked like another layer of the general versus instance logic. The general case pays for
ambiguity and the specific instance does not. What caught my attention is that undefinability is one
of the attributes of the bottom, so I asked whether the bottom is just a specific instance of
arbitrary types, since every structure has to have some concept of zero to work.

The Lean says the two walls are not the same wall. Self-containment turned out to be a bolt-on, and it
sits on both a decidable carrier and an undecidable one with no effect on the cost. The bottom that
would actually loop forever when you ask whether something is it is exactly the object this proof
system will not let us build.

So the essential version of the question cannot be posed in this foundation. That is not the answer I
was after and it is still a result. A line where the question stops being answerable because the
object lives outside what the system can express is the edge we keep looking for. It points at a
non-well-founded or univalent setting as the place the question would get its teeth back.

---

## Structure
- § I   The identity decision on the witness carrier
- § II  Decidable equality of the carrier implies weak excluded middle
- § III `SelfContained`: self-containment on both sides of the decidability line
- § IV  On a decidable carrier, "is this the bottom?" resolves
-/

namespace ZeroParadox

/-! ## § I — The identity decision on the `LawvereTaboo` witness carrier

`Glue p` (`ZeroParadox/Category/LawvereTaboo.lean`) is three tokens modulo a `p`-indexed gluing: the
glued point `gx p` equals `gb0 p` under `p` and `gb1 p` under `¬p`, while `gb0 p ≠ gb1 p`
unconditionally. Deciding the single identity `gx p = gb0 p` therefore decides a side of `¬p ∨ ¬¬p`.
Nothing here is self-referential; the source of the ambiguity is the quotient. -/

/-- **The one identity decision suffices for the taboo.** A decision procedure for `gx p = gb0 p`,
uniform in `p`, yields weak excluded middle. Choice-free: the decision is the hypothesis, and the
witness facts (`gx_eq_gb0`, `gx_eq_gb1`, `glue_b0_ne_b1`) carry only `[propext, Quot.sound]`. -/
theorem wem_of_glue_identity (h : ∀ p : Prop, Decidable (gx p = gb0 p)) : WeakExcludedMiddle := by
  intro p
  rcases h p with hne | heq
  · -- `gx p ≠ gb0 p`: were `p` to hold, `gx p = gb0 p` (`gx_eq_gb0`). So `¬p`.
    exact Or.inl fun hp => hne (gx_eq_gb0 p hp)
  · -- `gx p = gb0 p`: were `¬p` to hold, `gx p = gb1 p`, forcing `gb0 p = gb1 p`. So `¬¬p`.
    exact Or.inr fun hnp => glue_b0_ne_b1 p (heq.symm.trans (gx_eq_gb1 p hnp))

/-! ## § II — Decidable equality of the carrier implies weak excluded middle -/

/-- **Decidable equality on the witness carrier is the taboo.** `DecidableEq (Glue p)` supplies the
identity decision of § I, so its uniform availability implies weak excluded middle.

This lands the keystone's classical cost *at `DecidableEq`* — one step earlier than
`wem_of_fixedPointFree`, which first spends a `classical` tactic to build a fixed-point-free endomap.
Both are the same taboo; this is its decidable-equality face. Prior art: Hedberg (1998),
Kraus–Escardó–Coquand–Altenkirch (2013); see the header. Choice-free. -/
theorem wem_of_decidableEq_glue (h : ∀ p : Prop, DecidableEq (Glue p)) : WeakExcludedMiddle :=
  wem_of_glue_identity fun p => h p (gx p) (gb0 p)

/-! ## § III — `SelfContained`: self-containment lives on both sides of the line

`SelfContained` is `AbstractSelfApp`'s three structural fields (`ZeroParadox/Computability/SelfApp.lean`)
with the bottom bundled instead of drawn from a `ZPSemilattice`, so it can be instantiated on carriers
that are not lattices. The point of this section is that a `SelfContained` structure exists on the
undecidable carrier `Glue p` *and* on the decidable carrier `Bool`, via the same trivial construction —
so self-containment is orthogonal to the taboo. -/

/-- The carrier-agnostic self-application structure: a self-map with a designated bottom as its
**unique** fixed point. Mirrors `AbstractSelfApp.selfApp` / `fixed_bot` / `unique_fp`. -/
structure SelfContained (C : Type) where
  /-- The self-application. -/
  app : C → C
  /-- The designated bottom. -/
  bot : C
  /-- The bottom is a fixed point. -/
  fixed : app bot = bot
  /-- It is the only one. -/
  unique : ∀ x, app x = x → x = bot

/-- **The taboo carrier is itself self-containing.** The constant-to-bottom self-map — the
`ZeroParadox/Settheory/OntBridge.lean` "constant-to-null" pattern — makes `gb0 p` the unique fixed
point of `Glue p`. So a self-containing carrier can have the undecidable equality of § II:
self-containment does **not prevent** the taboo. -/
def selfContained_glue (p : Prop) : SelfContained (Glue p) where
  app := fun _ => gb0 p
  bot := gb0 p
  fixed := rfl
  unique := fun _ hx => hx.symm

/-- **A self-containing carrier with decidable equality and no taboo.** `Bool` carries the same
constant-to-bottom self-application, and `DecidableEq Bool` is free. So self-containment does **not
force** the taboo either. Read with `selfContained_glue`: the structure is a bolt-on, orthogonal to
whether equality decides. -/
def selfContained_bool : SelfContained Bool where
  app := fun _ => false
  bot := false
  fixed := rfl
  unique := fun _ hx => hx.symm

/-! ## § IV — On a decidable carrier, "is this the bottom?" resolves

The framework proves `selfMem_eq_singleton_bot`: the self-containing elements are exactly `{⊥}`. Its
carrier-agnostic form says checking self-containment *is* checking `x = bot`. That decides on any
carrier with decidable equality — so the "checking is-this-⊥ re-enters forever" intuition is a fact
about the *semantic* Quine atom, not about the Lean encoding. -/

/-- **Self-containment is identity with the bottom** (carrier-agnostic `selfMem_eq_singleton_bot`).
`x` is a fixed point of the self-map iff `x` is the bottom. -/
theorem selfContaining_iff_bot {C : Type} (S : SelfContained C) (x : C) :
    S.app x = x ↔ x = S.bot := by
  constructor
  · exact S.unique x
  · rintro rfl; exact S.fixed

/-- **On a decidable carrier the self-containment check terminates.** Given `DecidableEq C`, "is `x`
self-containing?" is decidable — directly, and via `selfContaining_iff_bot` it is the decision
`x = bot`. Concrete rebuttal of "checking is-this-⊥ does not resolve", *at the Lean level*: it does,
whenever the carrier is one Lean will host. -/
def selfContaining_decidable {C : Type} [DecidableEq C] (S : SelfContained C) (x : C) :
    Decidable (S.app x = x) := inferInstance

end ZeroParadox

/-! ## Axiom Purity Check

§ II must be choice-free: the classical content is the hypothesis (a decision procedure), not the
proof. The witness facts inherited from `LawvereTaboo` carry `[propext, Quot.sound]`; no
`Classical.choice` appears. § III–IV are constructions and are expected to be axiom-free or
`[propext, Quot.sound]`. -/

section PurityCheck
open ZeroParadox

-- § I–II — the taboo. MUST NOT carry `Classical.choice`.
#print axioms wem_of_glue_identity
#print axioms wem_of_decidableEq_glue

-- § III — the orthogonality witnesses.
#print axioms selfContained_glue
#print axioms selfContained_bool

-- § IV — self-containment resolves to an identity decision.
#print axioms selfContaining_iff_bot
#print axioms selfContaining_decidable

end PurityCheck
