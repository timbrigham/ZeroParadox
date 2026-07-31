import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Order.Snap
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Tactic

/-!
# ZP-K: Computational Grounding of Self-Reference

## Engineer's Take

ZPJ established the set-theoretic case. ZPK adds the computational grounding.
Existence is itself an action away from null. Action by definition is not null.
There is nothing prior to bottom that could trigger it. So if bottom is going
to do anything, it has to do it itself. Kleene's theorem is basically saying
that there is always a version of that logic. It isn't specific to one
programming language or way of looking at things. Much like the bootstrapping
problem in any sufficiently powerful language. It is not specific to one system.
Any language powerful enough eventually has to face it. T-COMP proves three of
them equivalent. Being bottom, being the Quine atom, and satisfying the join
identity are the same structural fact stated three ways. Being a Kleene fixed
point is the fourth, and it comes in as a requirement of the class rather than
as something the theorem shows. That one is the soft joint, and that is exactly
why I keep coming back to it.

---

## Formal Overview (AI-assisted)

Relates four structural roles of ⊥, of which three are proved equivalent:

  (1) Quine atom       — set-theoretic self-reference (ZF + AFA)
  (2) Bottom element   — order-theoretic minimum (ZP-A)
  (3) Join identity    — algebraic generator (ZP-A A4)
  (4) Kleene fixed point — computational self-reference (Mathlib: fixed_point₂)

The central result (T-COMP) establishes (1) ↔ (2) ↔ (3) via T-EXEC. Its proof term is
`t_exec_triple_iff`, a ZP-J result that does not mention computation; ⊥ is then the
element those three pick out. **(4) is not a clause of that theorem** — it is present
by typeclass requirement, as the class field `botCode_is_quine`. The KleeneStructure
typeclass taking (1)–(4) to name the same structural role in four formal languages is
the motivating commitment, not a consequence derived by the theorems. Note the two
sides also differ in shape: (1)–(3) pick out a unique element, while the computational
fixed points form an infinite family (§ VI).

## Structure

- § I   The Kleene fixed point — statement and computational Quine definition
- § II  KleeneStructure typeclass — the commitment bridging AFAStructure to computability
- § III T-COMP: three proved equivalent, and where the fourth face sits
- § IV  DA-1 closure — the witnesses the description-instantiation argument rests on
- § V   MachinePhase instance — DA-1's concrete witness for ZP-E's machine
- § VI  Function-Gödel-number correspondence — period = index, non-computability boundary

## Key insight (April 26, 2026)

This is the framework's reading, and it is a commitment throughout — no theorem in this
file establishes it. On that reading, ⊥ in the computational instantiation (ZP-C D7) is
not a state OF a Turing machine: ⊥ IS the universal Turing machine in its ground state,
and U is not a description awaiting an external executor but IS the executor.

What Lean supplies underneath: Kleene's second recursion theorem (Mathlib:
Nat.Partrec.Code.fixed_point₂) guarantees a fixed point exists for any partially
computable transformation. The KleeneStructure typeclass then takes the AFA Quine atom
(⊥ = {⊥}) and the Kleene computational quine (∃ c, eval c = f c) to be the same
structural property. That identification is the motivating commitment, not a theorem
proved here, and it cannot be stated as an equation — `Code` and `L` are different
types.

## Dependencies

ZP-J (T-EXEC: IsQuineAtom q ↔ q = ⊥, bot_self_mem).
Mathlib: Nat.Partrec.Code.fixed_point₂ (Kleene's second recursion theorem).
Mathlib: Nat.Partrec.Code.fixed_point (Rogers' fixed-point theorem).

## Axiom footprint (verified)

All proved ZP-K theorems depend on [propext, Classical.choice, Quot.sound].
Source: Mathlib computability infrastructure — Kleene's theorem (fixed_point₂) and
Rogers' theorem (fixed_point) themselves use classical logic and choice.
ZP-J T-EXEC (axiom-free) is preserved as a ZP-J result; the classical axioms enter
through Code/Partrec machinery, not through the ZPSemilattice or AFAStructure fields.

Note a distinction that is easy to get backwards. Several results here are ZP-J
theorems restated under a stronger hypothesis — `t_comp` (proof term
`t_exec_triple_iff`), `kleene_quine_is_bot` (`t_exec`), `da1_computational`
(`bot_is_quine_atom`). The `[KleeneStructure L]` hypothesis is inert *on those proof
routes*, and the fences below say so. It is **not** absent from their axiom footprints:
`#print axioms` traverses the statement, and the hypothesis reaches
`IsComputationalQuine` → `selfApply` → Mathlib `eval`. So all three report the full
triple, as the block at the end of this file shows. Inert-in-the-proof and
absent-from-the-footprint are different properties; do not infer either from the other.

§ VI theorems: all fully proved — self_halting_undecidable, isComputationalQuine_undecidable,
quine_period_is_goedel, quine_goedel_injective, and infinite_quine_family.
No sorry stubs remain in ZPK.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open Nat.Partrec Nat.Partrec.Code

/-! ## § I. The Kleene Fixed Point -/

/-- A code c is a Kleene fixed point for f if c's computed behavior equals f(c).
    This is the computational expression of self-containment: c's behavior is
    determined by c itself, with no external description shorter than c. -/
-- [ZP-CUSTOM] replaces: Mathlib Function.IsFixedPt | reason: Function.IsFixedPt works on total functions α → α. Here f : Code → ℕ →. ℕ (partial function) and the fixed-point condition is eval c = f c — equality of partial functions. No Mathlib predicate covers this; IsKleeneFixedPoint is the partial-function analog needed for the computability layer.
def IsKleeneFixedPoint (f : Code → ℕ →. ℕ) (c : Code) : Prop :=
  eval c = f c

/-- Kleene's second recursion theorem (Mathlib: fixed_point₂):
    for any partially computable f, a fixed-point code exists.
    This is the direct import — no new content, just a named alias
    establishing the connection to ZP-K's framework. -/
theorem kleene_fixed_point_exists (f : Code → ℕ →. ℕ) (hf : Partrec₂ f) :
    ∃ c : Code, IsKleeneFixedPoint f c :=
  fixed_point₂ hf

/-- The self-application transformation: the map sending each code c to the
    partial function encoding "run c on c's own Gödel number plus offset n."
    A fixed point of selfApply satisfies a periodicity condition with period encode(c):
    eval c n = eval c (encode c + n) for all n — so a code's own Gödel number is a
    period of it, though not necessarily the least. Non-uniqueness is expected, and it
    holds for two separate reasons: distinct fixed points have distinct Gödel numbers
    (encoding is injective), and the family is infinite (`infinite_quine_family`,
    witnessed by the constant codes). Neither reason follows from the other. (Note this
    says nothing about codes that are not fixed points; most are not.)

    The Gödel numbering uses Mathlib's `Encodable.encode : Code → ℕ`, which gives
    each code a canonical index. selfApply_partrec confirms this is computable. -/
noncomputable def selfApply : Code → ℕ →. ℕ :=
  fun c n => eval c (Encodable.encode c + n)

/-- selfApply is partially computable. -/
lemma selfApply_partrec : Partrec₂ selfApply := by
  simp only [Partrec₂, selfApply]
  exact eval_part.comp Computable.fst
    (Primrec₂.comp Primrec.nat_add
      (Primrec.encode.comp Primrec.fst)
      Primrec.snd).to_comp

/-- A computational Quine is a code satisfying the selfApply periodicity condition:
    eval c n = eval c (encode c + n) for all n. Existence is guaranteed by Kleene's
    second recursion theorem. Non-uniqueness is expected — multiple codes with distinct
    Gödel numbers satisfy the condition independently. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Named alias for IsKleeneFixedPoint selfApply c. Makes the connection to Quine atoms explicit in type signatures and theorem statements; not a raw Mathlib concept. Unlike the AFA Quine (unique by AFA), computational quines are NOT unique — each has a distinct Gödel number, giving the infinite family of §VI.
def IsComputationalQuine (c : Code) : Prop :=
  IsKleeneFixedPoint selfApply c

/-- Kleene guarantees a computational Quine exists. -/
theorem computational_quine_exists : ∃ c : Code, IsComputationalQuine c :=
  kleene_fixed_point_exists selfApply selfApply_partrec

/- Note on computational quine uniqueness (why it is not stated here):
    Unlike the AFA quine (ZP-J quine_unique), computational fixed points of
    selfApply are NOT unique in general. AFA uniqueness follows from the unique
    decoration theorem: there is literally only one set satisfying x = {x}. The
    computational setting is richer. A fixed point c of selfApply satisfies:
      eval c n = eval c (Encodable.encode c + n)  for all n
    This is a periodicity condition on eval c, not a global identity constraint.
    Multiple programs can satisfy it independently — including the constant codes,
    which satisfy it vacuously (`hconst_quine`, a `have` inside `infinite_quine_family`, § VI), so the condition is strictly
    weaker than self-reference.
    The framework reads the resulting family as the DA-2 instantiation succession —
    each bottom element carrying its own Gödel number, hence its own fixed point and
    period — so that a single unique quine would contradict DA-2. That reading is an
    interpretation of the non-uniqueness, not a theorem: nothing here exhibits a map
    from instantiation index to code, and the type boundary makes such an
    identification unstatable.
    Uniqueness in ZP-K is inherited from ZP-J (set-theoretic side via T-EXEC):
    any element satisfying IsQuineAtom equals ⊥ — this is kleene_quine_is_bot.
    The framework reads the computational witnesses (botCode) as naming ⊥. That reading
    is the KleeneStructure commitment; it is not established by behavioral equality of
    codes, and it is not a Lean identity — see the type-boundary note above. -/

/-! ## § II. KleeneStructure — Bridging Computation and AFA -/

/-- A ZP-A semilattice has KleeneStructure if it carries an AFAStructure and
    additionally names a `Code` satisfying `IsComputationalQuine`.

    **This class is a COMMITMENT, and it is the framework's, not a theorem.** It
    asserts that the AFA Quine atom and the Kleene computational quine name the same
    structural property — the reading "botCode is the code that IS its own program,
    the universal Turing machine in ground state, and this is the computational
    expression of `bot_self_mem`". Nothing in this file derives that identification,
    and nothing could state it as an equation: `botCode` is a `Code` and `bot` is an
    element of `L`, so no `=` exists between them.

    Three things to keep in view when relying on this class:
    * `botCode_is_quine` requires only `IsComputationalQuine`, a *periodicity*
      condition satisfied by constant codes (`hconst_quine`, a `have` inside `infinite_quine_family`, § VI). It does not by
      itself pin self-reference.
    * `bot_self_mem_from_kleene` restates the `AFAStructure` field `bot_self_mem`
      that this class already inherits. It records the intent of the bridge; it adds
      no content beyond the inherited field.
    * The AFA side has exactly one self-containing element (`quine_unique`); the
      computational side has infinitely many fixed points (`infinite_quine_family`).
      The commitment relates a unique element to a family, and § VI says what that
      family is. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Bridges AFAStructure (set-theoretic self-containment) with Mathlib's computability library (Nat.Partrec.Code). No Mathlib typeclass connects AFA and Code. KleeneStructure asserts that the AFA Quine atom and the Kleene computational Quine (∃ c, eval c = f c) name the same structural property — this identification is the motivating commitment, not a derived theorem.
class KleeneStructure (L : Type*) [ZPSemilattice L] extends AFAStructure L where
  /-- The code the framework nominates as ⊥'s computational witness. Nothing here
      distinguishes it: it is whatever code the instance supplies. -/
  botCode : Code
  /-- botCode satisfies `IsComputationalQuine` — a periodicity condition, which constant
      codes also satisfy (`hconst_quine`, a `have` inside `infinite_quine_family`, § VI). Reading it as "the computational
      expression of bot_self_mem" is the class's commitment, not a consequence of this
      field. -/
  botCode_is_quine : IsComputationalQuine botCode
  /-- Restates the inherited `AFAStructure` field `bot_self_mem`; it records the intent
      of the bridge and adds no content beyond what `extends AFAStructure L` already
      supplies.
      The intended reading — ⊥ = {⊥} in set theory alongside
      eval botCode = selfApply botCode in computation — is the commitment. The two are
      not equated and cannot be: one is about an element of `L`, the other about a
      `Code`. -/
  bot_self_mem_from_kleene : AFAStructure.selfMem (bot : L)

/-! ## § III. T-COMP — the three-way equivalence, and where the fourth face sits -/

/-- T-COMP (Computational Grounding Theorem):
    In any KleeneStructure lattice, **three** characterisations of the null ground
    element are proved equivalent:
      (1) Quine atom  — IsQuineAtom q  (AFA self-containment, set-theoretic)
      (2) Bottom      — q = ⊥          (order-theoretic minimum)
      (3) Join identity — ∀ x, q ∨ x = x  (algebraic generator)

    **Honest fence.** Lean proves (1) ↔ (2) ↔ (3), and that is the whole content of
    this statement — the proof term is literally `t_exec_triple_iff`, a ZP-J result
    that does not mention computation. The fourth characterisation,

      (4) Kleene fixed point — computational self-reference,

    is **not** a clause of this theorem. It enters as the `KleeneStructure` class field
    `botCode_is_quine` — a typeclass *requirement*, as the file header states. Reading
    (1)–(4) as "the same structural role in four formal languages" is the framework's
    interpretation of that arrangement, not a theorem proved here.

    Two facts that keep the fence honest:
    * (4) is a condition on a `Code`, (1)–(3) are conditions on an element of `L`.
      There is no equality across those types, and none is claimed.
    * (1)–(3) pick out a **unique** element (`quine_unique`), while the computational
      fixed points form an **infinite** family (`infinite_quine_family`,
      `quine_goedel_injective`). A unique element and an infinite family are not
      identified by this theorem; see the note in § II on why the non-uniqueness is
      structurally expected, and § VI on what the family actually is. -/
theorem t_comp {L : Type*} [ZPSemilattice L] [KleeneStructure L] (q : L) :
    IsQuineAtom q ↔ q = bot ∧ ∀ x : L, join q x = x :=
  t_exec_triple_iff q

/-- Any element satisfying the AFA Quine-atom property equals ⊥.

    **Honest fence.** The statement quantifies over elements of `L` and mentions no
    computational fixed point; the proof term is `t_exec`, a pure ZP-J result. The
    `KleeneStructure` hypothesis is inert *on this proof route* — it supplies the
    `AFAStructure` this inherits from, and nothing else is used. It is not absent from
    the axiom footprint, which follows the statement (see the footprint note in the
    header). That the Kleene fixed point and the AFA Quine atom
    "identify the same element" is the class's motivating commitment (header, § II),
    not what this theorem shows. -/
theorem kleene_quine_is_bot {L : Type*} [ZPSemilattice L] [KleeneStructure L]
    (q : L) (hq : IsQuineAtom q) : q = bot :=
  t_exec q hq

/-- Rogers' fixed-point theorem (Mathlib: fixed_point) as used in ZP-K:
    for any total computable transformation of codes, a fixed point exists.
    This is the foundation of the Kleene connection — programs can always
    be self-referential. -/
theorem roger_fixed_point_exists (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  fixed_point hf

/-! ## § IV. DA-1 Closure -/

/-- DA-1 (Computational Grounding): in any KleeneStructure lattice, the bottom
    element is a Quine atom.

    **Honest fence.** The proof is `bot_is_quine_atom` from ZP-J: ⊥ is self-containing
    by the class field `bot_self_mem` and unique by `quine_unique`. Both are *fields*,
    so this statement unpacks the structure's own requirements — it does not derive
    them. Nothing computational appears in the statement or the proof.

    The reading "⊥ is necessarily *executing*, not a static description" is the
    framework's interpretation of `bot_self_mem` under the KleeneStructure commitment,
    and DA-1's central claim. It is meaning attached to the Lean fact, not a separate
    Lean theorem. -/
theorem da1_computational {L : Type*} [ZPSemilattice L] [KleeneStructure L] :
    IsQuineAtom (bot : L) :=
  bot_is_quine_atom

/-- Both DA-1 witnesses hold together: ⊥ is an AFA Quine atom, and the class's chosen
    `botCode` is a computational quine.

    **Honest fence.** The statement is a **conjunction**, and a conjunction is not an
    identity. Each conjunct comes from a class field (`bot_self_mem`,
    `botCode_is_quine`); nothing here shows the two are the same fact, and they cannot
    be equated in Lean — one is a property of an element of `L`, the other of a `Code`.

    The framework's reading — that Path 1 (AFA: nothing external to ⊥ can execute it)
    and Path 3 (AIT: no shorter external program generates it) are one structural fact
    expressed in two languages — is DA-1's argument, carried by this pair of witnesses,
    not proved by it.

    Note also that `IsComputationalQuine` is a *periodicity* condition, satisfied by
    constant codes (`hconst_quine`, in the proof of `infinite_quine_family`). So the
    second conjunct alone does not pin self-reference; see § VI. -/
theorem da1_paths_unified {L : Type*} [ZPSemilattice L] [KleeneStructure L] :
    IsQuineAtom (bot : L) ∧ IsComputationalQuine (KleeneStructure.botCode (L := L)) :=
  ⟨bot_is_quine_atom, KleeneStructure.botCode_is_quine⟩

/-- ⊥ is a Quine atom, and it is the only one.

    **Honest fence.** Both conjuncts are ZP-J results recombined (`bot_is_quine_atom`,
    `t_exec`); neither mentions computation, and the `KleeneStructure` hypothesis is
    inert in the proof. The statement is about existence-and-uniqueness of the
    self-containing element in `L`, nothing more.

    The framework's reading — that ⊥ is not a description awaiting an external
    executor but IS the executor, so DA-1's static-description alternative is closed —
    is the argument this witness supports. It is DA-1's claim, not this theorem's
    content, and "no external program is prior to ⊥" is a requirement the framework
    imposes rather than something derived here. -/
theorem description_instantiation_gap_closed {L : Type*} [ZPSemilattice L]
    [KleeneStructure L] : IsQuineAtom (bot : L) ∧
    ∀ (q : L), IsQuineAtom q → q = bot := by
  exact ⟨bot_is_quine_atom, fun q hq => t_exec q hq⟩

/-! ## § V. MachinePhase — Concrete DA-1 Closure

Provides AFAStructure and KleeneStructure instances for ZP-E's MachinePhase type,
closing DA-1 formally for the specific computational model ZP-E describes.

selfMem is modelled as equality with bot — the CIC-compatible expression of AFA
self-containment ⊥ = {⊥}. Anti-foundation is not required at the typeclass level:
the relevant structural fact (bot is the unique self-containing element) is
captured by the definition selfMem x := x = bot, proved axiom-free. -/

open ZeroParadox ZeroParadox

/-- AFAStructure instance for MachinePhase.
    selfMem x := x = bot (bot = .initial = c₀).
    The unique self-containing element is the initial state — the bottom of the
    semilattice. This is the CIC encoding of ⊥ = {⊥}: bot is self-containing
    and is the only element with this property. -/
-- [ZP-CUSTOM] instance: AFAStructure MachinePhase | reason: selfMem x := x = bot is the CIC-compatible encoding of AFA self-containment (⊥ = {⊥} cannot be stated in Lean's well-founded type theory). Quine uniqueness and bot_self_mem are provable by rfl. This is the concrete closure of DA-1 for ZP-E's machine model.
instance machinePhaseAFA : AFAStructure MachinePhase where
  selfMem x      := x = bot
  quine_unique _ _ hx hy := hx.trans hy.symm
  bot_self_mem   := rfl

/-- KleeneStructure instance for MachinePhase.
    `botCode` is `Classical.choose` applied to `computational_quine_exists` — *some*
    code satisfying `IsComputationalQuine`, whose existence is guaranteed by
    `kleene_fixed_point_exists` (Kleene's second recursion theorem). It is not a
    distinguished code, and the predicate it satisfies is a periodicity condition that
    constant codes also meet (§ VI). Reading it as "the code that IS its own program,
    the computational expression of ⊥ = {⊥}" is the framework's commitment, carried by
    the class, not a property this instance establishes. -/
-- [ZP-CUSTOM] instance: KleeneStructure MachinePhase (noncomputable) | reason: botCode chosen via Classical.choose — no algorithm can identify which Code IS the botCode (isComputationalQuine_undecidable). The noncomputable marker is load-bearing, not a proof artifact: the non-constructivity is the formal content of DA-1's computational path. Stripping it would misrepresent the result.
noncomputable instance machinePhaseKleene : KleeneStructure MachinePhase where
  botCode               := Classical.choose computational_quine_exists
  botCode_is_quine      := Classical.choose_spec computational_quine_exists
  bot_self_mem_from_kleene := rfl

/-- DA-1 closed (concrete): in the MachinePhase semilattice, ⊥ is a Quine atom.
    Follows from `da1_computational` at the MachinePhase KleeneStructure instance.

    **Honest fence — read this before citing the theorem.** What Lean proves is exactly
    `IsQuineAtom (bot : MachinePhase)`: the initial state is self-containing, and it is
    the only such state. The self-containment comes from the `AFAStructure` instance
    for `MachinePhase` (`machinePhaseAFA`'s `bot_self_mem`), not from any computational
    field — `KleeneStructure`'s `bot_self_mem_from_kleene` is inert on this proof
    route.

    The reading "c₀ is self-**executing** — not a static description awaiting an
    external interpreter" is DA-1's claim and the framework's requirement on the
    computational bottom. It is meaning attached to this Lean fact, **not** what the
    statement carries. Two specifics that matter when this theorem is cited as
    computational grounding:
    * The statement mentions no `Code` and no execution.
    * `botCode` here is `Classical.choose computational_quine_exists` — *some*
      computational quine, not a distinguished one. `IsComputationalQuine` is a
      periodicity condition satisfied by constant codes (`hconst_quine`, a `have` inside `infinite_quine_family`, § VI), so the
      chosen witness need not itself exhibit self-reference. -/
theorem da1_closed_concrete : IsQuineAtom (bot : MachinePhase) :=
  da1_computational

/-! ## § VI. Function-Gödel-Number Correspondence

Every computational quine c has a Gödel number encode(c) that is not external
metadata — it is *a* period of the function computed by c in the selfApply sense. (Not
*the* period: nothing here shows it is the least one, and a constant code is periodic
with every period.)
The computational quines form an infinite family with distinct Gödel numbers. Within
that family a code is recovered from its Gödel number, since encoding is injective on
all of `Code`. That does not make the function and the index mutually determining: the
index is only *a* period of the function, and constant codes are periodic with every
period, so the function does not fix the index. Reading that family as the DA-2 instantiation
succession — one bottom element per instantiation, each with its own code — is the
framework's interpretation and is NOT what the theorems below establish; see the fence
immediately following for what actually witnesses the family.

**Honest fence on what "computational quine" does and does not pin.**
`IsComputationalQuine` is the *periodicity* condition eval c n = eval c (encode c + n).
A constant code satisfies it vacuously — a constant ignores its input and is periodic
with every period — and the proof of `infinite_quine_family` below witnesses the family
with exactly those (`hconst_quine`, `Code.const k`). So the predicate is strictly weaker
than "self-referential": genuine Kleene fixed points satisfy it (`computational_quine_exists`,
via the second recursion theorem, and that witness is real), and so do constants. The
(function, index) pairing is therefore a signature of the *code*, and should not be read
on its own as a signature of self-reference.

**And on the shape of the family.** These fixed points are genuinely many and genuinely
distinct — `infinite_quine_family` and `quine_goedel_injective` prove it — while the
set-theoretic side has exactly one self-containing element (`quine_unique`). A unique
element and an infinite indexed family are different shapes, so the correspondence here
is between the *succession* of instantiations and the family, not an identification of
one element with one code. The framework's reading of that correspondence is in § II;
no theorem in this file identifies a `Code` with an element of a lattice, and the type
boundary makes such an identification unstatable.

**Prior art, and a distinction that must not be collapsed.** That a computational object
is named by many indices rather than one is standard: the **Padding Lemma** — every
partial recursive function has infinitely many indices — is its classical home, and an
external computability reader mentioned it as possibly related when asked about ZP-K.
It is the right reference for the direction it actually gives: **a function does not
determine an index**, since infinitely many indices compute it. (Stated as a named lemma
without individual attribution; it appears as a hypothesis of Rogers' isomorphism theorem
rather than as a result of his, so do not attach a name to it.)
It is **not** what `infinite_quine_family` proves, and the two must not be conflated:
padding supplies infinitely many indices for the *same* function, whereas this family is
witnessed by the constant codes, and `Code.const 0` and `Code.const 1` compute *different*
functions. So the family here is broad, not a padding orbit. Cite padding for the
index-multiplicity point; do not cite it for this theorem.

Three formal results capture this structure:
  (1) quine_period_is_goedel — the Gödel number IS a period (definitionally; not shown
      to be the least one)
  (2) self_halting_undecidable and isComputationalQuine_undecidable — the boundary
      between computation and self-reference is genuinely non-computable, not merely
      unimplemented; Classical.choose in machinePhaseKleene reflects this
  (3) infinite_quine_family — the quine family is infinite: unboundedly many distinct
      (function, index) pairs exist. Its witnesses are the constant codes, so it bounds
      the family from below without showing those members are instantiation bottoms

The noncomputable marker on machinePhaseKleene is therefore load-bearing, not a
proof artifact. No algorithm can identify which code IS the botCode for a given
KleeneStructure instance — the choice is structurally outside classical computation. -/

/-- For any computational quine c, the Gödel number encode(c) is a period of
    eval c in the selfApply sense: eval c n = eval c (encode(c) + n) for all n.
    This makes explicit what IsComputationalQuine encodes definitionally: the index is
    a period. Note "a", not "the" — nothing here shows encode(c) is the *least* period,
    and a constant code is periodic with every period, so this alone does not make the
    function and the Gödel number mutually determining. -/
theorem quine_period_is_goedel (c : Code) (hc : IsComputationalQuine c) :
    ∀ n : ℕ, eval c n = eval c (Encodable.encode c + n) := by
  intro n
  have h := congr_fun hc n
  simp only [selfApply] at h
  exact h

/-- Among computational quines, distinct Gödel numbers imply distinct codes.

    **Honest fence.** The proof is `Encodable.encode_inj` — injectivity of the encoding
    on all of `Code`. Both quine hypotheses are bound to `_` and are unused, so this is
    a fact about the encoding, not about quines specifically. No map from an
    instantiation index to a code exists anywhere in this development, and none could be
    stated as an equality against a lattice element (§ VI fence above). The framework's
    reading — that each successive bottom carries its own distinct code — is an
    interpretation of the family, not a theorem here. -/
theorem quine_goedel_injective (c₁ c₂ : Code)
    (_ : IsComputationalQuine c₁) (_ : IsComputationalQuine c₂)
    (h : Encodable.encode c₁ = Encodable.encode c₂) : c₁ = c₂ :=
  Encodable.encode_inj.mp h

/-- The predicate "c halts on its own Gödel number" is undecidable.
    Proof: reduce from halting_problem 0. The function φ(c) = Code.comp c (Code.const 0)
    satisfies eval (φ c) k = eval c 0 for all k, so if the self-halting predicate were
    computable, composing with φ would decide "c halts on 0" — contradicting halting_problem 0.
    For a quine c, quine_period_is_goedel ties halting at encode(c) to halting at any
    encode(c) + n, so undecidability reaches directly into the period structure. -/
theorem self_halting_undecidable :
    ¬ComputablePred (fun c : Code => (eval c (Encodable.encode c)).Dom) := by
  intro h
  apply ComputablePred.halting_problem 0
  -- φ(c) = Code.comp c (Code.const 0): run c on 0 regardless of actual input
  have φ_comp : Computable (fun c : Code => Code.comp c (Code.const 0)) :=
    (primrec₂_comp.comp Primrec.id (Primrec.const _)).to_comp
  -- eval (φ c) k = eval c 0 for all k, c  (const 0 feeds 0 to c regardless of k)
  have φ_eval : ∀ (c : Code) (k : ℕ), eval (Code.comp c (Code.const 0)) k = eval c 0 := by
    intro c k
    change eval (Code.const 0) k >>= eval c = eval c 0
    simp [eval_const]
  -- Compose h (deciding self-halting) with φ to get ComputablePred for halting-at-0
  -- Use the same DecidablePred instance w that h carries, composed with φ
  obtain ⟨w, hdec⟩ := h
  have h_phi : ComputablePred (fun c : Code =>
      (eval (Code.comp c (Code.const 0)) (Encodable.encode (Code.comp c (Code.const 0)))).Dom) :=
    ⟨fun c => w (Code.comp c (Code.const 0)), hdec.comp φ_comp⟩
  exact h_phi.of_eq fun c => by simp [φ_eval]

/-- The predicate IsComputationalQuine is undecidable: no algorithm identifies
    which codes are Kleene fixed points of selfApply.

    Proof: reduce from self_halting_undecidable.
    For each c : Code, construct φ c = Code.comp Code.right
      (Code.pair (Code.comp c (Code.const (encode c))) (Code.pair Code.left Code.right)).
    Behavior: eval (φ c) n = (eval c (encode c)).bind (fun _ => Part.some n).
      — diverges everywhere when c does not halt on encode c
      — equals Part.some n for all n when c halts on encode c
    Key encoding fact: encode (φ c) ≠ 0 (φ c is a Code.comp term; Code.zero has encoding 0;
      constructor distinctness + injectivity gives encode (φ c) ≠ encode Code.zero = 0).
    Iff: IsComputationalQuine (φ c) ↔ ¬(eval c (encode c)).Dom.
      Backward (¬Dom → quine): φ c diverges everywhere; selfApply (φ c) n =
        eval (φ c) (encode (φ c) + n) = Part.none; so eval (φ c) = selfApply (φ c). ✓
      Forward (quine → ¬Dom), by contrapositive: Dom gives eval (φ c) n = Part.some n.
        At n = 0: eval (φ c) 0 = Part.some 0 and selfApply (φ c) 0 = Part.some (encode (φ c)).
        Quineness forces encode (φ c) = 0, contradicting the encoding fact. ✓
    Composing hD (hypothetical decider for IsComputationalQuine) with the computable
    map c ↦ φ c gives a decider for ¬self-halting; negating gives a decider for
    self-halting; self_halting_undecidable finishes. -/
theorem isComputationalQuine_undecidable :
    ¬ComputablePred (fun c : Code => IsComputationalQuine c) := by
  intro hD
  apply self_halting_undecidable
  -- φ c: run c on encode c; if halts return input; if diverges return nothing
  let φ : Code → Code := fun c =>
    Code.comp Code.right
      (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                 (Code.pair Code.left Code.right))
  -- Behavioral lemma: eval (φ c) n = (eval c (encode c)).bind (fun _ => Part.some n)
  -- Proved by case-splitting on whether eval c (encode c) has a value.
  have φ_eval : ∀ (c : Code) (n : ℕ),
      eval (φ c) n = (eval c (Encodable.encode c)).bind (fun _ => Part.some n) := by
    intro c n
    simp only [φ]
    rcases Part.eq_none_or_eq_some (eval c (Encodable.encode c)) with h | ⟨v, h⟩
    · -- Diverge: eval c (encode c) = Part.none → eval (φ c) n = Part.none
      rw [h, Part.bind_none]
      -- inner comp evaluates to Part.none
      have hc : eval (Code.comp c (Code.const (Encodable.encode c))) n = Part.none := by
        show eval (Code.const (Encodable.encode c)) n >>= eval c = Part.none
        simp [eval_const, h]
      -- pair with Part.none first arg evaluates to Part.none
      have hp : eval (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                                 (Code.pair Code.left Code.right)) n = Part.none := by
        show Nat.pair <$> eval (Code.comp c (Code.const (Encodable.encode c))) n
                     <*> eval (Code.pair Code.left Code.right) n = Part.none
        rw [hc, Part.map_eq_map, Part.map_none]
        simp only [Seq.seq, Part.bind]
        exact Part.assert_neg Part.not_none_dom
      -- outer comp: eval pair >>= eval right = Part.none >>= _ = Part.none
      show eval (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                            (Code.pair Code.left Code.right)) n >>= eval Code.right = Part.none
      rw [hp]; exact Part.bind_none _
    · -- Halting: eval c (encode c) = Part.some v → eval (φ c) n = Part.some n
      rw [h, Part.bind_some]
      have hc : eval (Code.comp c (Code.const (Encodable.encode c))) n = Part.some v := by
        show eval (Code.const (Encodable.encode c)) n >>= eval c = Part.some v
        simp [eval_const, h]
      -- eval (pair left right) n = Part.some n (definitional: ↑f applies to give Part.some)
      have h_lr : eval (Code.pair Code.left Code.right) n = Part.some n := by
        show Nat.pair <$> (Part.some n.unpair.1) <*> (Part.some n.unpair.2) = Part.some n
        rw [Part.map_eq_map, Part.map_some]
        -- Part.some (Nat.pair n.unpair.1) <*> Part.some n.unpair.2 = Part.some n
        show Part.bind (Part.some (Nat.pair n.unpair.1)) (fun f => f <$> Part.some n.unpair.2) = Part.some n
        rw [Part.bind_some]
        simp [Part.map_eq_map, Part.map_some, Nat.pair_unpair]
      have hp : eval (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                                 (Code.pair Code.left Code.right)) n = Part.some (Nat.pair v n) := by
        show Nat.pair <$> eval (Code.comp c (Code.const (Encodable.encode c))) n
                     <*> eval (Code.pair Code.left Code.right) n = Part.some (Nat.pair v n)
        rw [hc, h_lr, Part.map_eq_map, Part.map_some]
        -- Part.some (Nat.pair v) <*> Part.some n = Part.some (Nat.pair v n)
        show Part.bind (Part.some (Nat.pair v)) (fun f => f <$> Part.some n) = Part.some (Nat.pair v n)
        rw [Part.bind_some]
        simp [Part.map_eq_map, Part.map_some]
      -- outer comp: Part.bind (eval pair n) (eval right) = Part.some n
      show Part.bind (eval (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                                       (Code.pair Code.left Code.right)) n) (eval Code.right) = Part.some n
      rw [hp, Part.bind_some]
      show Part.some (Nat.pair v n).unpair.2 = Part.some n
      simp [Nat.unpair_pair]
  -- Encoding: encode (φ c) ≠ 0 for all c
  have φ_enc : ∀ c : Code, Encodable.encode (φ c) ≠ 0 := by
    intro c heq
    have h0 : Encodable.encode Code.zero = 0 := by decide
    have hne : φ c ≠ Code.zero := by simp [φ]
    exact hne (Encodable.encode_inj.mp (heq.trans h0.symm))
  -- IsComputationalQuine (φ c) ↔ ¬(eval c (encode c)).Dom
  have φ_iff : ∀ c : Code,
      IsComputationalQuine (φ c) ↔ ¬(eval c (Encodable.encode c)).Dom := by
    intro c
    constructor
    · -- quine → ¬Dom: contrapositive — Dom → not a quine
      contrapose!
      intro h_dom hq
      -- extract a value from Dom
      have hv : eval c (Encodable.encode c) = Part.some ((eval c (Encodable.encode c)).get h_dom) :=
        (Part.some_get h_dom).symm
      -- eval (φ c) n = Part.some n for all n
      have heval : ∀ n, eval (φ c) n = Part.some n := fun n => by
        rw [φ_eval, hv, Part.bind_some]
      -- quineness at 0: eval (φ c) 0 = selfApply (φ c) 0
      have h0 := congr_fun hq 0
      simp only [selfApply] at h0
      rw [heval 0, heval (Encodable.encode (φ c) + 0)] at h0
      -- Part.some 0 = Part.some (encode (φ c) + 0) → encode (φ c) = 0
      have henc : Encodable.encode (φ c) = 0 := by
        have := Part.some_inj.mp h0
        omega
      exact φ_enc c henc
    · -- ¬Dom → quine: both sides Part.none, equal trivially
      intro h_not
      funext n
      have hdiv : eval c (Encodable.encode c) = Part.none := Part.eq_none_iff'.mpr h_not
      -- LHS: eval (φ c) n = Part.none
      rw [φ_eval, hdiv, Part.bind_none]
      -- RHS: selfApply (φ c) n = eval (φ c) (encode (φ c) + n) = Part.none
      simp only [selfApply]
      rw [φ_eval, hdiv, Part.bind_none]
  -- Computability of c ↦ φ c: each Code constructor application is primitive recursive
  have φ_comp : Computable φ := by
    show Computable (fun c : Code => Code.comp Code.right
        (Code.pair (Code.comp c (Code.const (Encodable.encode c)))
                   (Code.pair Code.left Code.right)))
    apply Primrec.to_comp
    exact primrec₂_comp.comp (Primrec.const Code.right)
      (primrec₂_pair.comp
        (primrec₂_comp.comp Primrec.id (primrec_const.comp Primrec.encode))
        (Primrec.const (Code.pair Code.left Code.right)))
  -- Compose: hD ∘ φ gives decider for ¬self-halting; negate for self-halting
  -- hD = ⟨instD, hD_comp⟩ where instD : DecidablePred IsComputationalQuine
  rcases hD with ⟨instD, hD_comp⟩
  have hComp_phi : ComputablePred (fun c : Code => IsComputationalQuine (φ c)) :=
    ⟨fun c => instD (φ c), hD_comp.comp φ_comp⟩
  have hNeg : ComputablePred (fun c : Code => ¬(eval c (Encodable.encode c)).Dom) :=
    hComp_phi.of_eq (fun c => φ_iff c)
  exact hNeg.not.of_eq (fun c => not_not)

/-- The family of computational quines is infinite: for any n, a quine with
    Gödel number greater than n exists.
    Combined with quine_goedel_injective, this gives an infinite injection into quines.
    Note what witnesses it: the constant codes. So the family is unbounded, and this
    theorem does not show its members are instantiation bottoms — reading it as "the
    DA-2 succession has no finite bound" is the framework's interpretation.
    Proof: Code.const k is a quine for every k (constant functions satisfy the selfApply
    condition: both sides reduce to Part.some k). Code.const is injective (Mathlib:
    const_inj) and Encodable.encode is injective, so encode ∘ Code.const is an injective
    map ℕ → ℕ with infinite range — hence unbounded. No padding lemma required. -/
theorem infinite_quine_family :
    ∀ n : ℕ, ∃ c : Code, IsComputationalQuine c ∧ n < Encodable.encode c := by
  intro n
  -- Code.const k always returns k regardless of input, so both sides of eval c = selfApply c
  -- reduce to Part.some k: constant functions are quines.
  have hconst_quine : ∀ k : ℕ, IsComputationalQuine (Code.const k) := fun k => by
    show eval (Code.const k) = selfApply (Code.const k)
    funext m
    simp [selfApply, eval_const]
  -- encode ∘ Code.const is injective: const_inj (Mathlib) + encode_inj
  have hinj : Function.Injective (fun k : ℕ => Encodable.encode (Code.const k)) :=
    fun a b h => const_inj (Encodable.encode_inj.mp h)
  -- Injective ℕ → ℕ has infinite range, hence unbounded
  have hinf : (Set.range (fun k : ℕ => Encodable.encode (Code.const k))).Infinite :=
    Set.infinite_range_of_injective hinj
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n < Encodable.encode (Code.const k) := by
    by_contra h
    push Not at h
    apply hinf
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range (n + 1)))
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (h k)
  exact ⟨Code.const k, hconst_quine k, hk⟩

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox ZeroParadox ZPSemilattice ZeroParadox

#print axioms t_comp
#print axioms kleene_quine_is_bot
#print axioms da1_computational
#print axioms da1_paths_unified
#print axioms description_instantiation_gap_closed
#print axioms kleene_fixed_point_exists
#print axioms roger_fixed_point_exists
#print axioms selfApply_partrec
#print axioms computational_quine_exists
#print axioms da1_closed_concrete
#print axioms isComputationalQuine_undecidable
#print axioms infinite_quine_family
#print axioms self_halting_undecidable
#print axioms quine_period_is_goedel
#print axioms quine_goedel_injective

end PurityCheck
