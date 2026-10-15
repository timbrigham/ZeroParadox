# ChoicePurityInvariant — ride-along documentation

Moved from `ZeroParadox/Computability/ChoicePurityInvariant.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

In the sections below, "this file" and "here" refer to
`ZeroParadox/Computability/ChoicePurityInvariant.lean`.

## The honest answer, and what the Lean witnesses

A proposition about a proof cannot see that proof's axiom footprint: a predicate on the proofs of one
proposition takes the same value at every proof (proof irrelevance; measured 2026-10-14 by the `example`
just before this file's `PurityCheck` section, which closes by `Iff.rfl`), so no proposition about the
proof can say "this proof term omits `Classical.choice`." So "μ is choice-free" cannot be made
*directly* load-bearing in a statement; the footprint is read at the meta level (`#print axioms`), not
by a proposition about the proof. The only way to put constructive content IN the statement is to
exhibit the μ-witness through a genuinely constructive proxy. That is what this file does, and it is the load-bearing new
content over `fix_isEmpty`:

* **μ side — a strictly more constructive witness than the existing one.** `QPF.Fix idPF_Coalgebra.Obj` is by
  definition `Quotient (Wsetoid : Setoid idPF_Coalgebra.W)` with `idPF_Coalgebra.W = WType idPF_Coalgebra.B`. We prove
  `IsEmpty idPF_Coalgebra.W` **by the bare inductive `WType` eliminator** (`w_isEmpty`) — no `QPF.Fix.ind`, no
  `Liftp`, no quotient machinery. That term has footprint `[]` (NO axioms — not even `Quot.sound`),
  strictly tighter than `fix_isEmpty`'s `[propext, Quot.sound]`. `IsEmpty (Fix idPF_Coalgebra.Obj)`
  (`fix_isEmpty_constructive`) then follows using `Quot.exists_rep`, and is measured **fully
  axiom-free** — strictly tighter than the existing `fix_isEmpty`. The μ-emptiness of the root is thus
  witnessed by structural recursion on a plain inductive type.

* **ν side — choice cannot be made load-bearing.** The strongest honest in-statement claim is
  `Nonempty (Cofix idPF_Coalgebra.Obj)` with the corecursion term as witness (re-exported as `cofix_nonempty'`),
  whose footprint carries `Classical.choice` from Mathlib's M-type / `Cofix.corec`. We do **not**
  claim ν *requires* choice — but be precise about what is measured (2026-08-03). `QPF.Cofix` carries
  `Classical.choice` **in the type**, so this footprint is **not removable by rewriting the proof**;
  an earlier version of this line said "constructible choice-free in principle", which was an
  unmeasured inference. What makes it an *artifact* is the pair: `PFunctor.M`'s FORMER and
  constructors are axiom-free while its DESTRUCTOR (`M.children`/`M.dest`) is **not** — that is where
  the axiom originates — and `strict_cofix_nonempty`
  (`ZeroParadox/Computability/RootCutTrichotomy.lean`) proves the same ν-inhabitation **over that
  M-type** with **no axioms at all**, by only building and never destructing. So the choice belongs
  to the QPF *quotient layer*, and escaping it means changing the carrier rather than cleaning the
  argument.
  Recorded in the PurityCheck comment, not asserted as a theorem.

  **Prior art, and READ THE SETTING — each of these three lives in a different type theory, and the
  differences are the whole point of the block.**
  * **Altenkirch, Ghani, Hancock, McBride, Morris, *Indexed Containers*** (JFP 25, 2015) — **the
    Axiom-K citation, and the closest setting to this file.** It says so in its own words: it relies
    on axiom K, and notes that K together with function extensionality *"corresponds to extensional
    Type Theory"*. That is the setting the claim here is about, since Lean is an Axiom-K / UIP theory
    (the corpus says so itself in `ZeroParadox/Category/BottomUndecidable.lean`: "In Lean 4 UIP holds
    for every type").
  * **Abbott, Altenkirch, Ghani, "Containers: constructing strictly positive types"**, TCS
    342(1):3-27, 2005 — the **precursor, in EXTENSIONAL MLTT**, not Axiom-K. Its own text: *"We use
    here the language of extensional Martin-Löf Type Theory."* Cite it as the origin of the container
    treatment; do **not** cite it for the Axiom-K setting. *(That attribution was wrong here on
    2026-08-02 and is corrected — the error the block's own "READ THE SETTING" premise exists to
    catch, made one reference below the heading.)*
  * **Ahrens, Capriotti, Spadotti, "Non-wellfounded trees in Homotopy Type Theory"** (TLCA 2015,
    LIPIcs 38:17-30, arXiv:1504.02949) constructs the final coalgebra of a polynomial functor as an
    ω-limit in intensional MLTT, and says it *generalizes* the Altenkirch et al. construction *"to the
    whole of HoTT"*. **Its univalence dependency is narrower than stated here previously**: ACS says
    *"we make minimal use of univalence itself: Lemma 5 is the only result that uses it directly"* —
    and Lemma 5 is the **uniqueness** result, not the construction, which needs only function
    extensionality. Lean has function extensionality. So ACS is **not** simply "one setting removed";
    its construction is closer to applicable here than a univalence label suggests, and only its
    uniqueness half genuinely needs the stronger axiom.
  * **Veltri, FSCD 2021** — cite for **contrast only**. His subject is the **finite powerset** functor,
    which is *not* polynomial, and his headline results run the other way — certain constructions
    there are obtained ASSUMING choice principles rather than shown to need them, and his own
    preferred coinductive construction needs neither choice nor LLPO. The one genuine necessity
    he proves is of LLPO, a logic taboo, not of choice. He is apt as background — he treats the
    polynomial case explicitly as contrast, his
    `Tree` is the final `List`-coalgebra, and he himself hands the polynomial fact to Ahrens et al.

The bundle `root_purity_split` packages both honest halves: the μ-witness is propositionally derivable
from a purely structural eliminator AND the ν-inhabitant is a concrete corecursion term, in one
statement. The *content* that is genuinely new is `w_isEmpty` / `fix_isEmpty_constructive`: a μ-witness
inhabiting the constructive (choice-and-propext-free, then choice-free) namespace, derived without any
choice-dependent or quotient-quotient-collapse lemma.

## Formal Overview

`PFunctor.W P = WType P.B`, an ordinary inductive type. For `idPF_Coalgebra` (`A = PUnit`, `B = fun _ => PUnit`)
there is no leaf (no head `a` with `B a` empty), so `WType.recOn` with motive `fun _ => False`
discharges emptiness: each node needs its `PUnit`-indexed child already refuted, and `PUnit.unit`
supplies that contradiction. `QPF.Fix idPF_Coalgebra.Obj = Quotient (Wsetoid)` is then empty because every class
has a representative (`Quot.exists_rep`) and the representative is impossible. The ν inhabitant is the
self-unfolding corecursion node (`ZeroParadox.cofix_nonempty`).

What is PROVED is exactly: `IsEmpty idPF_Coalgebra.W` by the inductive eliminator (no axioms), `IsEmpty (Fix
idPF_Coalgebra.Obj)` from it, and `Nonempty (Cofix idPF_Coalgebra.Obj)`; footprints: the `PurityCheck` section of
`ZeroParadox/Computability/ChoicePurityInvariant.lean`. The VERDICT on the pre-registered
fork — whether this constitutes a *new theorem-level invariant* or only a *measured comment* — is the
finding, recorded in that section's VERDICT comment. The in-statement constructive
upgrade on the μ side is real; the "ν needs choice" half remains a fenced comment, not a theorem.

