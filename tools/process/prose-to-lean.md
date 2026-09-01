# Anything convertible from prose to Lean — the three tiers and the generic-witness trap

**Body for `CLAUDE.md` § `R-TOLEAN`.** The rule is there; the worked bedrock finding of
2026-08-08, the `IO.println` trap, the failing-probe-is-a-finding case and the
null case where genericity IS the claim are here.

---

## Anything convertible from prose to Lean MUST be converted. (Tim, 2026-08-08.)

> *"anything that can be converted from prose to lean should be done, with a single line statement
> or read reference for it right there"*

**THE RULE.** If a sentence makes a claim a declaration could carry, **write the declaration** and
leave ONE line at the site — a `Statement:`/`Reading:` gloss, or a pointer. Prose is the fallback
for what cannot elaborate, never the default. This generalizes the § above: that one caps prose by
volume, this one removes the *reason* to write it.

**THREE TIERS, in order of preference. Reach for the lowest-numbered one that fits:**
1. **An `example` that fails to compile when the claim is wrong.** Already the stated best form for
   `Statement:`; **now required for `Reading:` too, wherever the reading is checkable.**
2. **Emitted output** — `#print axioms`, `#check`. The machine computes it, and the **public CI log
   already carries all of it**: measured 2026-08-08 on `lean_action_ci.yml`, 1,270 `info:` lines
   including every axiom footprint and all 72 `BottomCannotBe` signatures, file-and-line prefixed,
   no truncation, regenerated per run, **retained nowhere in the repo — and that is correct.** Do
   not commit build logs; point at the workflow, never at a run id (logs expire).
3. **Prose**, only for interpretation carrying no mathematical content ("the framework calls this
   concurrency"). Label it `Reading:` and leave it alone.

**⚠ THE TRAP: `IO.println` of hand-written English is tier 3 wearing tier 2's clothes.** Measured
2026-08-08 — `#eval IO.println "Reading: the two faces coincide as a bare point."` printed that
**false** sentence, exit 0, no complaint. The machine did not compute it; it echoed it. In a log
where every other line is elaborator-derived, a typed sentence inherits authority it never earned —
this file's own *"the `#check` lines cannot overclaim, the glosses beside them absolutely can"*,
amplified rather than fixed. **Never route a claim through stdout to make it look checked.**

**A READING IS CHECKABLE WHENEVER IT CLAIMS STRENGTH, SCOPE, OR GENERICITY** — and those are the
readings that go wrong. Worked example, the bedrock finding of 2026-08-08: a `Reading:` said
`faces_iso_unique` shows the two faces of ⊥ coincide as a bare point, and that an exclusion rests on
it. Three lines refute it — `example (α : Type) : Subsingleton (α ≃ PUnit) := inferInstance`
elaborates, so the theorem holds of `Bool` and says nothing about ⊥. **That reading had been
certified accurate by an editorial gate one round earlier.** A prose round could not catch it; an
`example` makes it unwriteable. Same shape for *"the finiteness hypothesis is load-bearing"* (exhibit
the counterexample without it) and *"not* the *period, merely* a *period"* (exhibit a constant code
with a second period).

**⚠ And the probe settles it EITHER WAY — a failing `example` is a finding, not a dead end.** For
*"definitionally `t3_unreachability`"* the natural probe is `example : @t4 = @t3 := rfl`; **measured
2026-08-08, it does NOT typecheck** — `t4_chains_forward_only` carries an extra unused binder, so the
two statements are not the same type and the word *"definitionally"* was wrong. The one-line-
consequence form does elaborate. **That is the rule working**, and it is why you run the probe
instead of picking the phrasing that sounds safest.

**This is the NO-GO gauge (`.claude-local/notes/nogo_gauges_2026-06-29.md`, discipline (b) — *name
the obstruction in advance*) pointed at readings for the first time.** It also lands on the right
side of the prose rule for free: an `example` counts as **code**, not comment.

⚠ **Placement: put the `example` AFTER the `#check` it qualifies, never between the gloss and the
`#check`.** `check_prose.py` looks immediately above a `#check` for its gloss, so an interposed
`example` reads as a missing gloss and fires. Measured 2026-08-08 on the first application of this
rule. Write "the `example` below" in the gloss.

⚠⚠ **AND THE `example` MUST NOT ITSELF BE GENERIC — that is the same defect one level up, and it
happened on the second application of this rule.** To witness *"monotonicity is not the obstruction
for `Ordinal`"* an `example : Ordinal.{0} →o Ordinal.{0} := OrderHom.id` was written. **`OrderHom.id`
inhabits `α →o α` for every preorder**, so it says nothing about `Ordinal` — exactly the
`Subsingleton (α ≃ PUnit)` failure this section exists to prevent, committed four lines from where
the same file correctly fences it. **The test is the one from § *A requirements class is only
informative if something FAILS*: ask what the `example` EXCLUDES.** If it would elaborate with the
subject swapped for an arbitrary carrier, it witnesses nothing. Here the honest witness is the
ω-tower map itself, `⟨fun a => ω ^ a, fun _ _ h => opow_le_opow_right omega0_pos h⟩`.

**⚠ THAT WARNING HAS A NULL CASE, and reading it absolutely gets the answer backwards.** Ask what
the `example` excludes **relative to the claim it witnesses**, not in the abstract. When the claim
IS a universal — *"every inhabited carrier can be equipped"*, *"nothing here excludes anything"* —
a **generic** witness is the exact refutation and a specific one would be weaker. Worked example,
K1 (2026-08-10): the corpus said non-members of `ZPSemilattice` *"abound"*; the witness that settles
it is `example (L : Type) [Nonempty L] : Nonempty (ZPSemilattice L)`, which is maximally generic on
purpose, paired with `example : IsEmpty (ZPSemilattice Empty)` to pin inhabitation as the sole
obstruction. **Genericity is a defect when it is accidental and the content when it is the claim.**
This is the same shape as INVARIANT being the ratified null case of the Two-Pole Test — a rule that
fires everywhere is the cry-wolf shape this file says to narrow rather than tolerate.

**PREFER AN ANONYMOUS `example` OVER A NAMED `def`/`theorem` FOR A WITNESS — measured 2026-08-10,
it declares nothing.** `batch.py decls_in` returns `[]` for the two examples above and `['realOne']`
for a `theorem` beside them, so a witness in `example` form owes **no `#print axioms` entry and no
`ssot.json` row**, while a named one owes both plus an SJV sync. Name it only when something else
must cite it. Nothing is lost: the kernel checks an `example` exactly as hard, which is the entire
point of tier 1.
