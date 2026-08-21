# Claim revalidation — the argument, the case, and the detector

**Routed from `CLAUDE.md` § *Prose that resists correction is a CLAIM defect*.** That section carries
the rule, the trigger and the modal-claim discriminator. This file carries what produced them.

Enforcer: `tools/verify/gate_round.py` prints the MANDATORY CLAIM REVALIDATION protocol at round 3, or
as soon as the same `--target` has been re-fixed three times. Detector:
`python tools/verify/check_modal.py` (WARN at commit, `--block` at push).

## 1. The case that produced the rule (2026-08-03, Tim's call)

One remark-box sentence in ZP-P was wrong in **six consecutive versions** — v1.9 a universal, v1.10 a
doubling, v1.11 the universal restored, v1.13/v1.14 a false universal, v1.15 a false uniqueness. Four
gate rounds ran over it. **Every round passed the citations, because the citations were always
correct.**

The defect was one level down. The claim the sentence existed to support — that Mathlib's
`Classical.choice` in `cofix_nonempty` is *"an artifact, not a necessity"* — had never been measured by
anyone. One probe settled it in a minute:

```
QPF.Cofix         (the TYPE) : [propext, Classical.choice, Quot.sound]
PFunctor.M.corec             : does not depend on any axioms
```

`QPF.Cofix` carries choice **in the type**, so *no proof of any statement mentioning it can be
choice-free*. "Removable in principle" was not merely unproved — it was unprovable as stated.

The honest, measurable version nobody had written: the choice comes from Mathlib's **QPF quotient
layer**, not from the mathematics, and the corpus already witnesses the same inhabitation choice-free
(`strict_cofix_nonempty`).

⚠ **Do NOT sharpen that into "the M-type underneath is axiom-free."** The former and the constructors
are; the **destructor is not**. That sharpening is the bedrock defect recorded in § 4. That ACS is
choice-free is a separate fact — an ω-limit with no quotient layer.

**The generalizable lesson: the gates check WORDING against SOURCES. They cannot see an unmeasured
claim, and they will keep passing one forever.** Six rounds of prose editing could never have found
this. A one-minute probe did.

## 2. The protocol, when the tripwire fires

Name the claim in one line without its framing → ask what would settle it and whether anyone did that
→ probe it in the scratchpad (`lake env lean` on a standalone file needs no repo write) → then either
restate to exactly what was measured, or restate as an explicit conjecture, **or delete the sentence**.

**Deleting is legitimate and often correct.** If an accurate statement already lives in a checkable
file, published prose does not need to relitigate it — that is how the ZP-P case was finally closed
(v1.16, Tim: *"if the Lean is accurate, just delete the problem sentence"*).

**Record what the MEASUREMENT showed, not that you re-worded something.** A changelog entry saying
"clarified" after a revalidation round is the failure repeating.

## 3. `check_modal.py` — first-run yield and the detector's own failures

Baselined like `check_pov.py`: fires on NEW sites only. It flags modal vocabulary not accompanied by a
measurement, a reduction, an explicit non-claim, or a **named exhibited witness**.

**First run: 31 sites → 3 real defect clusters.**

- **A FALSE UNIVERSAL NEGATIVE LIVE IN A PUBLISHED PDF.** `ZP_Choice_Free_Core_Addendum` § III said
  *"The framework has no proven-necessity case anywhere."* Two taboo reductions exist
  (`em_of_wellOrder_comparable`, `wem_of_fixedPointFree`) and **neither was named anywhere in that
  document**. The 2026-08-01 sweep that recorded both universal negatives as removed had grepped
  `.lean` and **missed a Python build script** — so the claim survived in rendered public prose.
  **Grep the CLAIM across every surface that renders, not just the sources.**
- **The `Cofix` cluster**, including `CLAIMS.md`. Restated from inference to measurement.
- **Several sites were already honest** — retractions, `UNCLASSIFIED` tiers, explicit "does not show"
  fences. `ZeroParadox/Ordinal/SnapNucleus.lean` had measured this correctly in July, including that
  `Ordinal` the *type* is choice-free while `Ordinal.instLinearOrder` is not. **Read hits, do not count
  them.**

**⚠ THE DETECTOR SHIPPED WITH THREE FALSE-NEGATIVE PATHS, AND EVERY ONE WAS FOUND BY A PROBE RATHER
THAN BY READING THE CODE.** All three would have made a clean `0` meaningless:

1. **`#print axioms` listed as *evidence*** — so a claim beside a `PurityCheck` block was suppressed,
   which is exactly where these claims live. A footprint is the one thing that **cannot** establish a
   modal claim. Removing it surfaced two real sites at once.
2. **One wide evidence window** — a live claim passed because the word *"measured"* sat six lines away
   describing a **different** measurement. **Proximity is not aboutness.** Fixed with two tiers: weak
   tokens (`measur`, a named witness) must be in the *same sentence*; structural markers (`retracted`,
   `UNCLASSIFIED`, `NOT claimed`) may sit wider.
3. **Literal spaces in the pattern** — so any claim *wrapped across a line* was invisible, and Lean
   docstrings wrap constantly. Two fixes were needed: `\s+` between words, **and** blanking the `--` /
   `//` / quote-join separators that sit in the gap, to spaces of **equal length** so line numbers stay
   exact. The first fix alone still missed a wrapped Lean comment — measured by probe.

**VERIFY THE DETECTOR BEFORE BELIEVING A ZERO.** Plant a known-bad line *in the shape you actually
expect* — wrapped, comment-prefixed, near a purity block — confirm it fires, then remove it. A probe in
the wrong shape passes and teaches you nothing: the wrapped probe was written flat first and gave a
false all-clear. Keep a reproduction script in the scratchpad with **both** must-fire and must-suppress
controls; a checker that fires on everything is as useless as one that fires on nothing.

⚠ **AND BEFORE BELIEVING A NON-ZERO. A false POSITIVE is the more expensive error, because it
manufactures work that looks urgent.** Measured 2026-08-08: a survey of prose axiom-footprint claims
reported **6 mismatches against measured truth**, and that figure was relayed as fact before the hits
were read. Read individually, **all six were the detector's** — it attributed each bracketed axiom list
to the nearest backticked identifier, and in flowing prose the bracket normally belongs to the
*previous* clause. Three cited the bare type `Ordinal` (genuinely `[propext, Quot.sound]`) inside
sentences about declarations that inherit choice *through* it; two had the name opening the next
sentence; one was a cross-reference sitting above the declaration the claim was actually about. **True
corpus mismatches: zero.**

- **The rule: READ EVERY HIT BEFORE REPORTING A COUNT.** *"Read hits, do not count them"* is stated for
  `check_modal` and generalizes to every survey — to positives as much as to zeros.
- **Attribution-by-proximity is the specific trap.** Prose is not a table. If a detector must guess
  which declaration a sentence is *about*, its output is a **reading list, not a finding list** — label
  it that way, and resolve each entry at the artifact before it becomes a number.

## 4. The measured axiom footprints worth not re-deriving

⚠ The first version of this block listed only `PFunctor.M no axioms`, and that half-truth immediately
re-seeded a bedrock defect. **Read the table as a whole or not at all.**

```
PFunctor.M       (TYPE former) no axioms       ]  the M-type's FORMER and
PFunctor.M.mk                  no axioms       ]  CONSTRUCTORS are clean
PFunctor.M.corec               no axioms       ]
PFunctor.M.children  [propext, Classical.choice, Quot.sound]  <-- THE ORIGIN (destructor)
PFunctor.M.dest      [propext, Classical.choice, Quot.sound]
QPF.Cofix  (TYPE)    [propext, Classical.choice, Quot.sound]  <-- inherits via Mcongr/IsPrecongr
strict_cofix_nonempty          no axioms       -- clean because it only BUILDS, never destructs
Ordinal    (TYPE)              [propext, Quot.sound]                    -- choice-FREE
Ordinal.instLinearOrder        [propext, Classical.choice, Quot.sound]  -- the instance hazard

-- THE TWO LAYERS ARE CLEANLY SEPARATED. Measured 2026-08-08 after Tim asked whether
-- collapsing the hand-built ZPCategory instances would cost choice-freedom.
CategoryTheory.Category        no axioms                                -- clean base
CategoryTheory.Limits.IsLimit  [propext, Classical.choice, Quot.sound]  <-- the TYPE
  -- `IsInitial` is defined over `IsLimit`, and `ZPCategory.zpIsInitial` IS an
  -- `IsInitial`. So NO ZPCategory instance can ever be choice-free - not a defect and
  -- not removable by better proving, the same shape as `QPF.Cofix` above.
natZPCategory / nnrealZPCategory / forkZPCategory
                               [propext, Classical.choice, Quot.sound]  -- ALL of them
Preorder.smallCategory         no axioms  -- the Mathlib instance a generalization uses

ZPSemilattice        (CLASS)   no axioms  ]  the choice-free CORE, untouched by any
t_snap_derived                 no axioms  ]  of the above. Different class, different
t_snap_irreversible            no axioms  ]  base. `ZPCategory` is NOT `ZPSemilattice`,
da2_bottom_characterization    no axioms  ]  and the framework's own scoping - "the
ZPSemilattice.bot_le           no axioms  ]  framework is not choice-free; the CORE
ZPSemilattice.cc1              no axioms  ]  is" - is exactly right.
Ordinal.nfp / .epsilon         [propext, Classical.choice, Quot.sound]
padicValNat                    [propext, Classical.choice, Quot.sound]
```

*"`PFunctor.M` is axiom-free"* is true of the **type former** and says nothing about its
**eliminators**. Citing it to conclude *"the choice is not from the M-type underneath"* is a
**witness-vs-statement defect** — exactly what shipped to a published PDF on 2026-08-03 under the word
*"Measured"*, and was caught by the gate measuring it. **The choice DOES come from the M-type — from
its destructor.**

**The accurate account is stronger than the false one it replaced:** choice enters at
`M.children`/`M.dest`; `Cofix` inherits it in the type through the congruence it quotients by; and
`strict_cofix_nonempty` is axiom-free **because it only builds and never destructs**. So the escape is
not "use `M` instead of `Cofix`" generically — it is *build without destructing*. Attributing the
footprint to the **QPF quotient layer** is defensible and is the claim to keep; *"not from the M-type"*
is false and must not be re-introduced.
