# Commitments go in hypotheses, data goes in brackets — the argument

**Body for `CLAUDE.md` § `R-COMMIT`.** The rule is there; the three encodings, the worked
canonical form, and the measured 2026-07-26 bedrock findings are here.

---

## Commitments Go In HYPOTHESES, Data Goes In BRACKETS — Default Method, Hard Rule

**A commitment encoded as a typeclass field reads as data, because brackets are where data lives.
That single fact produced every bedrock defect of 2026-07-26.** State commitments as explicit
hypotheses so the signature cannot be misread.

**The test — CAN IT BE FALSE?**
- **Data** (goes in brackets): the carrier either has it or does not. `[ZPSemilattice L]` — a join with
  laws. Cannot be "wrong"; inference on it is worth keeping.
- **Commitment** (goes in a hypothesis): the framework asserts it and reality might not comply.
  "Nothing external can execute ⊥." "The bottom departs." "States are discrete."

**NEVER BUNDLE ONE INTO THE OTHER.** If a class field asserts something the framework could be wrong
about, extract it as a hypothesis on the theorems that need it. `KleeneStructure` is the worked example
of the misreading: the bracket reads as if it carries the identification that its `Code` names ⊥ of
`L`, and no field asserts that — the NO-GO gauge at the head of § II of
`ZeroParadox/Computability/Kleene.lean` says what the fields do assert. A commitment that sits in no
signature at all is what let `da1_closed_concrete` read as establishing self-execution for months.
`AbstractSelfApp` has the same shape — which is why `trivialSelfApp` inhabits it, and why "L carries
`AbstractSelfApp`, therefore …" is vacuous.

**The canonical form** (`ZeroParadox/Computability/Occurrence.lean` § VI-b):

```lean
theorem execution_requires_branching (R : σ → σ → Prop) (s : σ)
    (hfix : R s s)                      -- COMMITMENT: the bottom is its own fixed point
    (hdep : ∃ t, R s t ∧ t ≠ s) :       -- COMMITMENT: execution occurs
    ∃ t u, R s t ∧ R s u ∧ t ≠ u        -- CONSEQUENCE, not a further assumption
```

**Why this is the default and not a preference.** It is the only defence found on 2026-07-26 that
**requires nobody to remember anything** — gloss labels need discipline, review rounds need reviewers, a
type signature simply is what it is. It makes the framework's assumption load **countable** (grep the
hypotheses) instead of recoverable only by reading prose. And it would have prevented **both** bedrock
findings that day: `da1_closed_concrete` could not have been cited for self-execution with execution
visible as a hypothesis, and `t_iz_limit_is_new_null` could not have been cited for novelty with novelty
visible as one.

**Three encodings, decreasing honesty — know which you are writing:**
1. **Baked into the carrier** — `ax_b1_distinct : nullState ≠ firstAtomicState := by decide`, where
   discreteness *is* the two-element type. Invisible at every use site. **Worst.**
2. **Hidden in a class** — `[QuineHost L]`. Visible only if you know what the class carries.
   `[KleeneStructure L]` is the neighbouring hazard: the commitment it was built for is in no field, so
   the bracket shows it nowhere and reads as if it did.
3. **Explicit hypothesis.** Visible on the face of the statement. **Prefer this for anything that can be
   false.**

**Rollout — AS-TOUCHED, not a rewrite.** The class form is used widely enough that no big-bang
migration is realistic. Every new or edited commitment uses the hypothesis form immediately;
where an existing class carries a commitment, add a **companion explicit-hypothesis theorem** rather than
refactoring the class. First candidate: **AX-B1**, which is the framework's one substantive modelling
commitment and currently the least visible of the three (encoding 1). `KleeneStructure`'s identification
cannot take the hypothesis form as an equation: `botCode` is a `Code` and ⊥ of `L` is an element of `L`,
so no `=` between them is well-typed (the class docstring, `ZeroParadox/Computability/Kleene.lean` § II).
