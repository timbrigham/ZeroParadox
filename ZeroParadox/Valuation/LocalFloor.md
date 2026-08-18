# Why the 0-spine is standing still, and whose result this already is

Argument, scope and prior art for `ZeroParadox/Valuation/LocalFloor.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The discriminator is a nonzero digit

`zero_branch_same` and `one_branch_new` make the file's prose claim checkable: a child's local floor
is a NEW floor only when the step branches away. Descending 0-ward returns the same floor.

> **You only get a new bottom if you actually branch away. Going 0-ward is standing still.**

⚠ **The distinctness is earned, not stipulated.** `localBotEnd` is deliberately NOT injective, so
`one_branch_new` is a fact about digits rather than about a label. The alternative construction —
bolt an instantiation counter onto the state and let the index do the work — would prove novelty by
stipulation, and would be exactly as empty as a trivially-inhabited requirements class.

⚠ **SCOPE, and it is narrower than "branches in general".** The content is about the **0-spine**:
appending `0` lands on the same end because an all-zero tail is the floor's own tail. `one_branch_new`
is the single-digit case, and nothing here treats an arbitrary branching pattern.

**What it settles for the framework.** It QUALIFIES the commitment that the snap-arc returns to a new
bottom — neither confirming nor refuting it. A new bottom is obtained exactly when the step branches
away. `ε₀ ≠ ⊥` is untouched bedrock (`epsilon0_ne_bot`), and nothing here identifies any rung with ⊥.

## Prior art — neither statement is new, and the closest forms are in the pinned Mathlib

* **`Nat.ofDigits_append`** — both statements are its trailing-digit corollaries.
* **`Turing.ListBlank` / `Turing.BlankExtends`** — Mathlib's quotient of finite lists by trailing
  `default` — is `localBotEnd`'s construction under another name, and the 0-branch case is that
  quotient's defining relation. ⚠ **This is the second time this corpus has been adjacent to
  `Turing.*` without saying so**; the first was `Occurrence.lean`'s carrier being exactly Mathlib's
  `StateTransition`.
* **Cobos & Navas**, arXiv:1911.00929v2, p. 8 § 3 — the digit-word→natural encoding
  `N(w) = a₀ + a₁p + ⋯`. Filed in the project's paper library.

**The deliverable here was a pointer, not a construction.** Per the standing rule: when a question
turns out to be already proved, write the one line of consequence at the site the reader lands on and
name the canonical home — do not add an elementary instantiation.
