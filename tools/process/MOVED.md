# Moved sections — old `CLAUDE.md` heading → new home

**Why this file exists.** A compressed entry can be *correct* and *unreachable*: a mid-session edit
never reaches agents spawned after it, and a rule someone half-remembers by its old heading is a
rule they cannot grep for. This is the Phase 5 delivery half of the compression program — correctness
and delivery fail independently, and the second failure is the invisible one.

**How to use it.** If someone refers to a rule you do not recognise, or you remember a heading that
is no longer in `CLAUDE.md`, grep here first. Nothing has been deleted; every line of every moved
section is preserved verbatim in the body named below.

| old `CLAUDE.md` heading | now | body |
|---|---|---|
| The open-defect ledger — `.claude-local/DEFECTS.md`. Read it before choosing what to work on. | `R-DEFECTS` | `tools/process/defect-ledger.md` |
| ⭐⭐⭐ WHEN A FAILURE RECURS: the rule is wrong, not the reader. Run this list. | `R-RECUR` | `tools/process/recurrence-protocol.md` |
| — rung 5 / non-convergence, formerly inside the section above | `R-NOCONV` | `tools/process/non-convergence.md` |
| Core Objects — Read the Lean First (Hard Rule) | `R-COREOBJ` | `tools/process/core-objects.md` |
| — Bedrock invariants, formerly inside the section above | `R-BEDROCK` | `tools/process/core-objects.md` |
| Commitments Go In HYPOTHESES, Data Goes In BRACKETS | `R-COMMIT` | `tools/process/commitments-in-hypotheses.md` |
| The recurring defect is UNSTATED ADJACENCY | `R-ADJACENT` | `tools/process/unstated-adjacency.md` |
| Determinism is the SINGLE recurring cost | `R-DETERMINISM` | `tools/process/determinism.md` |
| The Two-Pole Test — Hard Rule | `R-TWOPOLE` | `tools/process/two-pole-test.md` |
| Prose that resists correction is a CLAIM defect | `R-REVALIDATE` | `tools/process/claim-revalidation.md` |

## Pass record

| pass | date | unit | before | after | saved |
|---|---|---|---|---|---|
| 1 | 2026-08-23 | `:238`–`:501` (defect ledger + failure-recurs) | 264 | 41 | **223** |
| 2 | 2026-08-23 | `:333`–`:527` (core objects + commitments) | 195 | 48 | **147** |
| 3 | 2026-08-23 | `:629`–`:870` (adjacency, determinism, two-pole, revalidate) | 242 | 57 | **185** |

**File total: 2338 → 1786 lines (−552, 24%).**

⚠ **The cap is still unset, deliberately.** Per the contract, the first cap is set BY MEASUREMENT
after the classification sweep completes, never picked as a round number mid-program. Until then
`check_claude_md.py`'s `budget` leg stays PENDING and says so on every run.
