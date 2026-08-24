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
| "NOT IN THE LIBRARY" IS A CLAIM | `R-NOTINLIB` | `tools/process/not-in-the-library.md` |
| Review-Loop Cap — Severity-Tiered | `R-LOOPCAP` | `tools/process/review-loop-cap.md` |
| NEVER truncate the output of a hook-running command | `R-TRUNC` | `tools/process/push-gate-bypass.md` |
| Staging — NAMED PATHS, never `-A` | `R-STAGE` | `tools/process/staging.md` |
| Editorial Review Gate | `R-ER` | `tools/process/review-gates.md` |
| Adversary Review Gate | `R-AR` | `tools/process/review-gates.md` || Prior-Art Search — Trigger Conditions and Gate | `R-PRIORART` | `tools/process/prior-art.md` |
| Guiding Principles / Repository Nature / Private Working Folder / Document Versioning | `R-CONTEXT` | `tools/process/repository-layout.md` || GitHub Releases and Zenodo Snapshots | `R-RELEASE` | `tools/process/document-workflow.md` |
| register.md — Canonical Version Registry / Build Script Hash Integrity | `R-REGISTER` | `tools/process/document-workflow.md` |
| Companion PDF Diagram Layout Standards / PDF Build Standards | `R-DIAGRAM` | `tools/process/document-workflow.md` |
| Companion Document Versioning / Vocabulary Reference Guide | `R-COMPANION` | `tools/process/document-workflow.md` || scripts/ is the build scripts' ONLY home | `R-SCRIPTS` | `tools/process/repository-layout.md` |
| Lean↔PDF Consistency / File-Reference Citation Convention | `R-LEANPDF` | `tools/process/document-workflow.md` |
| Development Environment | `R-SHELL` | `inline — no body` |
| README/GUIDE Maintenance / Transparency notices (RETIRED) / Superseding Document Versions | `R-INDEXES` | `tools/process/indexes-and-superseding.md` || Theorem/Proposition/Lemma Naming Convention (+ CC-2, keystone, MC-1 status) | `R-NAMING` | `tools/process/naming-and-labels.md` |
| GitHub Issues — Transparency and Engagement Policy | `R-ISSUES` | `tools/process/naming-and-labels.md` || Framework Structure (for context) | `R-FRAMEWORK` | `tools/process/lean-development.md` |
| Session Handoff File / Four-Fingerprint Scan / Communication Quality / Reviewer Feedback | `R-HANDOFF` | `tools/process/lean-development.md` |
| High-Value Insight Capture — Standing Rule | `R-CAPTURE` | `tools/process/lean-development.md` |
| Development mode — LOAD THE SECTION BEFORE YOU WORK | `R-DEVMODE` | `tools/process/lean-development.md` |
| Stub-First Protocol / Proof Documentation Workflow / Operational Rules / .claudecodes | `R-LEANDEV` | `tools/process/lean-development.md` || THE GATE-ENFORCED CONVENTIONS | `R-GATED` | `tools/process/gated-conventions.md` |
| Every brief carries the CONTROL OBJECTS | `R-CONTROLS` | `tools/process/gated-conventions.md` |
| Rules That Must Reach Spawned Agents | `R-BRIEF` | `tools/process/gated-conventions.md` |
| Anything convertible from prose to Lean MUST be converted | `R-TOLEAN` | `tools/process/prose-to-lean.md` || Gate exemption — this file and operational meta / WHERE THINGS LIVE | `R-EXEMPT` | `tools/process/gate-exemptions.md` |
| NARRATE THE MATH — in an engineer's register | `R-NARRATE` | `tools/process/narrate-and-pipeline.md` |
| batch.py precommit BEFORE EVERY COMMIT | `R-PRECOMMIT` | `tools/process/pipeline.md` |
| The defect register — DEFECT_CLASSES.md | `R-DEFECTCLASS` | `tools/process/narrate-and-pipeline.md` || BEFORE YOU EDIT ANY `.lean` FILE | `R-EDITLEAN` | `tools/process/core-objects.md` |

## Pass record

| pass | date | unit | before | after | saved |
|---|---|---|---|---|---|
| 1 | 2026-08-23 | `:238`–`:501` (defect ledger + failure-recurs) | 264 | 41 | **223** |
| 2 | 2026-08-23 | `:333`–`:527` (core objects + commitments) | 195 | 48 | **147** |
| 3 | 2026-08-23 | `:629`–`:870` (adjacency, determinism, two-pole, revalidate) | 242 | 57 | **185** |
| 4 | 2026-08-23 | `:687`–`:986` (not-in-library, loop cap, truncation, staging, both gates) | 300 | 80 | **220** |
| 5 | 2026-08-23 | `:768`-`:868` (prior-art, repo context) | 101 | 39 | **62** |
| 6 | 2026-08-23 | `:808`-`:960` (releases, register, diagrams, companions) | 153 | 57 | **96** |
| 7 | 2026-08-23 | `:866`-`:1013` (scripts home, Lean-PDF, shell, indexes) | 148 | 55 | **93** |
| 8 | 2026-08-23 | `:922`-`:1082` (naming/labels, public issues) | 161 | 33 | **128** |
| 9 | 2026-08-23 | `:956`-end (framework, handoff, capture, dev mode, Lean) | 236 | 85 | **151** |
| 10 | 2026-08-23 | `:382`-`:628` (gated conventions, controls, briefs, prose-to-Lean) | 247 | 71 | **176** |
| 11 | 2026-08-23 | `:4`-`:237` (exemptions, layout, narrate, pipeline, defect classes) | 234 | 87 | **147** |
| 12 | 2026-08-23 | `:134`-`:186` (before you edit a .lean file) | 53 | 17 | **36** |

**File total: 2338 → 686 lines (−1652, 71%).**

⚠ **The cap is still unset, deliberately.** Per the contract, the first cap is set BY MEASUREMENT
after the classification sweep completes, never picked as a round number mid-program. Until then
`check_claude_md.py`'s `budget` leg stays PENDING and says so on every run.
