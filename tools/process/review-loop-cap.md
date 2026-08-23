# Review-loop mechanics — round counting and the verbatim brief block

**Routed from `CLAUDE.md` § *Review-Loop Cap*.** That section carries the stopping rule and the
severity tiering, which stay there because they are semantics a reviewer must act on. This file carries
the mechanics: who bumps the counter, and the block that goes into every review brief.

Enforcer and authority for the caps themselves: `tools/verify/gate_round.py` (`BEDROCK_CAP` /
`ORDINARY_CAP`). **Change a cap there and nowhere else.**

## The cap is enforced by the REVIEWER, not by the caller

**A rule about a loop does not fire from inside the loop.** Each round is locally justified — *"a gate
found real defects; fix them"* — so the caller never evaluates the trigger. On 2026-07-19 three rounds
ran against a 2-round cap while the rule sat visible in the memory index, because nobody was
*counting*. The fix is structural: the reviewer stands outside the loop, so give it the number and let
it decide.

**The CALLER bumps, exactly once, before spawning the round:**

```
python tools/verify/gate_round.py bump --target <what-is-being-re-fixed>   # caller, once per ROUND
python tools/verify/gate_round.py show                                     # reviewers: read-only
```

**Always pass `--target`.** Use a stable slug for the thing being corrected, not the round's topic —
`zpp-remark-veltri-modality`, not `round-3`. It is what makes the revalidation tripwire fire on the
real signal (*the same sentence re-fixed*) rather than on round count alone. A target re-fixed three
times prints the MANDATORY CLAIM REVALIDATION protocol; follow `tools/process/claim-revalidation.md`
before drafting another fix.

`reset` at the start of a new arc or after a clean push. State lives in
`.claude-local/gate_round.json`, so it survives compaction.

**Reviewers must NEVER `bump`** — they are handed the number in the brief and may only `show`. Measured
2026-07-19: the caller bumped to round 1, a spawned reviewer ran `bump` itself, and reported round 2. A
double-increment is not cosmetic — it burns the cap early and can force a premature STOP-ORDINARY while
a bedrock defect is still live. If several gates run in one round, they all share that round's number.

## The block that goes in every review brief, with N substituted

> This is **gate round N** against a cap of 2 (ORDINARY) / 5 (BEDROCK). Your verdict must be one of:
> **PASS** — nothing found.
> **FAIL-BEDROCK** — you found a violated core invariant, a FABRICATED external-source claim, or a false
> premise carrying a conclusion. The loop continues.
> **STOP-ORDINARY** — round N is past the ordinary cap and nothing you found is bedrock-tier. Report the
> findings, then state explicitly that the correct action is to PUSH, not to iterate. Do not recommend
> another round.
> If N is past the ordinary cap, you must actively choose between FAIL-BEDROCK and STOP-ORDINARY — a bare
> "FAIL" is not a valid verdict, because it hands the stopping decision back to the party inside the loop.
>
> **If N ≥ 3, or if this text is a passage you are being asked to re-check for the third time: do NOT
> report a wording fix.** Report the CLAIM the passage exists to support, whether anything actually
> establishes it, and what measurement would settle it. Watch specifically for modal claims —
> "not a necessity", "an artifact", "in principle", "removable", "eliminable" — which no footprint
> measurement can establish (accidental needs an EXHIBITED clean proof; essential needs a REDUCTION;
> `#print axioms` follows the STATEMENT, so a TYPE carrying an axiom makes "removable" false for every
> possible proof). **A verdict that only re-words a passage that has already been re-worded twice is
> not a useful verdict.** Recommending DELETION is in scope and is often the right answer when an
> accurate statement already lives in a checkable file.

## Two measured reasons the loop cannot converge, which the cap exists to bound

1. **Fixes introduce errors.** Every fix is new prose carrying new claims. Two of round 3's eight
   findings were created by round 2's fixes. A loop whose corrections generate errors asymptotes above
   zero.
2. **Fix-the-site, not-the-class.** Three of round 3's findings were unpropagated instances of round 2's
   fixes. **Before declaring a kill fixed, grep the corpus for the CLAIM, not the named file.** Note
   that retractions quoting an error pollute that search — read hits, do not count them.
