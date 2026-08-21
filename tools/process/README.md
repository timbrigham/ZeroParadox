# `tools/process/` — the body of `CLAUDE.md`

`CLAUDE.md` is a **routing table**: a condition, the exact file to open when it fires, and one line
saying what it costs to skip. This directory holds what the routing points at.

**The split is by function, not by topic.** A rule's TRIGGER, its one-line statement and its
consequence stay in `CLAUDE.md`, because that file is injected into every session and every subagent
before anything else. The ARGUMENT — the measured case that produced the rule, the detector's failure
modes, the tables worth not re-deriving — lives here, because it is paid for only by whoever is
actually doing that work.

**Why the split works, and it is proved twice already.** Delivery is **not** injection: it is a
trigger in the injected file naming a specific path. `ZeroParadox/BottomCannotBe.lean` and its
siblings work exactly this way, and `tools/verify/README.md` is the same move for the checkers. A
control agent read `ZeroParadox/MANIFEST.md` it had never been given, purely because `CLAUDE.md`
named the path.

## The criterion for anything living here

A section may sit in this directory only with **all four** properties. Missing any one, it belongs
back in `CLAUDE.md`:

1. **An unmissable trigger** — an ACTION or a TOPIC, never a category someone must adjudicate. *"You
   are about to write a modal claim"* fires; *"when doing careful work"* does not.
2. **A named exact path**, so the pointer resolves or fails loud.
3. **A stated consequence** for skipping it.
4. **A target worth opening** — if the pointer costs more than the content, do not move the content.

⚠ **Keep the one-line WHY in every pointer.** `CLAUDE.md` records seven conventions that leaked when
they were stated as bare imperatives. A pointer with no reason attached is a bare imperative with an
extra step.

⚠ **Two sections deliberately do NOT move**, and re-proposing them is a regression: § *WHEN A FAILURE
RECURS* and § *BEFORE YOU EDIT ANY `.lean` FILE*. They govern how every other rule is applied, and
they are parked near the top of `CLAUDE.md` because position measurably determines whether a rule
fires at all.

## Review routing — declared, not inferred

**This directory is exempt from the Editorial and Adversary gates, and `/rely` covers it instead.**

The argument is the one already made for `tools/verify/**`: these files are operating instructions and
assert nothing about the mathematics, so an editorial or adversary pass has no claim to review. The
exemption is **not free** — it is a re-route, and `/rely` **blocks**.

⚠ **This is a DECLARED carve, not one derived from "it is operating instructions."** `CLAUDE.md` bans
that inference explicitly, and `.claude/commands/` is the counterexample that proves it: those files
are operating instructions too, and **both gates fire on them**, because they are surfaced on purpose
as the artifact showing how this project reviews itself.

**The fence:** anything asserting mathematics belongs in the corpus and is gated normally. A file here
that starts making claims about ⊥, the snap, or ε₀ has left this directory's scope.

## Contents

| file | opens when |
|---|---|
| `claim-revalidation.md` | a sentence has been re-fixed three times, or you are writing a modal claim ("an artifact", "in principle", "removable") |
| `review-loop-cap.md` | you are spawning a review gate and need the round mechanics and the verbatim brief block |
