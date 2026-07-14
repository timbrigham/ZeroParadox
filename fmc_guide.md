# A Reader's Guide to "Forced but Not Proved"

*The plain-language companion to [fmc.md](fmc.md). This is the on-ramp; the precise, technical version lives there.*

Mathematical claims do not all come with the same certainty. Some are proved outright. Some are argued for, carefully, without being proved. Some are choices we make on purpose. And some are still open. This framework labels every claim by which of these it is, so you never have to guess how sure we are. This guide explains those labels in plain language.

## Four Levels of Confidence

- **Proved (a theorem).** A computer has checked the argument step by step against a fixed set of rules. You can download the code and check it yourself. When we say "proved," we mean this, and nothing weaker.
- **Forced (a Forced Metatheoretic Commitment).** Sometimes a choice cannot be proved inside the system, but it is not free either: every alternative we can find fails for a stated reason, so the choice is forced by elimination. When we call something forced, we also name the one thing that would change our mind. It is stronger than a preference and weaker than a proof, and we never dress it up as either.
- **Chosen (a modeling commitment).** Some things we simply decide, on purpose, because they are the natural way to read the results, and we could honestly have chosen otherwise. We label these as choices so they are never mistaken for proofs.
- **Open.** Some questions we have not answered. We keep a public list of them.

## What Is Self-Reference?

Self-reference is simply something that points back at itself. A sentence can do it ("this sentence has five words"). A drawing can do it, when it contains a smaller copy of itself. The version that matters here is a thing that *contains* itself: a collection whose only member is that very collection. It sounds strange, and ordinary mathematics usually forbids it, which is part of why it takes care to handle.

Why does it keep coming up in what follows? Because this framework needs an origin that cannot be pinned down from anywhere outside itself. An empty bottom can always be described from some external standpoint, but a bottom that contains itself is defined entirely by itself, with no outside vantage on it. That self-contained quality, not emptiness, is the property the framework is built on.

## What "Forced" Means, With a Real Example

The framework needs a foundational object, a "bottom," that contains itself. Three ways to handle that:

- Ordinary set theory (with an axiom called Foundation) forbids anything from containing itself. That is **too strict**: it rules the bottom out entirely.
- A looser alternative (an axiom due to Boffa) allows such an object but lets there be many different ones. That is **too permissive**: it never pins down a single bottom.
- One specific rule (the Anti-Foundation Axiom) allows exactly one collection whose only member is itself. Not none, not many. One.

Too strict on one side, too loose on the other, exactly one fit in the middle. That squeeze is why we say the choice is forced rather than free.

And here is the honest part. This is an argument, not a proof, and we say so. We even name what would overturn it: if someone showed that all of the framework's own requirements could be met by a bottom that does *not* contain itself, the argument would collapse. That standing invitation to prove us wrong is what keeps "forced" honest, and it is what separates a forced commitment from a hopeful assumption.

## The Framework's Biggest Single Choice

It is easy to state as a question: **does nothing contain nothing?** In plain English that sounds like an empty truism, but the word "nothing" is quietly doing two jobs (the foundational bottom, and plain emptiness), so it is really a sharp question: is the bottom an empty thing that contains nothing at all, or a thing that contains itself?

Both answers are mathematically consistent. This is a fork in the road, not a fact waiting to be discovered, and the framework takes the second road: a bottom that contains itself. One way to picture the choice: to contain yourself is to refer to yourself, and referring is an act, so a self-containing bottom has an act of its own, pointing back at itself, where an empty bottom does nothing of the kind. What that self-reference buys is the property the framework is after: the bottom is defined only by itself, with no external vantage to pin it down.

A related choice: this same bottom turns up in several different areas of mathematics, wearing a different costume in each: a self-copying program, a self-containing collection, a point where a certain scale runs to infinity. The framework reads all of them as one and the same object. That reading is a genuine choice, not a proof. In fact the areas are different enough that "these are literally the same object" is not even a well-formed mathematical statement across all of them, so claiming it as a theorem would be claiming more than can be said. We label it a choice, and say so plainly.

None of the framings in this section, "does nothing contain nothing" or "a bottom that contains itself," are proofs. They are ways to understand the choices the framework makes. The proofs live elsewhere, and they are labeled proofs.

## Why We Bother Labeling

The value of a framework like this is not in how grand it sounds. It is in how honestly you can tell what it has and has not established. Every claim here is tagged by its confidence level so that any reader, expert or not, can see exactly how much is proved, how much is argued, and how much is chosen. Keeping that line sharp is the whole point. If we ever blur it, we have failed at the thing that matters most.

*For the precise version, the four criteria a forced commitment must meet, the named falsifiers, and the full list of claims by level, see [fmc.md](fmc.md) and [CLAIMS.md](CLAIMS.md).*
