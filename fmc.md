# Forced Metatheoretic Commitment (FMC)

## Gloss
<!-- This short gloss is the drop-in version for use in PDF document bodies. -->


A Forced Metatheoretic Commitment is a foundational choice whose alternatives the framework's internal structure rules out by argument, not proof, and falsifiably: a viable alternative would overturn it.

## Why metatheoretic work at all?

They are argued, not provable within the formal system. This commitment lives in the metatheory, outside what the Lean kernel verifies, and is falsifiable: a viable alternative would overturn it.

## The Roots

FMC is a disciplined, falsifiable form of the "intrinsic justification" of axioms described by Gödel (1964) and Penelope Maddy (1988, 2011); see References. Intrinsic justification is itself a contested notion, classically resting on intuition or self-evidence (Maddy, for one, leans toward extrinsic justification by consequences). That contestedness is exactly why we formalize it: an FMC replaces "self-evident" with an explicit argument, a named falsifier, and a clear line between what is proved and what is argued. We are making inferences, with as much reason and structure behind them as possible. Each Forced Metatheoretic Commitment names what would overturn it; that named falsifier is the standing invitation to refute it.

## How and why we use it

We try to avoid project-specific vernacular. FMC names a status the framework genuinely needs and no existing label fit.

It is stronger than a free modeling choice (the alternatives are argued away, not merely declined). By definition it is weaker than a theorem: the ruling-out is a metatheoretic "squeeze" argument, not a derivation in the formal system. As such, it sits between a Conditional Claim and a Theorem.

Naming it honestly, rather than calling it "proved" or burying it as a free assumption, is what keeps the foundations legible: a reader sees exactly how much is established, and how.

## Canonical definition

A claim is an FMC iff asserted with all four of:

* **Structural argument:** the argument ruling out the alternatives is stated or cited.
* **Falsifier:** what would overturn it is named. "Forced" means no alternative survives the argument, not proved necessary.
* **Metatheoretic scope:** explicitly outside the formal system / not Lean-verified; not presented as a theorem.
* **Proved part cited separately:** any formally proved component is distinguished from the argued component.

Dropping any one turns an FMC into an overclaim (argument read as settled necessity) or an underclaim (a forced commitment buried as a free choice).

## References

* Kurt Gödel, "What is Cantor's Continuum Problem?" (1964 version), in P. Benacerraf and H. Putnam (eds.), *Philosophy of Mathematics: Selected Readings*, pp. 258–273. Origin of the distinction: Gödel contrasts an axiom's "intrinsic necessity" with justification by its "success" (fruitfulness in consequences), which the later literature calls extrinsic justification.
* Penelope Maddy, "Believing the Axioms. I," *The Journal of Symbolic Logic* 53(2), 1988, pp. 481–511.
* Penelope Maddy, "Believing the Axioms. II," *The Journal of Symbolic Logic* 53(3), 1988, pp. 736–764.
* Penelope Maddy, *Defending the Axioms: On the Philosophical Foundations of Set Theory*, Oxford University Press, 2011.
