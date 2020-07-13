# DProp

**DProp** ("Dee prop"): A deep embedding of classical propositional logic into Coq.

This file is a quick tutorial to using Coq as a logical framework to
study propositional logic, which is synonymous to saying we are
providing a deep embedding (a shallow embedding would like more like
the section "Minimal Logic" in the [basic Coq
tutorial](https://coq.inria.fr/tutorial/1-basic-predicate-calculus)). This
file is the backbone of a PL club presentation, as well as "homework"
for the willing.

We by defining the synax of propositional logic, taking as primitives conjunction, negation, and the top element. From there we define the semantics, but instead of looking at propositions as Boolean values (like most logic textbooks), we interpret into Coq's `Prop` sort. This is essentially a kind of [Algebraic semantics](https://en.wikipedia.org/wiki/Algebraic_semantics_(mathematical_logic)). For this to work, we axiomatize the law of excluded middle into Coq for propositional valuations---but since anything can be a valuation, this is equivalent to just assuming LEM in Coq. We could be more nuanced and define valuations to have a Boolean algebra as their target (meaning they include a proof of LEM for their range).
