# DProp

https://dunnl.github.io/dprop/

**DProp** ("Dee prop"): A deep embedding of classical propositional logic into Coq.

:warning: This repo is still under development. The homework exercises may be slightly impacted by changes.

Errata for PL clubbers doing the homework (mistakes/clarifications fixed between from Monday's announcement and Friday's talk):
- Exercise 6 has to be proved on pen and paper, not Coq
- Some commits define negation elimination as ex falso which isn't complete
- My "double negation elimination" rule is actually reductio absurdum

----

This file is a quick tutorial to using Coq as a logical framework to
study propositional logic, which is synonymous to saying we are
providing a deep embedding (a shallow embedding would like more like
the section "Minimal Logic" in the [basic Coq
tutorial](https://coq.inria.fr/tutorial/1-basic-predicate-calculus)). This
file is the backbone of a PL club presentation, as well as "homework"
for the willing.

We start by defining the synax of propositional logic, taking as primitives conjunction, negation, and the top element. From there we define the semantics, but instead of looking at propositions as `bool` values, we interpret into Coq's `Prop` sort. This is essentially a kind of [algebraic semantics](https://en.wikipedia.org/wiki/Algebraic_semantics_(mathematical_logic)). To get soundness, we have to require that valuations come with a proof that their range satisfies the law of excluded middle, which is essentially requiring that the codomain forms a boolean algebra.

There are about 10 [SF-inspired](https://softwarefoundations.cis.upenn.edu/) exercises in the file. Some are easy, some are hard. We talk about soundness, and state completeness but admit it as an axiom. Near the end there are some notes on syntactical incompleteness. A proof by induction on deductions fails due to lack of normal forms (cut elimination), but the result can be shown easily using soundness. Finally, some commentary at the end is given for understanding Gödel's completeness and first incompleteness theorem using what we've learned about propositional logic.

**PRs/Emails/Corrections welcome** 
