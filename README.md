## Proof search for classical propositional linear logic

### Background
I was doing background reading on functional analysis for my numerical work and came across the concept of $C^{*}$-algebras, which called to mind the semantics of linear logic (Girard 1987). That made me want to take a break from matrix algebra and work out some proof-search code

### Algorithm
Andreoli (1992) introduced *focusing* for the express purpose of trimming down the search space for classical linear sequent calculus, and I've adapted the technique from that paper here. 

I chose to work in Haskell because ADT's make it easy to instantiate formal languages and work with recursive types. Unfortunately for me, the focusing algorithm relies on an essentially state-ful context to guide the verification steps, so I had to brush up on threading state through with the `State` monad. (I'm still not certain my monadology makes sense in places.)

### Next steps
The next order of business after further validation is extending the checker to the first-order case, which ought to be straight-forward.

I'd eventually like to extend this to a linear type-checker, incorporating the term language developed by Wadler (2012), and write a front-end for a language incorporating Wadler's deadlock/race-free-by-construction type system.

### References

Andreoli, Jean-Marc (1992). "Logic Programming with Focusing Proofs in Linear Logic". *The Journal of Logic and Computation* 

Girard, Jean-Yves (1987). "Linear Logic". *Theoretical Computer Science* 

Wadler, Philip (2012). "Propositions as Sessions". *ICFP '12 Proceedings of the 17th ACM SIGPLAN international conference on Functional programming*
