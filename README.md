Polynomial Functors Constrained by Regular Expressions
======================================================

*Dan Piponi and Brent A. Yorgey*

This work was published in the Conference on the Mathematics of
Program Construction (MPC) 2015.

Abstract
--------

We show that every regular language, via some DFA which accepts it,
gives rise to a homomorphism from the semiring of polynomial functors
to the semiring of $n \times n$ matrices over polynomial functors.
Given some polynomial functor and a regular language, this
homomorphism can be used to automatically derive a functor whose
values have the same shape as those of the original functor, but whose
sequences of leaf types correspond to strings in the language.

The primary interest of this result lies in the fact that certain
regular languages correspond to previously studied derivative-like
operations on polynomial functors, which have proven useful in program
construction.  For example, the regular language $a^*ha^*$ yields the
\emph{derivative} of a polynomial functor, and $b^*ha^*$ its
\emph{dissection}.  Using our framework, we are able to unify and lend
new perspective on this previous work.  For example, it turns out that
dissection of polynomial functors corresponds to taking \emph{divided
differences} of real or complex functions, and, guided by this
parallel, we show how to generalize binary dissection to $n$-ary
dissection.
