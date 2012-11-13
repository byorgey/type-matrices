% -*- mode: LaTeX; compile-command: "runghc make" -*-
\documentclass[authoryear,preprint]{sigplanconf}

\usepackage{amsmath}
\usepackage{tikz}

%vim: set makeprg=runghc make:

%include lhs2TeX.fmt
%include lhs2TeX.sty

\begin{document}

%\conferenceinfo{WXYZ '05}{date, City.} 
%\copyrightyear{2005} 
%\copyrightdata{[to be supplied]} 

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Matrices! Of Types!}
%\subtitle{Subtitle Text, if any}

\authorinfo{Dan Piponi}
           {Google}
           {dpiponi@@gmail.com}
\authorinfo{Brent A. Yorgey}
           {University of Pennsylvania}
           {byorgey@@cis.upenn.edu}

\maketitle

\begin{abstract}
Matrices of types are sweet
\end{abstract}

%\category{CR-number}{subcategory}{third-level}

%\terms
%term1, term2

%\keywords
%matrices, types

\section{Introduction}
\label{sec:introduction}

(I'm listing some elementary examples. We don't have to use all of them.)

Here is how we might define a homogeneous list type in Haskell:

> data List a = Nil | Cons a (List a)

It's homogeneous because each element has the same type as every other element. But suppose we want some other constraint on our list, for example that the types of the elements alternate between |a| and |b|, starting with |a| and ending with |b|. We can define a pair of mutually recursive types as follows:

> data AList a b = ANil | ACons a (BList a b)
> data BList a b = BCons b (AList a b)

The required list is |AList a b|. Our goal will be to generalise this in two different ways
\begin{itemize}
\item We can think of the sequence of types in our list as conforming to a regular expression $(ab)^\ast$. We can generalize this to other regular expressions.
\item We can consider more general recursive types than lists and make their leaf nodes, when read from left to right, conform to a regular expression
\end{itemize}

\section{An alternating tree}
Let's consider the example of constructing a binary tree whose leaves conform to the regular expression $(ab)^\ast$.

%format Tree11
%format Tree12
%format Tree21
%format Tree22

%format Fork11
%format Fork11'
%format Fork12
%format Fork12'
%format Fork21
%format Fork21'
%format Fork22
%format Fork22'

%format Leaf11
%format Leaf12
%format Leaf21
%format Leaf22

(Maybe nobody wants to see the gory details of this.)

Here's a basic binary tree:

> data Tree a =  Leaf a | Fork (Tree a) (Tree a)
>                 deriving Show

Now suppose that |Tree11| is a tree whose leaf nodes are in $(ab)^\ast$.
(We'll explain the suffix $11$ later.)
It can't itself be a leaf node because then it would have only one element.
It must be a fork consisting of two subtrees.
There are two ways this could happen.
The left fork could start with |a| and end with |b| in which case the right fork must also start with |a| and end with |b|.
Or the left fork could start with |a| and end with |a| in which case the right fork must start with |b| and end with |b|. So we are led to this type:

> data Tree11 a b  =  Fork11  (Tree11 a b)  (Tree11 a b)
>                  |  Fork11' (Tree12 a b)  (Tree21 a b)

%options ghci
%if False

>                     deriving Show

%endif

Similar reasoning about the subtree types leads to the remainder of the mutually recursive definition:

> data Tree12 a b  = Leaf12 a
>                  |  Fork12  (Tree11 a b)  (Tree12 a b)
>                  |  Fork12' (Tree12 a b)  (Tree22 a b)

%options ghci
%if False

>                     deriving Show

%endif

> data Tree21 a b  = Leaf21 b
>                  |  Fork21  (Tree21 a b)  (Tree11 a b)
>                  |  Fork21' (Tree22 a b)  (Tree21 a b)

%options ghci
%if False

>                     deriving Show

%endif

> data Tree22 a b  =  Fork22  (Tree21 a b)  (Tree21 a b)
>                  |  Fork22' (Tree22 a b)  (Tree21 a b)

%options ghci
%if False

>                     deriving Show

%endif

Any tree of type |Tree11 a b| is now constrained to have alternating leaf node types:

%format ex1=\VarID{ex_1}
%format ex2=\VarID{ex_2}

> ex1 = Fork11' (Leaf12 1) (Leaf21 'a')
> ex2 = Fork11' (Fork12 ex1 (Leaf12 2)) (Leaf21 'b')

\begin{tikzpicture}[level/.style={sibling distance=30mm/#1}]
\node {|Fork11'|}
  child {
      node {|Fork12|}
          child {node {|Fork11'|}
                    child {node {|Leaf12 1|}}
                    child {node {|Leaf21 "a"|}}
          }
          child {node {|Leaf12 1|}}
  }
  child {node {|Leaf21 "b"|}};
\end{tikzpicture}

While this works, the procedure was somewhat {\it ad hoc}. We reasoned about the properties of the pieces we get when we split a string from $(ab)^\ast$ into two and used this to find corresponding types for the subtrees. Why did we end up with four tree types? And how does this relate to the standard theory of regular languages?

\section{Zippers and dissections}
\label{sec:zippers-and-dissections}

Given a recursive type $t$ we can consider the problem of `lifting' it to a new type that conforms to a given regular expression. It turns out that for certain regular expressions this problem has already been solved in the literature without the problem having been phrased in this form.

Consider the regular language $a^\ast1a^\ast$. It matches sequences of $a$s with precisely one occurrence of $1$ somewhere in the word, where $1$ represents the unit type (usually written |()| in Haskell). Applied to a recursive types it corresponds to trees where all of the leaf nodes are of type |a| apart from one which has the fixed value |()|. In other words, it's the derivative of the orginal type. The regular language $a^\ast ba^\ast$ is a zipper type with elements of type $b$ at the `focus'. And the regular language $a^\ast1b^\ast$ corresponds to dissection types.

Zippers, derivatives and dissections are usually described using Leibniz rules and their generalizations. We'll show how these rules can be placed in a more general framework applying to any regular language.

\section{Regular expressions and DFAs}
\label{sec:dfas}
A {\it deterministic finite state automaton} (DFA) consists of a set of states $Q$ and a set of input symbols $\Sigma$ along with a transition function $\delta:Q\times\Sigma\rightarrow Q$. At any time the automaton can be considered to be in one of the states in $Q$, say $q$. Whenever it receives an input symbol $s$ it changes to state $\delta(q,s)$. A DFA is started in a particular state called its {\it start} state, say $q_0$. Some subset of states $F\subset S$ are considered to be {\it accept} states.

If we have a string of symbols from the set $\Sigma$, we can feed them one by one to a DFA and at the end of the string it will be left in some state. If the DFA starts in the start state $q_0$ and ends in an accept state then it is said to {\it accept} the string.

We can draw a DFA as a directed multigraph where each graph edge is labeled by a symbol from $\Sigma$. Each state is a vertex, and an edge is drawn from $q_1$ to $q_2$ and labeled with symbol $s$ whenever $\delta(q_1,s)=q_2$. We can think of the state of the DFA as ``walking'' through the graph each time it receives an input.

[The symbol $0$ stuff below may be the wrong way to do this.]

The main property of DFAs we will be interested in are what strings it accepts. Now suppose that at some stage in reading in a string we know that it is impossible for the DFA to ever reach an accept state. Then we may as well switch off the DFA there and then. So let's allow $\delta$ to also take the value $0$ so its range is $Q\cup\{0\}$. If $\delta(q,s)=0$, the DFA stops if it receives input $s$ when in state $q$ and the string isn't accepted. This allows us to simplfy the multigraph we draw: we can simply leave out edges leaving state $q$ with symbol $s$ when $\delta(q,s)=0$.

Kleene's Theorem says that the set of strings accepted by a DFA is a regular language, ie. it corresponds to strings that match a regular expression.

Given any pair of states $q_1$ and $q_2$ in $Q$ we can consider the set of strings that, when input to the DFA, would take it from state $q_1$ to state $q_2$. The set of strings taking the DFA from $q_0$ to a state in $F$ is the set of strings accepted by the DFA. We consider the empty string to take the DFA from state $q$ to $q$ for any $q$.

Suppose a string $S$ takes the DFA from $q_1$ to $q_2$. Suppose we break up our string into two pieces $S=S_1S_2$. Then $S_1$ must take the DFA from $q_1$ to some intermediate state $q_3$ and $S_2$ must take it from state $q_3$ to $q_2$. In other words the set of strings taking the DFA from $q_1$ to $q_2$ is the set o

\section{Matrices of types}
\label{sec:matrices-of-types}

Consider again the regular expression $(ab)^\ast$, whose corresponding
DFA is shown in Figure~\ref{fig:ab-star-dfa}.  Again, our goal will be
to construct a type with the same shape as

> data Tree a =  Leaf a | Fork (Tree a) (Tree a)
>                 deriving Show

but whose sequences of leaf types always match $(ab)^\ast$---that is,
whose sequences of leaf types, considered as a string, take the DFA
from state $1$ to itself.

\begin{figure}
  \centering
  TODO
%    ---A->--
%   /        \
% (1)        (2)
%   \        /
%    --<-B---

  \caption{A DFA for $(ab)^\ast$}
  \label{fig:ab-star-dfa}
\end{figure}

%format Treeij = Tree "_{ij}"

Generalizing a bit, let |Treeij a b| denote the type of binary trees
whose leaf sequences take the DFA from state $i$ to state $j$.  Since
the DFA has two states, there are four such types:
\begin{itemize}
\item |Tree11 a b| --- this is the type of trees we are primarily
  interested in constructing, whose leaf sequences match $(ab)^\ast$.
\item |Tree12 a b| --- trees of this type have leaf sequences which
  take the DFA from state $1$ to state $2$; that is, they match the
  regular expression $a(ba)^\ast$ (or, equivalently, $(ab)^\ast{}a$).
\item |Tree21 a b| --- trees matching $b(ab)^\ast$.
\item |Tree22 a b| --- trees matching $(ba)^\ast$.
\end{itemize}

TODO: finish this example.  Derive |Treeij| intuitively---sums,
products, etc.  Then show how we can organize everything into matrices.

TODO: explain more generally.  type algebra, homomorphism to semiring
of matrices, etc.

\section{Derivatives, again}
\label{sec:derivatives-again}

\begin{itemize}
\item Circle back round and discuss derivatives, dissection, and
  infinitesimals again from the new vantage point.  (e.g. discuss
  where the usual Leibniz equation comes from.)
\end{itemize}

\section{Divided differences}
\label{sec:divided-differences}

\begin{itemize}
\item Use the new power to also generalize dissections to divided
  differences.
\end{itemize}

\acks

Acknowledgments.

% We recommend abbrvnat bibliography style.

% \bibliographystyle{abbrvnat}

\end{document}
