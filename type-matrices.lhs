% -*- mode: LaTeX; compile-command: "runghc make" -*-
\documentclass[authoryear,preprint]{sigplanconf}

%vim: set makeprg=runghc make:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2tex setup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include lhs2TeX.sty

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Package imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{amsmath}
\usepackage{tikz}
\usepackage{prettyref}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Semantic markup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\pkg}[1]{\texttt{#1}}
\newcommand{\ext}[1]{\texttt{#1}}
\newcommand{\module}[1]{\texttt{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Prettyref
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{Section~\ref{#1}}
\newrefformat{var}{Variation~\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\newcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\newcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Notes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\brent}[1]{\authornote{blue}{BAY}{#1}}
\newcommand{\dan}[1]{\authornote{green}{DP}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Math typesetting
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\union}{\cup}

\newcommand{\m}[1]{\mathbf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
\label{sec:alt-tree}

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

Consider the regular language $a^\ast1a^\ast$. It matches sequences of $a$s with precisely one occurrence of $1$ somewhere in the word, where $1$ represents the unit type (usually written |()| in Haskell). Applied to a recursive types it corresponds to trees where all of the leaf nodes are of type |a| apart from one which has the fixed value |()|. In other words, it's the derivative of the orginal type \cite{DBLP:journals/fuin/AbbottAMG05}. The regular language $a^\ast ba^\ast$ is a zipper type with elements of type $b$ at the `focus'.
And the regular language $a^\ast1b^\ast$ corresponds to dissection types \cite{dissection}.

Zippers, derivatives and dissections are usually described using Leibniz rules and their generalizations. We'll show how these rules can be placed in a more general framework applying to any regular language.

\section{Regular expressions and DFAs}
\label{sec:dfas}
A {\it deterministic finite state automaton} (DFA) $D$ is a triple $(Q, \Sigma, \delta)$ consisting of a set of states $Q$ and a set of input symbols $\Sigma$ along with a transition function $\delta:Q\times\Sigma\rightarrow Q$. At any time the automaton can be considered to be in one of the states in $Q$, say $q$. Whenever it receives an input symbol $s$ it changes to state $\delta(q,s)$. A DFA is started in a particular state called its {\it start} state, say $q_0$. Some subset of states $F\subset S$ are considered to be {\it accept} states.

If we have a string of symbols from the set $\Sigma$, we can feed them one by one to a DFA and at the end of the string it will be left in some state. If the DFA starts in the start state $q_0$ and ends in an accept state then it is said to {\it accept} the string.

We can draw a DFA as a directed multigraph where each graph edge is labeled by a symbol from $\Sigma$. Each state is a vertex, and an edge is drawn from $q_1$ to $q_2$ and labeled with symbol $s$ whenever $\delta(q_1,s)=q_2$. We can think of the state of the DFA as ``walking'' through the graph each time it receives an input.

\dan{The symbol $0$ stuff below may be the wrong way to do this.}

The main property of DFAs we will be interested in are what strings it accepts. Now suppose that at some stage in reading in a string we know that it is impossible for the DFA to ever reach an accept state. Then we may as well switch off the DFA there and then. So let's allow $\delta$ to be a partial function. If $\delta(q,s)$ isn't defined, the DFA stops if it receives input $s$ when in state $q$ and the string isn't accepted. This allows us to simplfy the multigraph we draw: we can simply leave out edges leaving state $q$ with symbol $s$ when $\delta(q,s)$ isn't defined.

Kleene's Theorem says that the set of strings accepted by a DFA is a regular language, ie. it corresponds to strings that match a regular expression.

\dan{
I'm implicitly defining the notion of "taking a DFA from state $q_0$ to $q_1$". Is there a better word for this?
}
Given any pair of states $q_1$ and $q_2$ in $Q$ we can consider the set of strings that, when input to the DFA, would take it from state $q_1$ to state $q_2$. Call this $D(q_0,q_1)$.
The set of strings taking the DFA from $q_0$ to a state in $F$ is the set of strings accepted by the DFA. We consider the empty string to take the DFA from state $q$ to $q$ for any $q$.

Suppose a string $S$ takes the DFA from $q_1$ to $q_2$. Suppose also that we break up our string into two pieces $S=S_1S_2$. Then $S_1$ must take the DFA from $q_1$ to some intermediate state $r$ and $S_2$ must take it from state $r$ to $q_2$. In other words $D(q_1,q_2) = \bigcup_{r\in Q}\{ST || S \in D(q_1,r), T \in D(r,q_2)\}$.

\section{Types and DFAs}
\label{sec:types-and-dfas}

Consider again the regular expression $(ab)^\ast$, whose corresponding
DFA is shown in Figure~\ref{fig:ab-star-dfa}.  Again, our goal will be
to construct a type with the same shape as

%format Tij = T "_{ij}"
%format T11
%format T12
%format T21
%format T22

> data T a b =  Apple a | Banana b | Fork (T a) (T a)

%options ghci
%if False

>                 deriving Show

%endif

\noindent but whose sequences of leaf types always match $(ab)^\ast$---that is,
whose sequences of leaf types, considered as a string, take the DFA
from state $1$ to itself.

\begin{figure}
  \centering
  \todo{draw a DFA}
%    ---A->--
%   /        \
% (1)        (2)
%   \        /
%    --<-B---

  \caption{A DFA for $(ab)^\ast$}
  \label{fig:ab-star-dfa}
\end{figure}

Generalizing a bit, let |Tij a b| denote the type of binary trees
whose leaf sequences take the DFA from state $i$ to state $j$.  Since
the DFA has two states, there are four such types:
\begin{itemize}
\item |T11 a b| --- this is the type of trees we are primarily
  interested in constructing, whose leaf sequences match $(ab)^\ast$.
\item |T12 a b| --- trees of this type have leaf sequences which
  take the DFA from state $1$ to state $2$; that is, they match the
  regular expression $a(ba)^\ast$ (or, equivalently, $(ab)^\ast{}a$).
\item |T21 a b| --- trees matching $b(ab)^\ast$.
\item |T22 a b| --- trees matching $(ba)^\ast$.
\end{itemize}

What does a tree of type |T11| look like?  It cannot be a leaf,
because a single leaf takes the DFA from state 1 to 2 or vice versa.
It must be a pair of trees, which together take the DFA from state 1
to state 1.  There are two ways for that to happen: both trees could
themselves begin and end in state 1; or the first tree could take the
DFA from state 1 to state 2, and the second from state 2 to state 1.
In fact, we have already carried out this analysis in
\pref{sec:alt-tree}; the only difference is that we now have a DFA as
a less ad-hoc framework in which to do the analysis.

\section{Matrices of types}
\label{sec:matrices-of-types}

In what follows, we abstract away from the particular details of
Haskell data types and work in terms of \term{polynomial
  functors}. \todo{explain this better? Shouldn't have to know any CT
  to understand it\dots do we actually make use of functoriality, or
  should we just say ``polynomial type constructors''?}
\begin{itemize}
\item $1$ denotes the constantly unit functor $1\ A = 1$ (whether $1$
denotes the constantly unit functor or the unit value should be clear
from the context).
\item $X$ denotes the identity functor $X\ A = A$.
\item Given two functors $F$ and $G$, we can form their sum, $(F + G)\
  A = F\ A + G\ A$.
\item We can also form products of functors, $(F \times G)\ A = F\ A
  \times G\ A$.  We will often abbreviate $F \times G$ as $FG$.
\end{itemize}

The above also generalizes naturally to multi-argument functors:
\begin{itemize}
\item $1\ A_1\ \dots\ A_n = 1$;
\item $(F + G)\ A_1\ \dots\ A_n = F\ A_1\ \dots\ A_n + G\ A_1\ \dots\
  A_n$;
\end{itemize}
and similarly for products.  The identity functor $X$ generalizes to
the family of projections ${}_nX_i$, where \[ {}_nX_i\ A_1\ \dots\ A_n = A_i. \]  For
example, the Haskell type
\begin{spec}
data S a b = Apple a | Banana b | Fork (S a b) (S a b)
\end{spec}
corresponds to the two-argument functor $S = {}_2X_1 + {}_2X_2 + S
\times S$.  Usually we omit the pre-subscript on $X$ and just write
$X_1$, $X_2$ and so on when the arity $n$ is clear from the context.

\todo{formally define ``sequence of leaf types''?}

% \newcommand{\leafseq}[1]{\llbracket #1 \rrbracket}

% $\leafseq{1} = \emptyset$
% $\leafseq{X_i} = \{ i \}$
% $\leafseq{F + G} = \leafseq{F} \union \leafseq{G}$
% $\leafseq{F \times G} = \leafseq{F} \cdot \leafseq{G}$

Suppose we have a one-argument functor $F$ and some DFA $D =
(Q,\Sigma,\delta)$ with $n$ states (that is, $||Q|| = n$).  Let
$F_{ij}$ denote the type with the same shape as $F$
  \brent{should we
  define this ``have the same shape as'' thing formally?  I guess the
  idea would be that $F$ and $G$ have the same shape iff $F\ 1\ \dots\
  1 \cong G\ 1\ \dots\ 1$ (where $F$ and $G$ could have different
  arities).}
  \dan{
  Should that be $F$ and $G$ have the same shape iff $F\ a\ \dots\
  a \cong G\ a\ \dots\ a$?
  Your definition gives the usual notion of shape: ie. the branching
  structure without regard to what the elements are. But I'm
  talking about the shape as a container with elements.
  I'm also not sure we need to make this formal.
  }
but whose sequence of leaf types takes $D$ from state $i$
to state $j$.  In particular $F_{ij}$ has arity $||\Sigma||$, since
there is a leaf type corresponding to each alphabet symbol of $D$.  We
can deduce $F_{ij}$ compositionally by considering each of the functor
building blocks above in turn.

\begin{itemize}
\item The constant functor $1$ creates structures containing no
  elements, \emph{i.e.} which do not cause the DFA to transition at
  all.  So the only way a $1$ structure can take the DFA from state
  $i$ to state $j$ is if $i = j$:

\[ 1_{ij} =
\begin{cases}
  1 & i = j \\
  0 & i \neq j
\end{cases}
\]

\item The identity functor $X$ creates structures containing a single
  leaf element.  So an $X$ structure containing a single value of type
  $A$ takes the DFA from state $i$ to state $j$ precisely when the DFA
  contains a transition from $i$ to $j$ labeled with $A$.   For
  example, \todo{give example?}
  \[ X_{ij} = \sum_{\substack{A \in \Sigma \\ \delta(i,A) = j}} X_A \]
  \todo{need to figure out the right way to present the above}

\item A value of type $F + G$ is either a value of type $F$ or a value of
type $G$; so

\[ (F + G)_{ij} = F_{ij} + G_{ij}. \]

\item Products are more interesting.  An $FG$-structure consists of an
  $F$-structure paired with a $G$-structure, which drive the DFA in
  sequence.
  \dan{Should the matrix be transposed?} 
  Hence, in order to take the DFA from state $i$ to state
  $j$ overall, the $F$-structure must take the DFA from state $i$ to
  some state $k$, and then the $G$-structure must take it from $k$ to
  $j$.  This works for any state $k$, and $(FG)_{ij}$ is the sum over
  all such possibilities.  Thus,

\[ (FG)_{ij} = \sum_{k \in Q} F_{ik} G_{kj}. \]
\end{itemize}

The above rules for $1$, sums, and products might look familiar.  In
fact, they are just the definitions of the identity matrix, matrix
addition, and matrix product.  That is, we can arrange all the
$F_{ij}$ for a given functor $F$ in a matrix $\m{F}$ whose $(i,j)$th
entry is $F_{ij}$.  Then $\m{1}$ is the identity matrix (with ones
along the main diagonal and zeros everywhere else); the matrix for the
sum of $F$ and $G$ the sum of their matrices; and the matrix for their
product is the product of their matrices.

And what about $X$?  Recall that $X_{ij}$ is the sum of the labels on
all transitions from state $i$ to state $j$ in the DFA.  Hence, the
matrix $\m{X}_D$ is the \emph{transition matrix} for $D$.

In other words, given a DFA $D$, we have a \emph{semiring
  homomorphism} from arity-$1$ functors to $||Q|| \times ||Q||$
matrices of arity-$||\Sigma||$ functors---that is, a mapping from
functors to matrices which preserves sum and product. \todo{explain
  better what is meant by semiring homomorphism}

As an example, consider again the recursive tree type given by $T = X
+ T \times T$, along with the two-state DFA for $(ab)^*$ shown in
\pref{fig:ab-star-dfa}.  The matrix for $T$ can be written
\[ \m{T} =
\begin{bmatrix}
  |T11| & |T12| \\
  |T21| & |T22|
\end{bmatrix}
\]
and we have already determined previously what is represented by each
$T_{ij}$.  The punchline is that we can take the recursive equation
for $T$ and simply apply the homomorphism to both sides, resulting in
the matrix equation
\[ \m{T} = \m{X}_D + \m{T}^2, \] where $\m{X}_D$ is the transition
matrix for $D$, namely
\[ \m{X}_D =
  \begin{bmatrix}
    0 & a \\
    b & 0
  \end{bmatrix}.
\]
Expanding out this matrix equation and performing the indicated matrix
operations yields

\begin{multline*}
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|
  \end{bmatrix}
  =
  \begin{bmatrix}
    0 & a \\
    b & 0
  \end{bmatrix}
  +
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|
  \end{bmatrix}
  ^2
  \\
  =
  \begin{bmatrix}
    |T11|^2 + |T12| |T21| & |a| + |T11| |T12| + |T12| |T22| \\
    |b| + |T21| |T12| + |T22| |T21| & |T21| |T12| + |T22|^2
  \end{bmatrix}.
\end{multline*}
Equating the left- and right-hand sides elementwise yields precisely
the definitions for $T_{ij}$ we derived in \pref{sec:alt-tree}.

\todo{include a bunch more examples here.  Both other DFAs and other
  types \dots}

%format Lij = L "_{ij}"
%format L11
%format L12
%format L21
%format L22

To make things concrete can revisit some familiar types from this viewpoint. For example consider the resular expression $(aa)^\ast$. This corresponds to the DFA:
\todo{draw it}
Now apply our homomorphism to the defining equation for lists and we get
\[ \m{L} = \m{1} + \m{X}_D \m{L}, \] where $\m{X}_D$.
The transition matrix in this case is
\[ \m{X}_D =
\begin{bmatrix}
  |0| & |a| \\
  |a| & |0|
\end{bmatrix}
\]
\begin{multline*}
  \begin{bmatrix}
    |L11| & |L12| \\
    |L21| & |L22|
  \end{bmatrix}
  =
  \begin{bmatrix}
    1 & 0 \\
    0 & 1
  \end{bmatrix}
  +
  \begin{bmatrix}
    0 & a \\
    a & 0
  \end{bmatrix}
  \begin{bmatrix}
    |L11| & |L12| \\
    |L21| & |L22|
  \end{bmatrix}
  \\
  =
  \begin{bmatrix}
    1+a |L21| & a |L22| \\
    a | L12| & 1+a |L21|
  \end{bmatrix}.
\end{multline*}

|L11| and |L22| are isomorphic types as are the pair of types |L12| and |L21|. We can recognise |L11| as a list with odd length and |L12| as a list with even length. More familarly:

> data EvenList a = EvenNil | EvenList a (OddList a)
> data OddList a = OddList a (EvenList a)

\section{Derivatives, again}
\label{sec:derivatives-again}
\begin{itemize}
\item Circle back round and discuss derivatives, dissection, and
  infinitesimals again from the new vantage point.  (e.g. discuss
  where the usual Leibniz equation comes from.)
\end{itemize}
DFA for $a^\ast1a^\ast$.
\dan{Diagram}
\[ \m{X} =
\begin{bmatrix}
  |a| & |1| \\
  |0| & |a|
\end{bmatrix}
\]
Suppose a functor \dan{?} is a product of two functors
\[
F = G \times H
\]
Then
\[
F_{00} = F_{00}\times G_{00}+F_{01}\times G_{10}
\]
$G_{10}$ is the type of trees whose leaves take our DFA from $1$ to $0$.
But there are no such strings. So $G_{10}$ is the uninhabited type $0$.
So $F_{00} = F_{00}\times G_{00}$.
In fact, $F_{00}$ is simply structures whose leaves take the DFA from state 0 to state 0 and so whose
leaves match the regular expression $a^\ast$.
So we have simply that $F_{00} = F$.
Similarly $F_{11} = F$.
We also have
\[
F_{01} = F_{00}\times G_{01}+F_{01}\times G_{11}
\]
So
\[
F_{01} = F\times G_{01}+F_{01}\times G
\]
This looks suspiciously like the Leibniz law.
We also know that
\[
1_{01} = 0
\]
and
\[
X_{01} = 1
\]
\dan{Make sure $1$ isn't ambiguous}
These are precisely the rules for differentiating polynomials.
So $F_{01}$ is the derivative of $F$.
We described above how $a^\ast1a^\ast$ gives rise to zipper types.
We have now shown how these can be computed as derivatives.
  \dan{
  Need to do sums and fixed points.
  }

There is another way to look at this. Write
\[
\m{T} = a\m{1}+\m{d}
\]
where
\[ \m{d} =
\begin{bmatrix}
  |0| & |1| \\
  |0| & |0|
\end{bmatrix}
\]
Note that $\m{d}^2=\m{0}$.

\section{Divided differences}
\label{sec:divided-differences}

\begin{itemize}
\item Use the new power to also generalize dissections to divided
  differences.
\end{itemize}

DFA for $a^\ast1b^\ast$.
\dan{Diagram}
\[ \m{T} =
\begin{bmatrix}
  |a| & |1| \\
  |0| & |b|
\end{bmatrix}
\]
Suppose a functor \dan{?} is a product of two functors
\[
F = G \times H
\]
\dan{
This is just placeholder really. I need to work out precisely what is a function
of what.
}
Then
\[
F_{00} = F_{00}\times G_{00}+F_{01}\times G_{10}
\]
$G_{10}$ is the type of trees whose leaves take our DFA from $1$ to $0$.
But there are no such strings. So $G_{10}$ is the uninhabited type $0$.
So $F_{00} = F_{00}\times G_{00}$.
As before, $F_{00}$ is structures whose leaves take the DFA from state 0 to state 0 and so whose
leaves match the regular expression $a^\ast$.
So we have simply that $F_{00}(a,b) = F(a)$.
However, we now have that $F_{11}(a,b) = F(b)$.
We also have
\[
F_{01} = F_{00}\times G_{01}+F_{01}\times G_{11}
\]
So
\[
F_{01}(a,b) = F(a)\times G_{01}(a,b)+F_{01}(a,b)\times G(b)
\]
This is the modified Leibniz rule described in \cite{dissection}.
\dan{Do other operations}
We have already argued above \dan{xref} that the regular expression $a^\ast1b^\ast$
gives rise to dissections. We have now also shown how the algebraic rules for
dissections are actually statements about the transition matrices for the
corresponding DFA.

There is a more familiar interpretation of the dissection operation.
Given a function of a single real variable $f$,
the divided difference is the function of two variables mapping $x_0$, $x_1$ to $(f(x_0)-f(x_1)/(x_0-x_1))$ which is sometimes also written as $[x_0, x_1]f$.
\dan{Terrible notation.}
\begin{multline*}
[x_0,x_1]fg = (f(x_0)g(x_0)-f(x_1)g(x_1))/(x_0-x_1)\\
= (f(x_0)g(x_0)-f(x_0)g(x_1)+f(x_0)g(x_1)-f(x_1)g(x_1))/(x_0-x_1)\\
= f(x_0)[x_0,x_1]g+[x_0,x_1]fg(x_1)
\end{multline*}
This is McBride's modified Leibniz rule above.
For polynomial types it appears that dissection is the divided difference.
There is an important caveat: divided differences are defined using
subtraction which isn't meaningful for types.
But the Leibniz law above shows that for polynomials divided differences
could have been defined without making reference to subtraction and that
this definition carries over to types.
Notice how in the limit as $x_0\rightarrow x_1$ we recover the derivative.

\dan{I'd like to point out
\begin{itemize}
\item we can generalise to higher divided differences
\item the transition matrix (and its generalisation) corresponds to Opitz formula, but this
might be too much information
\end{itemize}
}

\acks

Acknowledgments.

% We recommend abbrvnat bibliography style.

\bibliography{type-matrices}{}
\bibliographystyle{abbrvnat}

\end{document}
