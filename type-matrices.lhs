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

\usepackage[outputdir=diagrams/,backend=ps,extension=eps]{diagrams-latex}

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

\dan{I'm listing some elementary examples. We don't have to use all of
  them.} \brent{I like these examples. I certainly don't think we
  should have fewer.}

Consider the standard singly-linked list type, which can be defined in
Haskell \cite{haskell} as:

> data List a  =  Nil
>              |  Cons a (List a)

This type is \term{homogeneous} because each element in the list has
the same type as every other element.

Suppose, however, that we wanted some other sort of list type with a
different constraint on the types of its elements.  For example, we
might want a list whose elements alternate between two types |a| and
|b|, beginning with |a| and ending with |b|.

\begin{figure}[h]
  \centering
\begin{diagram}[width=150]
import TypeMatricesDiagrams
import Data.List
import Data.Ord

lst = withNameAll "elt" (\ds ->
        let locs  = map location ds
            cmpX  = comparing (fst . unp2)
            start = minimumBy cmpX locs
            end   = maximumBy cmpX locs
        in
            beneath (start ~~ end)
      )
    . hcat' with {sep=1}
    . map (named "elt" . drawType)
    $ [A,B,A,B,A,B]

dia = lst # lw 0.1 # centerXY # pad 1.1
\end{diagram}
%$
  \caption{A list with alternating types}
  \label{fig:alt-list}
\end{figure}
One way to encode such an
alternating list is with a pair of mutually recursive types, as follows:

> data AList a b  =  ANil
>                 |  ACons a (BList a b)
>
> data BList a b  =  BCons b (AList a b)

(Another way would be to use a single GADT with a phantom type
parameter.) \brent{Include this parenthetical?} The required type is
|AList a b|: a value of type |AList a b| must be either empty (|ANil|)
or contain a value of type |a|, followed by a value of type |b|,
followed recursively by another |AList a b|.

In fact, we can think of |AList a b| as containing values whose
\term{shape} corresponds to the original |List| type, but whose
sequence of element types corresponds to the \term{regular expression}
$(ab)^\ast$, that is, any number of repetitions of the sequence $ab$.

We can easily generalize this idea to regular expressions other than
$(ab)^\ast$ (though constructing the corresponding types may be
complicated). We can also generalize to algebraic data types other
than |List|, by considering the sequence of element types encountered
by an \term{inorder traversal} of each data structure.

%format TreeAB = Tree "_{AB}"
%format TreeAA = Tree "_{AA}"
%format TreeBB = Tree "_{BB}"
%format TreeBA = Tree "_{BA}"

%format ForkAB = Fork "_{AB}"
%format ForkAB' = Fork "_{AB}^\prime"
%format ForkAA = Fork "_{AA}"
%format ForkAA' = Fork "_{AA}^\prime"
%format ForkBB = Fork "_{BB}"
%format ForkBB' = Fork "_{BB}^\prime"
%format ForkBA = Fork "_{BA}"
%format ForkBA' = Fork "_{BA}^\prime"

%format LeafAB = Leaf "_{AB}"
%format LeafAA = Leaf "_{AA}"
%format LeafBB = Leaf "_{BB}"
%format LeafBA = Leaf "_{BA}"

\dan{Maybe nobody wants to see the gory details of this.}
\brent{Actually, I think an example which is both understandable and
  has lots of gory details (like this one) will serve well: it both
  gives people some good intuition, and at the same time sets them up
  to really appreciate the elegant, general solution in contrast.}

For example, consider the following type |Tree| of nonempty binary
trees with data stored in the leaves:
> data Tree a  =  Leaf a
>              |  Fork (Tree a) (Tree a)
%if False
>                 deriving Show
%endif
Consider again the problem of writing down a type whose values have
the same shape as values of type |Tree a|, but where the data elements
alternate between two types |a| and |b| (when listed according to an
inorder traversal), beginning with a leftmost element of type |a| and
ending with a rightmost element of type |b|.  An example can be seen
in \pref{fig:alt-tree}.

\begin{figure}
  \centering
\begin{diagram}[width=150]
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import TypeMatricesDiagrams

t = Nothing ##
    [ Nothing ##
      [ Nothing ##
          leaves [ Just A, Just B ]
      , leaf $ Just A
      ]
    , Nothing ##
      [ Nothing ##
        [ leaf $ Just B
        , Nothing ## leaves [Just A, Just B]
        ]
      , Nothing ## leaves [Just A, Just B]
      ]
    ]
  where (##)   = Node
        leaf x = Node x []
        leaves = map leaf

dia = renderT t # lw 0.1 # centerXY # pad 1.1
\end{diagram}
%$
  \caption{A tree with alternating leaf types}
  \label{fig:alt-tree}
\end{figure}

Suppose |TreeAB a b| is such a type. Values of type |TreeAB a b|
cannot consist solely of a leaf node: there must be at least two
elements, one of type |a| and one of type |b|.  Hence a value of type
|TreeAB a b| must be a fork consisting of two subtrees.  There are two
ways this could happen.  The left subtree could start with |a| and end
with |b|, in which case the right subtree must also start with |a| and
end with |b|.  Or the left subtree could start with |a| and end with
|a|, in which case the right subtree must start with |b| and end with
|b|. So we are led to define
> data TreeAB a b  =  ForkAB  (TreeAB a b)  (TreeAB a b)
>                  |  ForkAB' (TreeAA a b)  (TreeBB a b)
%if False
>                     deriving Show
%endif
where |TreeAA a b| represents alternating trees with left and
rightmost elements both of type |a|, and similarly for |TreeBB|.

Similar reasoning about the subtree types leads to the remainder of
the mutually recursive definition:
> data TreeAA a b  =  LeafAA a
>                  |  ForkAA  (TreeAB a b)  (TreeAA a b)
>                  |  ForkAA' (TreeAA a b)  (TreeBA a b)
%if False
>                     deriving Show
%endif
> data TreeBB a b  =  LeafBB b
>                  |  ForkBB  (TreeBB a b)  (TreeAB a b)
>                  |  ForkBB' (TreeBA a b)  (TreeBB a b)
%if False
>                     deriving Show
%endif
> data TreeBA a b  =  ForkBA  (TreeBB a b)  (TreeAA a b)
>                  |  ForkBA' (TreeBA a b)  (TreeBA a b)
%if False
>                     deriving Show
%endif
Any tree of type |TreeAB a b| is now constrained to have alternating
leaf node types.  For example, here are two values of type |TreeAB Int
Char|:

%format ex1
%format ex2

> ex1, ex2 :: TreeAB Int Char
> ex1 = ForkAB' (LeafAA 1) (LeafBB 'a')
> ex2 = ForkAB' (ForkAA ex1 (LeafAA 2)) (LeafBB 'b')

|ex2| can also be seen in pictorial form in \pref{fig:alt-tree-hs}.

\begin{figure}
  \centering
\begin{tikzpicture}[level/.style={sibling distance=50mm/#1}]
\node {|ForkAB'|}
  child {
      node {|ForkAA|}
          child {node {|ForkAB'|}
                    child {node {|LeafAA 1|}}
                    child {node {|LeafBB "a"|}}
          }
          child {node {|LeafAA 1|}}
  }
  child {node {|LeafBB "b"|}};
\end{tikzpicture}
  \caption{A tree with alternating leaf types}
  \label{fig:alt-tree-hs}
\end{figure}

While this works, the procedure was somewhat {\it ad hoc}. We reasoned
about the properties of the pieces that result when a string matching
$(ab)^\ast$ is split into two substrings, and used this to find
corresponding types for the subtrees. One might wonder why we ended up
with four mutually recursive types---is there is any simpler solution?
And how well will this sort of reasoning extend to more complicated
structures or regular expressions?  Our goal will be to derive a more
principled way to do this analysis for any regular language and any
data type.\brent{actually only for \emph{polynomial} types, but we
  haven't defined that yet... is there something we can say to be more
  accurate without using technical terms which haven't yet been
  introduced?}

% There's a detail whose importance I'm not 100\% sure of. There are
% multiple solutions to the problem of 'lifting' a type to be
% constrained by a regexp. Compare

% data S a b = Apple a || Banana b || Fork (S a b) (S a b)

% vs.

% data S a b = Apple a || Apple' a || Banana b || Fork (S a b) (S a b)

% Both will end up with the same regular language. (Basically because we
% have idempotence in languages, x+x=x.) Is here anything you think that
% needs to be said about this? Some solutions are nice in that every
% string in the language is represented precisely once. I think the
% matrix construction gives us these because it's coming from a DFA so
% there's only one path you can take through it. Does that sound right?
% So we're actually doing slightly better than just constraining the
% leaves with regular expressions. We're getting the best such type, in
% some sense. Or at least I hope we are.

It's worth mentioning that for certain regular languages, this problem
has already been solved in the literature, though without being
phrased in terms of regular languages.  For example, consider the
regular language $a^\ast1a^\ast$. It matches sequences of $a$s with
precisely one occurrence of $1$ somewhere in the middle, where $1$
represents the unit type (written |()| in Haskell). Data structures
whose inorder sequence of element types matches $a^\ast1a^\ast$ have
all elements of type |a|, except for one which has the fixed value
|()|. In other words, imposing this regular expression corresponds to
finding the \term{derivative} of the orginal type
\cite{DBLP:journals/fuin/AbbottAMG05} (\pref{fig:derivative}).
Likewise, the regular language $a^\ast ba^\ast$ corresponds to a
zipper type \cite{Huet_zipper} with elements of type $b$ at the
`focus', and the regular language $a^\ast1b^\ast$ corresponds to
\term{dissection types} \cite{dissection}.

\begin{figure}
  \centering
  \begin{diagram}[width=150]
import TypeMatricesDiagrams
import Data.Tree

t = Nothing ##
    [ Nothing ##
      [ Nothing ##
          leaves [ Just A, Just A ]
      , leaf $ Just A
      ]
    , Nothing ##
      [ Nothing ##
        [ leaf $ Just A
        , Nothing ## leaves [Just H, Just A]
        ]
      , Nothing ## leaves [Just A, Just A]
      ]
    ]
  where (##)   = Node
        leaf x = Node x []
        leaves = map leaf

dia = renderT t # lw 0.1 # centerXY # pad 1.1
  \end{diagram}
  \caption{A tree corresponding to the regular language $a^\ast1a^\ast$}
  \label{fig:derivative}
\end{figure}

Zippers, derivatives and dissections are usually described using
Leibniz rules and their generalizations. We'll show how these rules
can be placed in a more general framework applying to any regular
language.

\todo{should insert somewhere around here a list of
  contributions/outline of the rest of the paper.}

\section{Regular expressions and DFAs}
\label{sec:dfas}

We begin with a quick review of the basic theory of regular
languages and deterministic finite automata.  Readers already
familiar with this theory may safely skip this section.

\subsection{Regular expressions}
\label{sec:regexps}

A \term{regular expression} over an alphabet $\Sigma$ is a term of the
following grammar:
\[ \begin{array}{rrl}
  R & ::= & \varnothing \\
  & \mid & \varepsilon \\
  & \mid & a \qquad (a \in \Sigma) \\
  & \mid & R \union R \\
  & \mid & RR \\
  & \mid & R^*
\end{array}
\]

\newcommand{\sem}[1]{\ensuremath{\left\llbracket #1 \right\rrbracket}}

When writing regular expressions, we also allow parentheses for
disambiguation, and also adopt the common convention that Kleene star
($R^*$) has higher precedence than concatenation ($RR$), which has
higher precedence than alternation ($R \union R$).

Semantically, we can interpret each regular expression $R$ as a set of
strings $\sem R \subseteq \Sigma^*$, where $\Sigma^*$ denotes the set
of all finite sequences built from elements of $\Sigma$.  In
particular,
\begin{itemize}
\item $\sem \varnothing = \varnothing$ denotes the empty set of strings.
\item $\sem \varepsilon = \{\varepsilon\}$ denotes the singleton set
  containing the empty string.
\item $\sem a = \{a\}$ denotes the singleton set containing the
  length-$1$ sequence $a$.
\item $\sem{R_1 \union R_2} = \sem{R_1} \union \sem{R_2}$.
\item $\sem{R_1 R_2} = \sem{R_1} \sem{R_2}$, where $L_1 L_2$ denotes
  concatenation of sets, \[ L_1 L_2 = \{ s_1 s_2 \mid s_1 \in L_1,
  s_2 \in L_2 \}. \]
\item $\sem{R^*} = \sem{R}^*$, where $L^*$ denotes the least solution
  of \[ L^* = \{\varepsilon\} \union LL^*. \]
\end{itemize}

\todo{add an example here?}

Finally, a \term{regular language} over the alphabet $\Sigma$ is a set
$L \subseteq \Sigma^*$ which is the interpretation $L = \sem R$ of
some regular expression $R$.

\subsection{DFAs}
\label{sec:dfas}

A {\it deterministic finite automaton} (DFA) is a quintuple $(Q,
\Sigma, \delta, q_0, F)$ consisting of
\begin{itemize}
\item a nonempty set of states $Q$,
\item a set of input symbols $\Sigma$,
\item a \term{transition function} $\delta : Q\times\Sigma \to Q$,
\item a distinguished \term{start state} $q_0 \in Q$, and
\item a set $F \subseteq Q$ of \term{accept states}.
\end{itemize}

We can ``run'' a DFA on an input string by feeding it symbols from the
string one by one.  When encountering the symbol $s$ in state $q$, the
DFA changes to state $\delta(q,s)$.  If a DFA beginning in its start
state $q_0$ ends in state $q'$ after being fed a string in this way,
we say the DFA \term{accepts} the string if $q' \in F$, and
\term{rejects} the string otherwise.  Thus, a DFA $D$ can be seen as
defining a subset $L_D \subseteq \Sigma^*$ of the set of all possible
strings, namely, those strings which it accepts.

We can draw a DFA as a directed multigraph where each graph edge is
labeled by a symbol from $\Sigma$. Each state is a vertex, and an edge
is drawn from $q_1$ to $q_2$ and labeled with symbol $s$ whenever
$\delta(q_1,s)=q_2$. We can think of the state of the DFA as
``walking'' through the graph each time it receives an input.

\todo{draw an example DFA}

\todo{edit this section}

The main property of DFAs we will be interested in are what strings it
accepts. Now suppose that at some stage in reading in a string we know
that it is impossible for the DFA to ever reach an accept state. Then
we may as well switch off the DFA there and then. So let's allow
$\delta$ to be a partial function. If $\delta(q,s)$ isn't defined, the
DFA stops if it receives input $s$ when in state $q$ and the string
isn't accepted. This allows us to simplfy the multigraph we draw: we
can simply leave out edges leaving state $q$ with symbol $s$ when
$\delta(q,s)$ isn't defined.

\dan{ I'm implicitly defining the notion of "taking a DFA from state
  $q_0$ to $q_1$". Is there a better word for this?  } Given any pair
of states $q_1$ and $q_2$ in $Q$ we can consider the set of strings
that, when input to the DFA, would take it from state $q_1$ to state
$q_2$. Call this $D(q_0,q_1)$.  The set of strings taking the DFA from
$q_0$ to a state in $F$ is the set of strings accepted by the DFA. We
consider the empty string to take the DFA from state $q$ to $q$ for
any $q$.

Suppose a string $S$ takes the DFA from $q_1$ to $q_2$. Suppose also
that we break up our string into two pieces $S=S_1S_2$. Then $S_1$
must take the DFA from $q_1$ to some intermediate state $r$ and $S_2$
must take it from state $r$ to $q_2$. In other words $D(q_1,q_2) =
\bigcup_{r\in Q}\{ST || S \in D(q_1,r), T \in D(r,q_2)\}$.

\subsection{Kleene's Theorem}
\label{sec:kleenes-theorem}

The punchline is \emph{Kleene's Theorem}, which says that the theory
of regular expressions and the theory of DFAs are really ``about the
same thing''.  In particular, the set of strings accepted by a DFA is
always a regular language, and conversely, for every regular language
there exists a DFA which accepts it.  Moreover, the proof of the
theorem is effective: given a regular expression, we may
algorithmically construct a corresponding DFA (and vice versa).  For
example, \todo{put a few examples here}.

\section{Types and DFAs}
\label{sec:types-and-dfas}

Viewing regular expressions via the lens of DFAs gives us exactly the
tools we need to generalize our \emph{ad hoc} analysis from the
introduction.   Consider again the task of encoding a type with the
same shape as
\begin{spec}
data Tree a  =  Leaf a
             |  Fork (Tree a) (Tree a)
\end{spec}
whose sequence of element types matches the regular expression
$(ab)^\ast$, as in the introduction.  This time, however, we will
think about it from the point of view of the corresponding DFA, shown
in \pref{fig:ab-star-dfa}.

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

%format Tij = T "_{ij}"
%format T11
%format T12
%format T21
%format T22

Let |Tij a b| denote the type of binary trees whose element type
sequences take the DFA from state $i$ to state $j$.  Since the DFA has
two states, there are four such types:
\begin{itemize}
\item |T11 a b| --- this is the type of trees we are primarily
  interested in constructing, whose leaf sequences match $(ab)^*$.
\item |T12 a b| --- trees of this type have leaf sequences which
  take the DFA from state $1$ to state $2$; that is, they match the
  regular expression $a(ba)^*$ (or, equivalently, $(ab)^{*}a$).
\item |T21 a b| --- trees matching $b(ab)^*$.
\item |T22 a b| --- trees matching $(ba)^*$.
\end{itemize}

What does a tree of type |T11| look like?  It cannot be a leaf,
because a single leaf takes the DFA from state 1 to 2 or vice versa.
It must be a pair of trees, which together take the DFA from state 1
to state 1.  There are two ways for that to happen: both trees could
themselves begin and end in state 1; or the first tree could take the
DFA from state 1 to state 2, and the second from state 2 to state 1.
We can carry out a similar analysis for the other three types.  In
fact, we have already carried out this exact analysis in the
introduction, but it is now a bit less ad hoc.  In particular, we can
now see that we end up with four mutually recursive types precisely
because the DFA for $(ab)^*$ has two states (and $4 = 2^2$).

% \footnote{In general, we can imagine ending up with \emph{fewer}
%  than $n^2$ mutually recursive types for a DFA of $n$ states---if some
%  of the combinations are impossible or irrelevant---but we will
%  certainly

\section{Matrices of types}
\label{sec:matrices-of-types}

Though shifting our point of view to DFAs has given us a better
framework for determining which types we must define, we still had to
reason on a case-by-case basis to determine the definitions of these
types.  It turns out that we can concisely and elegantly formalize
this process in terms of \emph{matrices}.

At this point, we abstract away from the particular details of
Haskell data types and work in terms of \term{polynomial
  functors}. \todo{explain this better? Shouldn't have to know any CT
  to understand it\dots do we actually make use of functoriality, or
  should we just say ``polynomial type constructors''?}
  \dan{We can try to use what's in https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf
  as a lead, though we have n-ary functors and so we shouldn't get bogged down implementung |bimap| etc.}
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
\times S$.  \todo{need to say something about recursion here.  e.g.,
  note $S$ is defined recursively; typically we would define a least
  fixed-point operation, etc., and we could do that here to make
  things completely formal, but the details will just distract.}
Usually we omit the pre-subscript on $X$ and just write $X_1$, $X_2$
and so on when the arity $n$ is clear from the context.

\todo{formally define ``sequence of leaf types''?}

\dan{Don't know if we want this}
We can define $S(F)$, the language of possible sequences of leaf types
of a multi-argument functor, $F$ as follows:

\begin{itemize}
\item $S(1) = \empty$, the empty sequence
\item $S(F+G) = S(F)+S(G)$
\item $S(F\times G) = S(F)S(G)$
\item \dan{Fixed point???}
\end{itemize}

% \newcommand{\leafseq}[1]{\llbracket #1 \rrbracket}

% $\leafseq{1} = \emptyset$
% $\leafseq{X_i} = \{ i \}$
% $\leafseq{F + G} = \leafseq{F} \union \leafseq{G}$
% $\leafseq{F \times G} = \leafseq{F} \cdot \leafseq{G}$

Suppose we have a one-argument functor $F$ and some DFA $D =
(Q,\Sigma,\delta,q_o,F)$ with $n$ states (that is, $||Q|| = n$).  Let
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

\[ \label{eq:product-of-functors} (FG)_{ij} = \sum_{k \in Q} F_{ik} G_{kj}. \]
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

To make things concrete can revisit some familiar types from this viewpoint. For example consider the resular expression $(aa)^*$. This corresponds to the DFA:
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
Now we'll return to the derivative example of section~\ref{sec:zippers-and-dissections}.
We require the DFA for the regular expression $a^*1a^*$.

\dan{Diagram goes here}

The corresponding transition matrix is:
\[ \m{X} =
\begin{bmatrix}
  |a| & |1| \\
  |0| & |a|
\end{bmatrix}
\]
Now consider using the procedure described in section~\ref{sec:matrices-of-types} to lift
the product of two functors:
\[
F = G \times H
\]
From equation\~ref{eq:product-of-functors} we see that
\[
F_{00} = F_{00}\times G_{00}+F_{01}\times G_{10}
\]
$G_{10}$ is the type of trees whose leaves take our DFA from $1$ to $0$.
But there are no such strings. So $G_{10}$ is the uninhabited type $0$ and
$F_{00} = F_{00}\times G_{00}$.
In fact, $F_{00}$ is simply the type of structures whose leaves take the
DFA from state 0 to state 0 and so whose
leaves match the regular expression $a^*$.
So we have $F_{00} = F$.
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
We described above how $a^*1a^*$ gives rise to zipper types.
We have now shown how these can be computed as derivatives.
  \dan{
  Need to do sums and fixed points.
  }

There is another way to look at this. Write
\[
\m{X} = a\m{1}+\m{d}
\]
where
\[ \m{d} =
\begin{bmatrix}
  |0| & |1| \\
  |0| & |0|
\end{bmatrix}
\]
Note that $\m{d}^2=\m{0}$.
If we have a polynomial $F$, then we have that
\begin{eqnarray}
F(\m{X}) &=& F(a\m{1}+\m{d})\\
&=& F(a\m{1})+F'(a)\m{d}\\
&=& \begin{bmatrix}
  |F(a)| & |0| \\
  |0| & |F(a)|
\end{bmatrix}
+\begin{bmatrix}
  |0| & |F'(a)| \\
  |0| & |0|
\end{bmatrix}
\end{eqnarray}
The matrix $\m{d}$ is playing a role similar to an
``infinitesimal'' in calculus where the expression
$dx$ is manipulated informally as if $(dx)^2=0$.
(Compare wth the dual numbers described by \cite{DBLP:journals/lisp/SiskindP08}.)

\section{Divided differences}
\label{sec:divided-differences}

\begin{itemize}
\item Use the new power to also generalize dissections to divided
  differences.
\end{itemize}

Consider now the DFA for the regular expression $a^*1b^*$.
The corresponding diagram is
\dan{Diagram}
\[ \m{T} =
\begin{bmatrix}
  |a| & |1| \\
  |0| & |b|
\end{bmatrix}
\]
Just as when we considered derivatives, suppose a functor \dan{?} is a
product of two functors
\[
F = G \times H.
\]
Then
\[
F_{00} = F_{00}\times G_{00}+F_{01}\times G_{10}
\]
As before, $G_{10}$ is the type of trees whose leaves take our DFA from $1$ to $0$.
But there are no such strings. So $G_{10}$ is the uninhabited type $0$.
So $F_{00} = F_{00}\times G_{00}$.
As before, $F_{00}$ is structures whose leaves take the DFA from state 0 to state 0 and so whose
leaves match the regular expression $a^*$.
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
We have already argued above in section~\ref{sec:zippers-and-dissections}
that the regular expression $a^*1b^*$
gives rise to dissections. We have now also shown how the algebraic rules for
dissections are actually statements about the transition matrices for the
corresponding DFA.

There is a more familiar interpretation of the dissection operation.
Given a function of a single real variable $f$,
the divided difference is the function of two variables mapping $x_0$, $x_1$ to $(f(x_0)-f(x_1)/(x_0-x_1))$ which is sometimes also written as $[x_0, x_1]f$.
\begin{multline*}
[x_0,x_1](fg) = (f(x_0)g(x_0)-f(x_1)g(x_1))/(x_0-x_1)\\
= (f(x_0)g(x_0)-f(x_0)g(x_1)+f(x_0)g(x_1)-f(x_1)g(x_1))/(x_0-x_1)\\
= f(x_0)[x_0,x_1]g+[x_0,x_1]fg(x_1)
\end{multline*}
This is McBride's modified Leibniz rule.
For polynomial types, dissection is the divided difference.
There is an important caveat: in the usual context of numerical
methods, divided differences are usually defined using
subtraction. Subtraction isn't meaningful for types.
But the Leibniz law above shows that for polynomials divided differences
could have been defined without making reference to subtraction and that
this definition carries over to types.
Notice how in the limit as $x_1\rightarrow x_0$ we recover the derivative.

\section{Discussion}
Technique for constructing types with constraints. Ad hoc rules formalized.
In some sense we've given an explanation for derivatives and dissections.
Hope they can find new applications eg. trees with constraints in the style of
2-3/red-black trees (though maybe it's not the same kind of thing actually).

\acks

Acknowledgments.

\todo{should cite our blog posts on the topic}

% We recommend abbrvnat bibliography style.

\bibliography{type-matrices}{}
\bibliographystyle{abbrvnat}

\end{document}
