% -*- mode: LaTeX; compile-command: "runghc make" -*-
% \documentclass[authoryear,preprint]{sigplanconf}
\documentclass{llncs}

%vim: set makeprg=runghc make:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2tex setup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include lhs2TeX.sty

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Package imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{makeidx}

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

\newrefformat{fig}{Fig.~\ref{#1}}
\newrefformat{sec}{Sect.~\ref{#1}}
\newrefformat{eq}{Equation~\eqref{#1}}
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

%% ACM %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% %\conferenceinfo{WXYZ '05}{date, City.}
% %\copyrightyear{2005}
% %\copyrightdata{[to be supplied]}

% %\titlebanner{banner above paper title}        % These are ignored unless
% %\preprintfooter{short description of paper}   % 'preprint' option specified.

% \title{Matrices! Of Types!}
% %\subtitle{Subtitle Text, if any}

% \authorinfo{Dan Piponi}
%            {Google}
%            {dpiponi@@gmail.com}
% \authorinfo{Brent A. Yorgey}
%            {University of Pennsylvania}
%            {byorgey@@cis.upenn.edu}

% \maketitle

% \begin{abstract}
% Matrices of types are sweet
% \end{abstract}

% %\category{CR-number}{subcategory}{third-level}

% %\terms
% %term1, term2

% %\keywords
% %matrices, types

%% LLNCS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\title{Matrices of Types XXX}

\author{Dan Piponi\inst{1} \and Brent A. Yorgey\inst{2}}
\institute{Google \email{dpiponi@@gmail.com} \and Williams College \email{byorgey@@gmail.com}}

\maketitle

\begin{abstract}
  Matrices of types are sweet
\end{abstract}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
    . hcat' (with & sep .~ 1)
    . map (named "elt" . drawType)
    $ [A,B,A,B,A,B]

dia = lst # frame 0.5
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

The required type is
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
suitable (\term{polynomial}) data type.\brent{actually only for
  \emph{polynomial} types, but we haven't defined that yet... is there
  something we can say to be more accurate without using technical
  terms which haven't yet been introduced?}

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

When writing regular expressions, we allow parentheses for
disambiguation, and adopt the common convention that Kleene star
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
\item $\sem{R^*} = \sem{R}^*$, where $L^*$ denotes the least fixed
  point solution of \[ L^* = \{\varepsilon\} \union LL^*. \] (Such a
  least fixed point exists by the Knaster-Tarski
  theorem~\cite{tarski1955}, since the mapping $\varphi(S) = \{
  \varepsilon \} \union L S$ is monotone, that is, if $S \subseteq T$
  then $\varphi(S) \subseteq \varphi(T)$.)
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

\todo{We need a better story about finite vs. infinite.  The above
  gives the standard presentation of DFAs for finite strings, but
  Haskell types can include infinite values.  So we want to do
  something like use the \emph{greatest} fixed point of $\Sigma^* =
  \varepsilon \union \Sigma \Sigma^*$ and say that an infinite string
  is in the language recognized by a DFA if it never causes the DFA to
  reject.  I'm not quite sure how this relates to the fact that
  least+greatest fixedpoints coincide in Haskell.}

We can draw a DFA as a directed multigraph where each graph edge is
labeled by a symbol from $\Sigma$. Each state is a vertex, and an edge
is drawn from $q_1$ to $q_2$ and labeled with symbol $s$ whenever
$\delta(q_1,s)=q_2$. In addition, we indicate accept states with a
double circle, and always label the start state as $1$.  We can think
of the state of the DFA as ``walking'' through the graph each time it
receives an input.  \pref{fig:dfa-example} shows an example.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import TypeMatricesDiagrams

exampleDFA :: DFA (Diagram Postscript R2, Bool)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 & 0)
  , 3 --> (True,  10 & 0)
  , 4 --> (False, 5 & (-5))
  ]
  [ 1 >-- txtN "a" --> 2
  , 2 >-- txtN "b" --> 1

  , 2 >-- txtN "a" --> 3
  , 3 >-- txtN "b" --> 2

  , 1 >-- (txt "b", True) --> 4
  , 3 >-- txtN "a" --> 4

  , 4 >-- txtN "a,b" --> 4
  ]

txtN s = (txt s, False)

dia = drawDFA exampleDFA # centerXY # pad 1.1
  \end{diagram}
  \caption{An example DFA}
  \label{fig:dfa-example}
\end{figure}
It is convenient to allow the transition function $\delta$ to be
partial.  Operationally, encountering a state $q$ and input $s$ for
which $\delta(q,s)$ is undefined corresponds to the DFA
\emph{rejecting} its input.  This often simplifies matters, since we
may omit ``sink states'' from which there is no path to any accepting
state, making $\delta$ undefined whenever it would have otherwise
yielded such a sink state.  For example, the DFA from
\pref{fig:dfa-example} may be simplified to the one shown in
\pref{fig:dfa-example-simpl}, by dropping state $4$.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import TypeMatricesDiagrams

exampleDFA :: DFA (Diagram Postscript R2)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 & 0)
  , 3 --> (True,  10 & 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1

  , 2 >-- txt "a" --> 3
  , 3 >-- txt "b" --> 2
  ]

dia = drawDFA exampleDFA # centerXY # pad 1.1
  \end{diagram}
  \caption{Example DFA, simplified}
  \label{fig:dfa-example-simpl}
\end{figure}

\dan{ I'm implicitly defining the notion of "taking a DFA from state
  $q_0$ to $q_1$". Is there a better word for this?  } \brent{I'm not
  sure.  In any case, do we even need these paragraphs? Do we use this
  later?}
% Given any pair
% of states $q_1$ and $q_2$ in $Q$ we can consider the set of strings
% that, when input to the DFA, would take it from state $q_1$ to state
% $q_2$. Call this $D(q_0,q_1)$.  The set of strings taking the DFA from
% $q_0$ to a state in $F$ is the set of strings accepted by the DFA. We
% consider the empty string to take the DFA from state $q$ to $q$ for
% any $q$.

% Suppose a string $S$ takes the DFA from $q_1$ to $q_2$. Suppose also
% that we break up our string into two pieces $S=S_1S_2$. Then $S_1$
% must take the DFA from $q_1$ to some intermediate state $r$ and $S_2$
% must take it from state $r$ to $q_2$. In other words $D(q_1,q_2) =
% \bigcup_{r\in Q}\{ST || S \in D(q_1,r), T \in D(r,q_2)\}$.

\subsection{Kleene's Theorem}
\label{sec:kleenes-theorem}

The punchline is \emph{Kleene's Theorem}, which says that the theory
of regular expressions and the theory of DFAs are really ``about the
same thing''.  In particular, the set of strings accepted by a DFA is
always a regular language, and conversely, for every regular language
there exists a DFA which accepts it.  Moreover, the proof of the
theorem is constructive: given a regular expression, we may
algorithmically construct a corresponding DFA (and vice versa).  For
example, the regular expression $a^*1b^*$ corresponds to the DFA shown
in \pref{fig:astar-1-bstar}.  It is not hard to verify that strings
taking the DFA from state $1$ to state $2$ (the accept state) are
precisely those matching the regular expression $a^*1b^*$.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

astar1bstar :: DFA (Diagram Postscript R2)
astar1bstar = dfa
  [ 1 --> (False, origin)
  , 2 --> (True, 5 & 0)
  ]
  [ 1 >-- txt "1" --> 2

  , 1 >-- txt "a" --> 1
  , 2 >-- txt "b" --> 2
  ]

dia = drawDFA astar1bstar # centerXY # pad 1.1
  \end{diagram}
  \caption{A DFA for $a^*1b^*$}
  \label{fig:astar-1-bstar}
\end{figure}

\section{Types and DFAs}
\label{sec:types-and-dfas}

Viewing regular expressions through the lens of DFAs gives us exactly the
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
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

abStar :: DFA (Diagram Postscript R2)
abStar = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 & 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1
  ]

dia = drawDFA abStar # centerXY # pad 1.1
  \end{diagram}
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
because the DFA for $(ab)^*$ has two states, and we need one type for
each ordered pair of states.

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

We now abstract away from the particular details of Haskell data types
and work in terms of a simple language of \term{polynomial
  functors}. \todo{explain this better? Shouldn't have to know any CT
  to understand it\dots do we actually make use of functoriality, or
  should we just say ``polynomial type constructors''?}  \dan{We can
  try to use what's in
  https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf as a
  lead, though we have n-ary functors and so we shouldn't get bogged
  down implementung |bimap| etc.} \todo{cite something? Algebra of Programming?}
\begin{itemize}
\item $1$ denotes the constantly unit functor $1\ a = 1$ (whether $1$
denotes the constantly unit functor or the unit value should be clear
from the context).
\item $X$ denotes the identity functor $X\ a = a$.
\item Given two functors $F$ and $G$, we can form their sum, $(F + G)\
  a = F\ a + G\ a$.
\item We can also form products of functors, $(F \times G)\ a = F\ a
  \times G\ a$.  We often abbreviate $F \times G$ as $FG$.
\item We also allow functors to be defined by mutually recursive
  systems of equations $\overline{F_i = \Phi_i(F_1, \dots, F_n)}^n$,
  and interpret them using a standard least fixed point construction.
  For example, $L = 1 + X\times L$ denotes the standard type of
  polymorphic lists.\todo{explain better.  Note this is only
    \emph{finite} lists, unlike in Haskell.  Or maybe it doesn't
    matter?  Depends on the categories involved.}
\end{itemize}

All of this also generalizes naturally to multi-argument functors:
\begin{itemize}
\item $1\ a_1\ \dots\ a_n = 1$;
\item $(F + G)\ a_1\ \dots\ a_n = (F\ a_1\ \dots\ a_n) + (G\ a_1\ \dots\
  a_n$);
\item $(F \times G)\ a_1\ \dots\ a_n = (F\ a_1\ \dots\ a_n) \times (G\
  a_1\ \dots\ a_n)$;
\item the identity functor $X$ generalizes to the family of
  projections ${}_nX_i$, where \[ {}_nX_i\ a_1\ \dots\ a_n = a_i. \]
\end{itemize}
For example, the Haskell type
\begin{spec}
data S a b = Apple a | Banana b | Fork (S a b) (S a b)
\end{spec}
corresponds to the two-argument functor $S = {}_2X_1 + {}_2X_2 + S
\times S$.  Usually we omit the pre-subscript on $X$ and just write
$X_1$, $X_2$ and so on when the arity $n$ can be inferred from the
context.

\todo{Also translate one of the examples from the introduction into
  this notation, to show the use of mutually recursive systems?}

From this point onwards, as a practical matter, we will assume the
canonical alphabet $\Sigma = \{1, \dots, n\}$.  This is because
functor arguments correspond to alphabet elements, and functor
arguments are identified positionally.

\todo{this should probably be moved later, to some section where we
  formally prove some stuff}
We can define $S(F)$, the language of possible sequences of leaf types
of a multi-argument functor, $F$ as follows:

\newcommand{\leafseq}[1]{\mathcal{S}(#1)}

\begin{align*}
\leafseq{1} &= \{\varepsilon\} \\
\leafseq{X_i} &= \{ i \} \\
\leafseq{F + G} &= \leafseq{F} \union \leafseq{G} \\
\leafseq{F \times G} &= \leafseq{F}\leafseq{G}
\end{align*}
Finally, given $\overline{F_i = \Phi_i(F_1, \dots, F_n)}^n$ we set
\[ \overline{\leafseq{F_i} = \leafseq{\Phi_i(F_1, \dots, F_n)}}^n \]
and take the least fixed point (ordering sets by inclusion).  For
example, given the list functor $L = 1 + XL$, we obtain \[ \leafseq{L}
= \{ \varepsilon \} \union \{ 1\sigma \mid \sigma \in \leafseq{L}
\} \] whose least fixed point is the infinite set $\{ \varepsilon, 1,
11, 111, \dots \}$ as expected.

Suppose we have a one-argument functor $F$ and some DFA $D =
(Q,\Sigma,\delta,q_o,F)$.  Let $F_{ij}$ denote the type with the same
shape as $F$ \brent{should we define this ``have the same shape as''
  thing formally?  I guess the idea would be that $F$ and $G$ have the
  same shape iff $F\ 1\ \dots\ 1 \cong G\ 1\ \dots\ 1$ (where $F$ and
  $G$ could have different arities).}  \dan{ Should that be $F$ and
  $G$ have the same shape iff $F\ a\ \dots\ a \cong G\ a\ \dots\ a$?
  Your definition gives the usual notion of shape: ie. the branching
  structure without regard to what the elements are. But I'm talking
  about the shape as a container with elements.  I'm also not sure we
  need to make this formal.  } but whose sequence of leaf types takes
$D$ from state $i$ to state $j$.  Note that $F_{ij}$ has arity
$||\Sigma||$, that is, there is a leaf type corresponding to each
alphabet symbol of $D$.  We can deduce $F_{ij}$ compositionally by
considering each of the functor building blocks above in turn.

\begin{itemize}
\item The constant functor $1$ creates structures containing no
  elements, \emph{i.e.} which do not cause the DFA to transition at
  all.  So the only way a $1$ structure can take the DFA from state
  $i$ to state $j$ is if $i = j$:
\begin{equation}
  \label{eq:unit-functor}
  1_{ij} =
  \begin{cases}
    1 & i = j \\
    0 & i \neq j
  \end{cases}
\end{equation}

\item The identity functor $X$ creates structures containing a single
  leaf element.  So an $X$ structure containing a single value of type
  $a$ takes the DFA from state $i$ to state $j$ precisely when the DFA
  contains a transition from $i$ to $j$ labeled with $a$. Since there
  may be multiple edges from $i$ to $j$, $X_{ij}$ is therefore the
  \emph{sum} of all the labels on edges from $i$ to $j$.  Formally,
  \begin{equation}
    \label{eq:x-functor}
    X_{ij} = \sum_{\substack{k \in \Sigma \\ \delta(i,k) = j}} X_k.
  \end{equation}
  For example, \todo{give example?} \brent{Not sure if we need an
    example here?  What example would we give?}

\item A value with shape $F + G$ is either a value with shape $F$ or a
  value with shape $G$; so the set of $F + G$ shapes taking the DFA
  from state $i$ to state $j$ is just the sum of the corresponding $F$
  and $G$ shapes:
  \begin{equation}
    \label{eq:sum-of-functors}
    (F + G)_{ij} = F_{ij} + G_{ij}.
  \end{equation}

\item Products are more interesting.  An $FG$-structure consists of an
  $F$-structure paired with a $G$-structure, whose leaf types drive
  the DFA in sequence.  \dan{Should the matrix be transposed?}  Hence,
  in order to take the DFA from state $i$ to state $j$ overall, the
  $F$-structure must take the DFA from state $i$ to some state $k$,
  and then the $G$-structure must take it from $k$ to $j$.  This works
  for any state $k$, and $(FG)_{ij}$ is the sum over all such
  possibilities.  Thus,
  \begin{equation}
    \label{eq:product-of-functors}
    (FG)_{ij} = \sum_{k \in Q} F_{ik} G_{kj}.
  \end{equation}
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

\todo{Say something about implicits/fixed points.  Just do the same
  construction again -- take LFP of implicit matrix equation?  What's
  the order relation?  Actually, I guess it doesn't matter: we're
  really just using matrices as a way to organize systems of type
  equations.}

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
where the meanings of the types $T_{ij}$ \todo{finish}.  The punchline
is that we can take the recursive equation for $T$ and simply apply
the homomorphism to both sides, resulting in the matrix equation
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
the definitions for $T_{ij}$ we derived in \pref{sec:introduction}.

\todo{include a bunch more examples here.  Both other DFAs and other
  types \dots}

%format Lij = L "_{ij}"
%format L11
%format L12
%format L21
%format L22

To make things concrete, we can revisit some familiar types from this
viewpoint. For example consider the resular expression $(aa)^*$. This
corresponds to the DFA shown in \pref{fig:dfa-aa}.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

aaStar :: DFA (Diagram Postscript R2)
aaStar = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 & 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "a" --> 1
  ]

dia = drawDFA aaStar # centerXY # pad 1.1
  \end{diagram}
  \caption{A DFA for $(aa)^*$}
  \label{fig:dfa-aa}
\end{figure}
We now apply the homomorphism to the defining equation for lists,
\[ \m{L} = \m{1} + \m{X}_D \m{L}, \] where the transition matrix in
this case is
\[ \m{X}_D =
\begin{bmatrix}
  |0| & |a| \\
  |a| & |0|
\end{bmatrix}.
\]
This yields
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
    a |L11| & 1+a |L21|
  \end{bmatrix}.
\end{multline*}

We can see that |L11| and |L22| are isomorphic, as are |L12| and
|L21|. \brent{Note this sort of thing arises from automorphisms of the
  DFA?} Thinking about the meaning of paths through the DFA, we see
that |L11| is the type of lists with even length, and |L12|, lists with
odd length. More familiarly:

> data EvenList a  = EvenNil | EvenCons a (OddList a)
> data OddList a   = OddCons a (EvenList a)

%format Bij = B "_{ij}"
%format B11
%format B12
%format B21
%format B22

As another example, consider constructing a type of binary trees with
data of two different types, $a$ and $b$, at internal nodes---but with
the restriction that two values of type $a$ may never occur
consecutively in an inorder traversal.  \todo{mention RE's closed
  under negation, Aho-Corasick construction (Efficient String
  Matching, 1975)?} This restriction corresponds to the DFA shown in
\pref{fig:DFA-no-consec-a}, with the transition matrix
\[ \m{X}_D =
\begin{bmatrix}
  |b| & |a| \\
  |b| & 0
\end{bmatrix}.
\]

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

noAA :: DFA (Diagram Postscript R2)
noAA = dfa
  [ 1 --> (True, origin)
  , 2 --> (True, 5 & 0)
  ]
  [ 1 >-- txt "b" --> 1
  , 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1
  ]

dia = drawDFA noAA # centerXY # pad 1.1
  \end{diagram}
  \caption{A DFA for avoiding consecutive $a$'s}
  \label{fig:DFA-no-consec-a}
\end{figure}

Beginning with $T = 1 + TXT$ and applying the homomorphism, we obtain
\begin{multline*}
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|
  \end{bmatrix}
  =
  \begin{bmatrix}
    1 & 0 \\
    0 & 1
  \end{bmatrix}
  +
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|
  \end{bmatrix}
  \begin{bmatrix}
    b & a \\
    b & 0
  \end{bmatrix}
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|.
  \end{bmatrix}
\end{multline*}
Expanding the right-hand side and equating elementwise yields
\begin{align*}
  |T11| &= 1 + (|T11| + |T12|)b|T11| + |T11|a|T21| \\
  |T12| &=     (|T11| + |T12|)b|T12| + |T11|a|T22| \\
  |T21| &=     (|T21| + |T22|)b|T11| + |T21|a|T21| \\
  |T22| &= 1 + (|T21| + |T22|)b|T12| + |T21|a|T22|,
\end{align*}
or in Haskell notation,

%format Empty11
%format B11
%format A11
%format B12
%format A12
%format B21
%format A21
%format Empty22
%format B22
%format A22

> data T11 a b
>   =  Empty11
>   |  B11 (Either (T11 a b) (T12 a b)) b (T11 a b)
>   |  A11 (T11 a b) a (T21 a b)
>
> data T12 a b
>   =  B12 (Either (T11 a b) (T12 a b)) b (T12 a b)
>   |  A12 (T11 a b) a (T22 a b)
>
> data T21 a b
>   =  B21 (Either (T21 a b) (T22 a b)) b (T11 a b)
>   |  A21 (T21 a b) a (T21 a b)
>
> data T22 a b
>   =  Empty22
>   |  B22 (Either (T21 a b) (T22 a b)) b (T12 a b)
>   |  A22 (T21 a b) a (T22 a b)

(We could also equivalently distribute out products such as $(|T11| +
|T12|)b|T11| = |T11| b |T11| + |T12| b |T11|$ and end up with more
constructors for each data type.) Since both states in the DFA are
accept states, we are actually looking for the sum type

> type T a b = Either (T11 a b) (T12 a b)

\todo{show some example values?}

\todo{show example? discuss remaining issues: (1) inconvenient to use.
  Can ameliorate this with helper functions (?).}

\todo{Can we come up with a nice generic way to hide stuff under
  suitable existential wrappers, exposing an API similar to that of
  the original type but with some additional occurrences of |Maybe|,
  and dynamic type checks?  Could even code this up as a Haskell
  library perhaps\dots}

\section{Derivatives, Again}
\label{sec:derivatives-again}
Now that we have seen the general framework, let's return to the
specific application of computing \emph{derivatives} of data types.
In order to compute a derivative, we need the DFA for the regular
expression $a^*1a^*$, shown in~\pref{fig:DFA-deriv}.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

deriv :: DFA (Diagram Postscript R2)
deriv = dfa
  [ 1 --> (False, origin)
  , 2 --> (True , 5 & 0)
  ]
  [ 1 >-- txt "a" --> 1
  , 1 >-- txt "1" --> 2
  , 2 >-- txt "a" --> 2
  ]

dia = drawDFA deriv # centerXY # pad 1.1
  \end{diagram}
  \caption{A DFA for derivatives}
  \label{fig:DFA-deriv}
\end{figure}

The corresponding transition matrix is
\[ \m{X} =
\begin{bmatrix}
  |a| & |1| \\
  |0| & |a|
\end{bmatrix}.
\]

Suppose we start with a functor defined as a product:
\[ F = G \times H \]
Expanding via the homomorphism to type matrices (using $2 \times 2$
matrices since our DFA has two states), we obtain
\[
\begin{bmatrix}
  F_{11} & F_{12} \\
  F_{21} & F_{22}
\end{bmatrix}
=
\begin{bmatrix}
  G_{11} & G_{12} \\
  G_{21} & G_{22}
\end{bmatrix}
\begin{bmatrix}
  H_{11} & H_{12} \\
  H_{21} & H_{22}
\end{bmatrix}
\]
Let's consider each of the $F_{ij}$ in turn.  First, we have
\[
F_{11} = G_{11} \times H_{11} + G_{12}\times H_{21}
\]
$H_{21}$ is a type whose sequences of leaves take the DFA from state
$2$ to state $1$---but there are no such sequences, since the DFA has
no paths from state $2$ to state $1$. So $H_{21}$ is the uninhabited
type $0$, and $F_{11} = G_{11}\times H_{11}$.  In fact, $F_{11}$ is
simply the type of structures whose leaves take the DFA from state $1$
to itself and so whose leaves match the regular expression $a^*$.  So
we have $F_{11} = F$ (and $G_{11} = G$ and $H_{11} = H$).  Similarly,
$F_{22} = F$.  We also have
\[
F_{12} = G_{11}\times H_{12}+G_{12}\times H_{22}
\]
and thus
\[
F_{12} = G\times H_{12}+G_{12}\times H.
\]

\todo{note that $F_{21}$ ``should be'' zero but if we expand things
  out it doesn't look like it!  Have to do some fixpoint analysis to
  see that it is isomorphic to void.  What does it mean that if we
  take the greatest fixpoint we don't get void? (right?) seems odd.}

This looks suspiciously like the usual Leibniz law for the derivative
of a product. We also know that
\[
1_{12} = 0
\]
and
\[
X_{12} = 1
\]
\dan{Make sure $1$ isn't ambiguous}
These are precisely the rules for differentiating polynomials.
So $F_{12}$ is the derivative of $F$.
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

\section{Divided Differences}
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
F_{11} = G_{11}\times H_{11}+G_{12}\times H_{21}
\]
As before, $H_{21}$ contains sequences of leaves which take the DFA
from state $2$ to state $1$; but there are no such strings. So $H_{21}$ is the uninhabited type $0$.
So $F_{11} = G_{11}\times H_{11}$.
As before, $F_{11}$ is structures whose leaves take the DFA from state $1$ to itself and so whose
leaves match the regular expression $a^*$.
So we have simply that $F_{11}(a,b) = F(a)$.
However, we now have that $F_{22}(a,b) = F(b)$.
We also have
\[
F_{12} = G_{11}\times H_{12}+G_{12}\times H_{22}
\]
So
\[
F_{12}(a,b) = G(a)\times H_{12}(a,b)+G_{12}(a,b)\times H(b)
\]
This is the modified Leibniz rule described in \cite{dissection}.
\dan{Do other operations}
We have already argued above in \pref{sec:zippers-and-dissections}
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

\section{Composition}
\label{sec:composition}

\todo{Composition of functors.  Can't extend the homomorphism but we
  can say something about it.}


\todo{Write something about associativity/commutativity?  Holds for
  types up to isomorphism but we might want something a bit stronger
  at times.}

\section{Encoding in Haskell}

\brent{Maybe something should go here about encoding some of this
  automatically in Haskell with type-level computation.  Or maybe in
  Agda.  Needs to be fleshed out.}

\section{Discussion}
Technique for constructing types with constraints. Ad hoc rules formalized.
In some sense we've given an explanation for derivatives and dissections.
Hope they can find new applications eg. trees with constraints in the style of
2-3/red-black trees (though maybe it's not the same kind of thing actually).

\section*{Acknowledgments}
\label{sec:acknowledgments}

Acknowledgments.

\todo{should cite our blog posts on the topic}

\todo{should cite Duchon, Flajolet, Louchard, Schaeffer, ``Boltzmann
  Samplers for Random Generation'' --- they hint at something related
  to this idea on p. 590.}

\bibliography{type-matrices}{}
\bibliographystyle{abbrvnat}

\end{document}
