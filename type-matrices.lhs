% -*- mode: LaTeX; compile-command: "runghc make" -*-
% \documentclass[authoryear,preprint]{sigplanconf}
\documentclass{llncs}

%vim: set makeprg=runghc make:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2tex setup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include forall.fmt
%include lhs2TeX.sty

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Package imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% \usepackage[style=authoryear]{biblatex}
%% \bibliography{type-matrices}

% \usepackage[authoryear]{natbib}
\newcommand{\citep}[1]{\cite{#1}}

\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{tikz}
\usepackage{prettyref}
\usepackage{xspace}
\usepackage{url}

\usepackage[outputdir=diagrams/,backend=cairo,extension=pdf]{diagrams-latex}
% \usepackage{verbatim}
% \newenvironment{diagram}[1]{\comment}{\endcomment}

\graphicspath{{symbols/}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Semantic markup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\pkg}[1]{\texttt{#1}}
\newcommand{\ext}[1]{\texttt{#1}}
\newcommand{\module}[1]{\texttt{#1}}

\newcommand{\ie}{i.e.\xspace}
\newcommand{\eg}{e.g.\xspace}
\newcommand{\etal}{\emph{et al.}\xspace}

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

\newif\ifcomments\commentsfalse

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

%% a bit more space for matrices
\setlength{\arraycolsep}{5pt}

\newcommand{\union}{\cup}

% regular expression alternation/choice operator
\newcommand{\alt}{+}

\newcommand{\sem}[1]{\ensuremath{\left\llbracket #1 \right\rrbracket}}

% \newcommand{\m}[1]{\mathbf{#1}}
\newcommand{\m}[1]{\left[ {#1} \right]}
\newcommand{\mD}[1]{\m{#1}_D}

\newcommand{\dissect}{\includegraphics{Dissect}}
\newcommand{\clowns}{\includegraphics{Clowns}}
\newcommand{\jokers}{\includegraphics{Jokers}}

\newcommand{\N}{\mathbb{N}}
\newcommand{\R}{\mathbb{R}}

\newcommand{\leafseqsym}{\mathcal{S}}
\newcommand{\leafseq}[1]{\leafseqsym(#1)}

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

\title{Polynomial Functors Constrained by Regular Expressions}
%% ``Regular Types''?
%% ``Regular Types with Regular Leaf Sequences''?

\author{Dan Piponi\inst{1} \and Brent A. Yorgey\inst{2}}
\institute{Google, \email{dpiponi@@gmail.com} \and Williams College, \email{byorgey@@gmail.com}}

\maketitle

\begin{abstract}
  We show that every regular language, via some DFA which accepts it,
  gives rise to a homomorphism from the semiring of polynomial
  functors to the semiring of $n \times n$ matrices over polynomial
  functors.  Given some polynomial functor and a regular language,
  this homomorphism can be used to automatically derive a functor
  whose values have the same shape as those of the original functor,
  but whose sequences of leaf types correspond to strings in the
  language.

  The primary interest of this result lies in the fact that certain
  regular languages correspond to previously studied derivative-like
  operations on polynomial functors, which have proven useful in
  program construction.  For example, the regular language $a^*ha^*$
  yields the \emph{derivative} of a polynomial functor, and $b^*ha^*$
  its \emph{dissection}.  Using our framework, we are able to unify
  and lend new perspective on this previous work.  For example, it
  turns out that dissection of polynomial functors corresponds to
  taking \emph{divided differences} of real or complex functions, and,
  guided by this parallel, we show how to generalize binary dissection
  to $n$-ary dissection.

  \keywords{polynomial, functors, regular expressions,
    differentiation, dissection}
\end{abstract}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Introduction}
\label{sec:introduction}

Consider the standard polymorphic singly-linked list type, which can
be defined in Haskell \citep{haskell} as:

> data List a  =  Nil
>              |  Cons a (List a)

This type is \term{homogeneous}, meaning that each element in the list has
the same type as every other element.

Suppose, however, that we wanted lists with a different constraint on
the types of its elements.  For example, we might want lists whose
elements alternate between two types |a| and |b|, beginning with |a|
and ending with |b|.

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

%format List1
%format List2
%format Nil1
%format Cons1
%format Cons2

> data List1 a b  =  Nil1
>                 |  Cons1 a (List2 a b)
>
> data List2 a b  =  Cons2 b (List1 a b)

The required type is
|List1 a b|: a value of type |List1 a b| must be either empty (|Nil1|)
or contain a value of type |a|, followed by a value of type |b|,
followed recursively by another |List1 a b|.

In fact, we can think of |List1 a b| as containing values whose
\term{shape} corresponds to the original |List| type (that is, there
is a natural embedding from |List1 a a| into |List a|, \ie an
injective polymorphic function |forall a. List1 a a -> List a|), but whose
sequence of element types corresponds to the \term{regular expression}
$(ab)^*$, that is, any number of repetitions of the sequence $ab$.

We can easily generalize this idea to regular expressions other than
$(ab)^*$ (though constructing the corresponding types may be
complicated). We can also generalize to algebraic data types other
than |List|, by considering the sequence of element types encountered
by a canonical inorder traversal of each data structure
\citep{mcbride2008applicative}.  That is, in general, given some
algebraic data type and a regular expression, we consider the problem
of constructing a corresponding algebraic data type ``of the same
shape'' but with sequences of element types matching the regular
expression.

%format Tree12
%format Tree11
%format Tree22
%format Tree21

%format Fork12
%format Fork12' = Fork12 "^\prime"
%format Fork11
%format Fork11' = Fork11 "^\prime"
%format Fork22
%format Fork22' = Fork22 "^\prime"
%format Fork21
%format Fork21' = Fork21 "^\prime"

%format Leaf12
%format Leaf11
%format Leaf22
%format Leaf21

For example, consider the following type |Tree| of nonempty binary
trees with data stored in the leaves:
> data Tree a  =  Leaf a
>              |  Fork (Tree a) (Tree a)
%if False
>                 deriving Show
%endif
Consider again the problem of writing down a type whose values have
the same shape as values of type |Tree a|, but where the data elements
alternate between two types |a| and |b|, beginning with a leftmost
element of type |a| and ending with a rightmost element of type |b|.
An example can be seen in \pref{fig:alt-tree}.

\begin{figure}
  \centering
\begin{diagram}[width=150]
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import TypeMatricesDiagrams

t = nd
    [ nd
      [ nd $
          leaves [A, B]
      , lf A
      ]
    , nd
      [ nd
        [ lf B
        , nd $ leaves [A, B]
        ]
      , nd $ leaves [A, B]
      ]
    ]
  where nd     = Node Nothing
        lf x   = Node (Just x) []
        leaves = map lf

dia = renderT t # frame 0.5
\end{diagram}
%$
  \caption{A tree with alternating leaf types}
  \label{fig:alt-tree}
\end{figure}

Suppose |Tree12 a b| is such a type. Values of type |Tree12 a b|
cannot consist solely of a leaf node: there must be at least two
elements, one of type |a| and one of type |b|.  Hence a value of type
|Tree12 a b| must be a fork consisting of two subtrees.  There are two
ways this could happen.  The left subtree could start with |a| and end
with |b|, in which case the right subtree must also start with |a| and
end with |b|.  Or the left subtree could start with |a| and end with
|a|, in which case the right subtree must start with |b| and end with
|b|. So we are led to define
> data Tree12 a b  =  Fork12  (Tree12 a b)  (Tree12 a b)
>                  |  Fork12' (Tree11 a b)  (Tree22 a b)
%if False
>                     deriving Show
%endif
where |Tree11 a b| represents alternating trees with left and
rightmost elements both of type |a|, and similarly for |Tree22|.

Of course, we are now left with the task of defining |Tree11| and
|Tree22|, but we can carry out similar reasoning: for example a
|Tree11| value can either be a single leaf of type |a|, or a branch
with a |Tree12| and |Tree11|, or a |Tree11| and |Tree21|.  All told,
we obtain
> data Tree11 a b  =  Leaf11 a
>                  |  Fork11  (Tree12 a b)  (Tree11 a b)
>                  |  Fork11' (Tree11 a b)  (Tree21 a b)
%if False
>                     deriving Show
%endif
> data Tree22 a b  =  Leaf22 b
>                  |  Fork22  (Tree22 a b)  (Tree12 a b)
>                  |  Fork22' (Tree21 a b)  (Tree22 a b)
%if False
>                     deriving Show
%endif
> data Tree21 a b  =  Fork21  (Tree22 a b)  (Tree11 a b)
>                  |  Fork21' (Tree21 a b)  (Tree21 a b)
%if False
>                     deriving Show
%endif
Any tree of type |Tree12 a b| is now constrained to have alternating
leaf node types.  For example, here are two values of type |Tree12 Int
Char|:

%format ex1
%format ex2

> ex1, ex2 :: Tree12 Int Char
> ex1 = Fork12' (Leaf11 1) (Leaf22 'a')
> ex2 = Fork12' (Fork11 ex1 (Leaf11 2)) (Leaf22 'b')

|ex2| can also be seen in pictorial form in \pref{fig:alt-tree-hs}.

\begin{figure}
  \centering
\begin{tikzpicture}[level/.style={sibling distance=50mm/#1}]
\node {|Fork12'|}
  child {
      node {|Fork11|}
          child {node {|Fork12'|}
                    child {node {|Leaf11 1|}}
                    child {node {|Leaf22 "a"|}}
          }
          child {node {|Leaf11 1|}}
  }
  child {node {|Leaf22 "b"|}};
\end{tikzpicture}
  \caption{A tree with alternating leaf types}
  \label{fig:alt-tree-hs}
\end{figure}

While this works, the procedure was somewhat {\it ad hoc}. We reasoned
about the properties of the pieces that result when a string matching
$(ab)^*$ is split into two substrings, and used this to find
corresponding types for the subtrees. One might wonder why we ended up
with four mutually recursive types---is there any simpler solution?
And how well does this sort of reasoning extend to more complicated
structures or regular expressions?  Our goal will be to derive a more
principled way to do this analysis for any regular language and any
suitable (\term{polynomial}) data type.

For certain languages, this problem has already been explored in the
literature, though without being phrased in terms of regular
languages.  For example, consider the regular language $a^*ha^*$. It
matches sequences of $a$s with precisely one occurrence of $h$
somewhere in the middle.  Data structures whose inorder sequence of
element types matches $a^*ha^*$ have all elements of type |a|, except
for one which has type |h|. This corresponds to a zipper type
\citep{Huet_zipper} with elements of type $h$ at the `focus'; if we
substitute the unit type for |h|, we get the \term{derivative} of the
original type \citep{DBLP:journals/fuin/AbbottAMG05}
(\pref{fig:derivative}).  Likewise, the regular language $b^*ha^*$
corresponds to \term{dissection types} \citep{mcbride-dissection}.

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

dia = renderT t # frame 0.5
  \end{diagram}
  \caption{A tree corresponding to the regular language $a^*ha^*$}
  \label{fig:derivative}
\end{figure}

Zippers, derivatives and dissections are usually described using
Leibniz rules and their generalizations. We'll show how these rules
can be placed in a more general framework applying to any regular
language.

In the remainder of the paper, we first review some standard results
about regular languages and DFAs (\pref{sec:regexp-and-dfas}).  We
describe our framework informally (\pref{sec:dfas-matrices}) and give
some examples of its application (\pref{sec:examples}) and describe an
alternative encoding which can be more convenient in practice
(\pref{sec:alternative}). We conclude with a discussion of
derivatives (\pref{sec:derivatives-again}) and divided differences
(\pref{sec:divided-differences}).

\section{Regular Expressions and DFAs}
\label{sec:regexp-and-dfas}

We begin with a review of the basic theory of regular languages
and deterministic finite automata in Sections
\ref{sec:regexps}--\ref{sec:kleenes-theorem}.  Readers already
familiar with this theory may safely skip these sections.  In Section
\ref{sec:semirings} we introduce some preliminary material on star
semirings which, though not novel, may not be as familiar to readers.

\subsection{Regular Expressions}
\label{sec:regexps}

A \term{regular expression} \citep{kleene1951representation} over an
alphabet $\Sigma$ is a term of the following grammar:
\begin{equation}
R ::= \bullet \mid \varepsilon \mid a \in \Sigma \mid R \alt R  \mid
RR \mid R^*
\end{equation}

When writing regular expressions, we allow parentheses for
disambiguation, and adopt the common convention that Kleene star
($R^*$) has higher precedence than concatenation ($RR$), which has
higher precedence than alternation ($R \alt R$).

Semantically, we can interpret each regular expression $R$ as a set of
strings $\sem R \subseteq \Sigma^*$, where $\Sigma^*$ denotes the set
of all finite sequences built from elements of $\Sigma$.  In
particular,
\begin{itemize}
\item $\sem \bullet = \varnothing$ denotes the empty set.
\item $\sem \varepsilon = \{\varepsilon\}$ denotes the singleton set
  containing the empty string.
\item $\sem a = \{a\}$ denotes the singleton set containing the
  length-$1$ sequence $a$.
\item $\sem{R_1 + R_2} = \sem{R_1} \union \sem{R_2}$.
\item $\sem{R_1 R_2} = \sem{R_1} \sem{R_2}$, where $L_1 L_2$ denotes
  pairwise concatenation of sets, \[ L_1 L_2 = \{ s_1 s_2 \mid s_1 \in
  L_1, s_2 \in L_2 \}. \]
\item $\sem{R^*} = \sem{R}^*$, where $L^*$ denotes the least fixed
  point solution of \[ L^* = \{\varepsilon\} \union LL^*. \] Note that
  such a least fixed point must exist by the Knaster-Tarski
  theorem~\citep{tarski1955}, since the mapping $\varphi(S) = \{
  \varepsilon \} \union L S$ is monotone, that is, if $S \subseteq T$
  then $\varphi(S) \subseteq \varphi(T)$.
\end{itemize}

Finally, a \term{regular language} over the alphabet $\Sigma$ is a set
$L \subseteq \Sigma^*$ which is the interpretation $L = \sem R$ of
some regular expression $R$.

\subsection{DFAs}
\label{sec:dfas}

\newcommand{\accept}{\mathcal{A}}

A {\it deterministic finite automaton} (DFA) is a quintuple $(Q,
\Sigma, \delta, q_0, \accept)$ consisting of
\begin{itemize}
\item a nonempty set of states $Q$,
\item a set of input symbols $\Sigma$,
\item a \term{transition function} $\delta : Q\times\Sigma \to Q$,
\item a distinguished \term{start state} $q_0 \in Q$, and
\item a set $\accept \subseteq Q$ of \term{accept states}. (One often
  sees $F$ used to represent the set of accept or ``final'' states,
  but this would conflict with our use of $F$ to represent functors
  later.)
\end{itemize}

We can ``run'' a DFA on an input string by feeding it symbols from the
string one by one.  When encountering the symbol $s$ in state $q$, the
DFA changes to state $\delta(q,s)$.  If a DFA beginning in its start
state $q_0$ ends in state $q'$ after being fed a string in this way,
we say the DFA \term{accepts} the string if $q' \in \accept$, and
\term{rejects} the string otherwise.  Thus, a DFA $D$ can be seen as
defining a subset $L_D \subseteq \Sigma^*$ of the set of all possible
strings, namely, those strings which it accepts.

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

exampleDFA :: DFA (Diagram B, Bool)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 ^& 0)
  , 3 --> (True,  10 ^& 0)
  , 4 --> (False, 5 ^& (-5))
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

dia = drawDFA exampleDFA # frame 0.5
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

exampleDFA :: DFA (Diagram B)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 ^& 0)
  , 3 --> (True,  10 ^& 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1

  , 2 >-- txt "a" --> 3
  , 3 >-- txt "b" --> 2
  ]

dia = drawDFA exampleDFA # frame 0.5
  \end{diagram}
  \caption{Example DFA, simplified}
  \label{fig:dfa-example-simpl}
\end{figure}

\newcommand{\pfun}{\rightharpoonup}

As is standard, we may define $\delta^* : Q \times \Sigma^* \pfun Q$ as
an iterated version of $\delta$:
\begin{align}
  \delta^*(q,\varepsilon) & = q \\
  \delta^*(q, s \omega)   & = \delta^*(\delta(q,s), \omega)
\end{align}

If $\delta^*(q_0, \omega) = q_1$, then we say that the string $\omega$
``takes'' or ``drives'' the DFA from state $q_0$ to state $q_1$.  More
generally, given a string $\omega$, we can partially apply $\delta^*$
to obtain a ``driving function'' $\chi : Q \pfun Q$ which encodes how
the string $\omega$ drives the DFA: if the DFA starts in state $q$
then after processing $\omega$ it will either halt with an error or
end in state $\chi(q)$.

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

Connecting the previous two sections is \emph{Kleene's Theorem}, which
says that the theory of regular expressions and the theory of DFAs are
really ``about the same thing''.  In particular, the set of strings
accepted by a DFA is always a regular language, and conversely, for
every regular language there exists a DFA which accepts it.  Moreover,
the proof of the theorem is constructive: given a regular expression,
we may algorithmically construct a corresponding DFA, and vice versa.
For example, the regular expression $b^*ha^*$ corresponds to the DFA
shown in \pref{fig:bstar-h-astar}.  It is not hard to verify that
strings taking the DFA from state $1$ to state $2$ (the accept state)
are precisely those matching the regular expression $b^*ha^*$.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

bstarhastar :: DFA (Diagram B)
bstarhastar = dfa
  [ 1 --> (False, origin)
  , 2 --> (True, 5 ^& 0)
  ]
  [ 1 >-- txt "h" --> 2

  , 1 >-- txt "b" --> 1
  , 2 >-- txt "a" --> 2
  ]

dia = drawDFA bstarhastar # frame 0.5
  \end{diagram}
  \caption{A DFA for $b^*ha^*$}
  \label{fig:bstar-h-astar}
\end{figure}

The precise details of these constructions are not important for the
purposes of this paper; interested readers should consult a reference
such as Sipser \citep{sipser2012introduction}. %% citet
We note in passing that one can also associate \emph{nondeterministic}
finite automata (NFAs) to regular expressions, and the remainder of
the story of this paper could probably be retold using NFAs.  However,
it is not clear whether we would gain any benefit from making this
generalization, so we will stick with the simpler notion of DFAs.

\subsection{Semirings}
\label{sec:semirings}

A \term{semiring} is a set $R$ equipped with two binary operations,
$+$ and $\cdot$, and two distinguished elements, $0, 1 \in R$, such
that
\begin{itemize}
  \item $(+,0)$ is a commutative monoid (that is, $0$ is an identity for
$+$, and $+$ is commutative and associative),
  \item $(\cdot,1)$ is a monoid,
  \item $\cdot$ distributes over $+$ from both the left and the right,
    that is, $a \cdot (b + c) = a \cdot b + a \cdot c$ and $(b + c)
    \cdot a = b \cdot a + c \cdot a$, and
  \item $0$ is an annihilator for $\cdot$, that is $r \cdot 0 = 0
    \cdot r = 0$ for all $r \in R$.
\end{itemize}

Examples of semirings include:
\begin{itemize}
\item $(|Bool|, \lor, |False|, \land, |True|)$, boolean values under disjunction and conjunction;
\item $(\N, +, 0, \cdot, 1)$, the natural numbers under addition and multiplication;
\item $(\R^+ \cup \{-\infty\}, \max, -\infty, +, 0)$, the nonnegative
  real numbers (adjoined with $-\infty$) under maximum and addition;
\item the set of regular languages forms a semiring under the operations of union
  and pairwise concatenation, with $0 = \varnothing$ and $1 = \{\varepsilon\}$.
\end{itemize}

A \term{star semiring} or \term{closed semiring}
\citep{lehmann1977algebraic} has an additional operation, $(-)^*$,
satisfying the axiom
\begin{equation}
r^* = 1 + r \cdot r^* = 1 + r^* \cdot r\,,
\end{equation}
for all $r \in R$.  Intuitively, $r^* = 1 + r + r^2 + r^3 + \dots$
(although such infinite sums do not necessarily make sense in all
semirings).  The semiring of regular languages is closed, via Kleene
star.\footnote{In fact, regular languages (and several of the other
  examples above) form \term{Kleene algebras}, which essentially add
  to a star semiring the requirement that $+$ is idempotent ($a + a =
  a$). However, for our purposes we do not need the extra
  restriction.}

If $R$ is a semiring, then the set of $n \times n$ matrices with
elements in $R$ is also a semiring, where matrix addition and
multiplication are defined in the usual manner in terms of addition
and multiplication in $R$.  If $R$ is a star semiring, then a star
operator can also be defined for matrices; for details see
Lehmann \citep{lehmann1977algebraic} and Dolan
\citep{dolan2013fun}. %% citet x 2

Finally, a \term{semiring homomorphism} is a mapping from the elements
of one semiring to another that preserves the semiring structure, that
is, that sends $0$ to $0$, $1$ to $1$, and preserves addition and
multiplication.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{DFAs and Matrices of Functors}
\label{sec:dfas-matrices}

Viewing regular expressions through the lens of DFAs gives us exactly the
tools we need to generalize our \emph{ad hoc} analysis from the
introduction.

\subsection{A More Principled Derivation}
\label{sec:principled}

Consider again the task of encoding a type with the same shape as
\begin{spec}
data Tree a  =  Leaf a
             |  Fork (Tree a) (Tree a)
\end{spec}
whose sequence of element types matches the regular expression
$(ab)^*$, as in the introduction.  This time, however, we will
think about it from the point of view of the corresponding DFA, shown
in \pref{fig:ab-star-dfa}.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

abStar :: DFA (Diagram B)
abStar = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 ^& 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1
  ]

dia = drawDFA abStar # frame 0.5
  \end{diagram}
  \caption{A DFA for $(ab)^*$}
  \label{fig:ab-star-dfa}
\end{figure}

%format Tij = T "_{ij}"
%format T11
%format T12
%format T21
%format T22

The key is to consider not just the data type we are ultimately
interested in---in this case, those trees which take the DFA from
state $1$ to itself---but an entire family of related types. In
particular, let |Tij a b| denote the type of binary trees whose
element type sequences take the DFA from state $i$ to state $j$.
Since the DFA has two states, there are four such types:
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

In general, given a DFA with states $Q$ and alphabet $\Sigma = \{a_1,
\dots, a_n\}$, we get a mutually recursive family of types \[ T_{ij}\
a_1\ \dots\ a_n \] indexed by a pair of states from $Q$ and by one
type argument for each alphabet symbol. We are ultimately interested
in types of the form $T_{q_0 k}$ where $k \in \accept$, that is, types
which are indexed by the start state and some accept state of the DFA.

Though shifting our point of view to DFAs has given us a better
framework for determining which types we must define, we still had to
reason on a case-by-case basis to determine the definitions of these
types.  The next two sections show how we can concisely and elegantly
formalize this process in terms of \emph{matrices}.

\subsection{Polynomial Functors}
\label{sec:polynomial-functors}

\newcommand{\Fun}{\ensuremath{\mathbf{Fun}}}

We now abstract away from the particular details of Haskell data types
and work in terms of a simple language of \term{polynomial functors}.
We inductively define the universe \Fun\ of polynomial functors as
follows, simultaneously giving both syntax and semantics.
\begin{itemize}
\item $K_A \in \Fun$ denotes the constant functor $K_A\ a = A$,
  which ignores its argument and yields $A$.
\item $X \in \Fun$ denotes the identity functor $X\ a = a$.
\item Given $F, G \in \Fun$, we can form their sum, $F + G \in \Fun$,
  with $(F + G)\ a = F\ a + G\ a$.
\item We can also form products of functors, $(F \times G)\ a = F\ a
  \times G\ a$.  We often abbreviate $F \times G$ as $FG$.
\item Finally, we allow functors to be defined by mutually recursive
  systems of equations \[
  \begin{cases}
    F_1 = \Phi_1(F_1, \dots, F_n) \\
    \vdots \\
    F_n = \Phi_n(F_1, \dots, F_n),
  \end{cases}
  \]
  where each $\Phi_k$ is a polynomial functor expression with free
  variables in $\{F_1, \dots, F_n\}$, and interpret them using a
  standard least fixed point semantics.  For example, the single
  recursive equation $L = 1 + X \times L$ denotes the standard type of
  (finite) polymorphic lists.  As another example, the pair of
  mutually recursive equations
  \begin{align*}
    E & = K_{|Unit|} + X \times O \\
    O & = X \times E
  \end{align*}
  defines the types of even- and odd-length polymorphic lists.  Here,
  |Unit| denotes the unit type with a single inhabitant.
\end{itemize}

It is worth pointing out that functors form a semiring (up to
isomorphism) under $+$ and $\times$, where $1 = K_{|Unit|}$ and $0 =
K_{|Void|}$ (|Void| denotes the type with no inhabitants).  We
therefore will simply write $0$ and $1$ in place of $K_{|Unit|}$ and
$K_{|Void|}$.  In fact, functors also form a star semiring, with the
polymorphic list type playing the role of the star
operator, that is, $F^* = 1 + F \times F^*$.

The above language also generalizes naturally from unary to $n$-ary
functors.  We write $\Fun_n$ for the universe of $n$-ary polynomial
functors, so $\Fun = \Fun_1$.
\begin{itemize}
\item $K_A\ a_1\ \dots\ a_n = A$.
\item The identity functor $X$ generalizes to the family of
  projections $X_m$, where \[ X_m\ a_1\ \dots\ a_n = a_m. \] That is,
  $X_m$ is the functor which yields its $m$th argument, and may be
  regarded as an $n$-ary functor for any $n \geq m$.  More generally,
  the arguments to a functor can be labeled by the elements of some
  alphabet $\Sigma$, instead of being numbered positionally, and we
  write $\Fun_\Sigma$ for the universe of such functors.  In that
  case, for $a \in \Sigma$ we write $X_a$ for the projection which
  picks out the argument labeled by $a$.
\item $(F + G)\ a_1\ \dots\ a_n = (F\ a_1\ \dots\ a_n) +
  (G\ a_1\ \dots\ a_n)$.
\item $(F \times G)\ a_1\ \dots\ a_n =
  (F\ a_1\ \dots\ a_n) \times (G\ a_1\ \dots\ a_n)$.
\item Recursion also generalizes straightforwardly.
\end{itemize}
Of course, $n$-ary functors also form a semiring for any $n$.

As an example, the Haskell type
\begin{spec}
data S a b = Apple a | Banana b | Fork (S a b) (S a b)
\end{spec}
corresponds to the bifunctor (that is, $2$-ary functor) $S = X_a + X_b
+ S \times S$; we may also abbreviate $S \times S$ as $S^2$.

\newcommand{\power}{\mathcal{P}}

By induction over functor descriptions, we may define $\leafseqsym :
\Fun_\Sigma \to \power(\Sigma^*)$ which gives the sequences of leaf
types that can occur in the values of a given functor.  Thinking of
values of a given functor as trees, $\leafseq{-}$ corresponds to an
inorder traversal.  That is:
\begin{align*}
\leafseq{0}   &= \varnothing \\
\leafseq{K_A} &= \{\varepsilon\} \quad (A \neq |Void|) \\
\leafseq{X_a} &= \{ a \} \\
\leafseq{F + G} &= \leafseq{F} \union \leafseq{G} \\
\leafseq{F \times G} &= \leafseq{F}\leafseq{G}
\end{align*}
Finally, given a system $F_m = \Phi_m(F_1, \dots, F_n)$ we simply set
\[ \leafseq{F_m} = \leafseq{\Phi_m(F_1, \dots, F_n)} \]
for each $m$, and take the least fixed point (ordering sets by
inclusion).  For example, given the list functor $L = 1 + XL$, we
obtain \[ \leafseq{L} = \{ \varepsilon \} \union \{ 1\sigma \mid
\sigma \in \leafseq{L} \} \] whose least fixed point is the infinite
set $\{ \varepsilon, 1, 11, 111, \dots \}$ as expected.

\subsection{Matrices of Functors}
\label{sec:matrices-of-functors}

Now suppose we have a unary functor $F$ and some DFA $D =
(Q,\Sigma,\delta,q_0,\accept)$.  Let $F_{ij} \in \Fun_\Sigma$ denote the type with the
same shape as $F$ but whose sequences of leaf types take $D$ from
state $i$ to state $j$.  We are ultimately interested in
constructing \[ \sum_{k \in \accept} T_{q_0 k}, \] the sum of all
types $T_{ij}$ whose leaf sequences start in state $q_0$ and take the
DFA to some accept state. Note that $F_{ij}$ has arity $\Sigma$, that
is, there is a leaf type corresponding to each alphabet symbol of $D$.
We can deduce $F_{ij}$ compositionally, by recursion on the syntax of
functor expressions.

\begin{itemize}
\item The constant functor $K_A$ creates structures containing no
  elements, \emph{i.e.} which do not cause the DFA to transition at
  all.  So the only way a $K_A$-structure can take the DFA from state
  $i$ to state $j$ is if $i = j$:
\begin{equation}
  (K_A)_{ij} =
  \begin{cases}
    K_A & i = j \\
    0 & i \neq j
  \end{cases}
\end{equation}
As a special case, the functor $1 = K_{|Unit|}$ yields
\begin{equation}
\label{eq:unit-functor}
1_{ij} =
\begin{cases}
  1 & i = j \\
  0 & i \neq j
\end{cases}.
\end{equation}

\item A value with shape $F + G$ is either a value with shape $F$ or a
  value with shape $G$; so the set of $F + G$ shapes taking the DFA
  from state $i$ to state $j$ is the disjoint sum of the corresponding
  $F$ and $G$ shapes:
  \begin{equation}
    \label{eq:sum-of-functors}
    (F + G)_{ij} = F_{ij} + G_{ij}.
  \end{equation}

\item Products are more interesting.  An $FG$-structure consists of an
  $F$-structure paired with a $G$-structure, whose leaf types drive
  the DFA in sequence. Hence, in order to take the DFA from state $i$
  to state $j$ overall, the $F$-structure must take the DFA from state
  $i$ to some state $k$, and then the $G$-structure must take it from
  $k$ to $j$.  This works for any state $k$, so $(FG)_{ij}$ is the
  sum over all such possibilities.  Thus,
  \begin{equation}
    \label{eq:product-of-functors}
    (FG)_{ij} = \sum_{k \in Q} F_{ik} G_{kj}.
  \end{equation}

\item Finally, for a recursive system of functors \[ \overline{F_m} =
  \overline{\Phi_m(F_1, \dots, F_n)}, \] we may mutually define \[
  (F_m)_{ij} = \left( \Phi_m(F_1, \dots, F_n) \right)_{ij}, \]
  interpreted via the same least fixed point semantics.
\end{itemize}

The above rules for $1$, sums, and products might look familiar: in
fact, they are just the definitions of the identity matrix, matrix
addition, and matrix product.  That is, given some functor $F$ and DFA
$D$, we can arrange all the $F_{ij}$ in a matrix, $\mD{F}$, whose
$(i,j)$th entry is $F_{ij}$. (We also write simply $\m{F}$ when $D$
can be inferred.)  Then we can rephrase
\eqref{eq:unit-functor}--\eqref{eq:product-of-functors} above as

\begin{itemize}
\item $\mD{1} = I_{||\Sigma||}$, that is, the $||\Sigma|| \times
  ||\Sigma||$ identity matrix, with ones along the main diagonal and
  zeros everywhere else;
\item $\mD{F+G} = \mD F + \mD G$; and
\item $\mD{FG} = \mD F \mD G$.
\end{itemize}

So far, given a DFA $D$, we have the makings of a homomorphism from
the semiring of arity-$1$ functors to the semiring of $||Q|| \times
||Q||$ matrices of arity-$\Sigma$ functors.  However, there is
still some unfinished business, namely, the interpretation of
$\mD{X}$.  This gets at the heart of the matter, and to understand it,
we must take a slight detour.

\subsection{Transition Matrices}
\label{sec:transition-matrices}

Given a simple directed graph $G$ with $n$ nodes, its \term{adjacency
  matrix} is an $n \times n$ matrix $M_G$ with a $1$ in the $i,j$
position if there is an edge from node $i$ to node $j$, and a $0$
otherwise.  It is a standard observation that the $m$th power of $M_G$
encodes information about length-$m$ paths in $G$; specifically, the
$i,j$ entry of $M_G^m$ is the number of distinct paths of length $m$
from $i$ to $j$.  This is because a path from $i$ to $j$ of length $m$
is the concatenation of a length-$(m-1)$ path from $i$ to some $k$
followed by an edge from $k$ to $j$, so the total number of length-$m$
paths is the sum of such paths over all possible $k$; this is exactly
what is computed by the matrix multiplication $M_G^{m-1} M = M_G^m$.

However, as observed independently by O'Connor
\citep{oconnor2011shortestpaths} and Dolan
\citep{dolan2013fun}, % citet x 2
and as is standard weighted automata theory
\citep{droste2009handbook}, this can be generalized by parameterizing
the construction over an arbitrary semiring.  In particular, we may
suppose that the edges of $G$ are labeled by elements of some semiring
$R$, and form the adjacency matrix $M_G$ as before, but using the
labels on edges, and $0 \in R$ for missing edges.  The $m$th power of
$M_G$ still encodes information about length-$m$ paths, but the
interpretation depends on the specific choice of $R$ and on the edge
labeling.  Choosing the semiring $(\N,+,\cdot)$ with all edges labeled
by $1$ gives us a count of distinct paths, as before.  If we choose
$(|Bool|, \lor, \land)$ and label each edge with |True|, the $i,j$
entry of $M_G^m$ tells us whether there exists any path of length $m$
from $i$ to $j$.  Choosing $(\R, \min, +)$ and labeling edges with
costs yields the minimum cost of length-$m$ paths; choosing
$(\mathcal{P}(\Sigma^*), \cup, \cdot)$ (that is, languages over some
alphabet $\Sigma$ under union and pairwise concatenation) and labeling
edges with elements from $\Sigma$ yields sets of words corresponding
to length-$m$ paths.

Moreover, if $R$ is a star semiring, then $M_G^*$ encodes information
about paths of \emph{any} length (recall that, intuitively, $M_G^* = I
+ M_G + M_G^2 + M_G^3 + \dots$).  Choosing $R = (\R, \min, +)$ and
computing $M_G^*$ thus solves the all-pairs shortest paths problem;
$(|Bool|, \lor, \land)$ tells us whether any paths exist between each
pair of nodes; and so on.  Note that $(\N, +, \cdot)$ is not closed,
but we can make it so by adjoining $+\infty$; this corresponds to the
observation that the number of distinct paths between a pair of nodes
in a graph may be infinite if the graph contains any cycles.

Of course, DFAs can also be thought of as graphs.  Suppose we have a
DFA $D$, a semiring $R$, and a function $\Sigma \to R$ assigning an
element of $R$ to each alphabet symbol.  In this context, we call the
adjacency matrix for $D$ a \term{transition matrix}.\footnote{Textbooks
  on automata often define the \term{transition matrix} for a DFA as
  the $||Q|| \times ||\Sigma||$ matrix with its $q,s$ entry equal to
  $\delta(q,s)$.  This is just a particular representation of the
  function $\delta$, and quite uninteresting, so we co-opt the term
  \term{transition matrix} to refer to something more worthwhile.} The
graph of a DFA may not be simple, that is, there may be multiple edges
in a DFA between a given pair of nodes, each corresponding to a
different alphabet symbol.  We can handle this by summing in $R$.
That is, the transition matrix $M_D$ is the $||Q|| \times ||Q||$
matrix over $R$ whose component at $i,j$ is the sum, over all edges
from $i$ to $j$, of the $R$-values corresponding to their labels.

For example, consider the DFA in \pref{fig:dfa-example-simpl}, and the
semiring $(\N, +, \cdot)$. If we send each edge label (\ie alphabet
symbol) to $1$, we obtain the transition matrix
\[
\begin{bmatrix} 0 & 1 & 0 \\ 1 & 0 & 1
  \\ 0 & 1 & 0 \end{bmatrix}. \] The $m$th power of this matrix tells
us how many strings of length $m$ take the DFA from one given state to
another.  If we instead send each edge label to the singleton language
containing only that symbol as a length-$1$ string, as a member of the
semiring of regular languages, we obtain the transition matrix \[
\setlength{\arraycolsep}{5pt} \begin{bmatrix} \varnothing & \{a\} &
  \varnothing \\ \{b\} & \varnothing & \{a\} \\ \varnothing & \{b\} &
  \varnothing \end{bmatrix}. \] The star of this matrix yields the
complete set of strings that drives the DFA between each pair of
states.

We can now see how to interpret $\mD{X}$: it is the transition
matrix for $D$, taken over the semiring of arity-$\Sigma$
functors, where each transition $a$ is replaced by the functor
$X_a$. That is, in general, each entry of $\mD X$ will consist of a
(possibly empty) sum of functors \[ \sum_{\substack{a \in \Sigma
    \\ \delta(i,a) = j}} X_a. \] By definition, these will drive the
DFA in the proper way; moreover, sums of $X_a$ are the only functors
with the same shape as $X$.

\section{Examples}
\label{sec:examples}

%format Lij = L "_{ij}"
%format L11
%format L12
%format L21
%format L22

To make things more concrete, we can revisit some familiar examples
using our new framework. As a first example, consider the regular
expression $(aa)^*$, corresponding to the DFA shown in
\pref{fig:dfa-aa}, along with the standard polymorphic list type, $L =
1 + XL$. The matrix for $L$ can be written
\[ \m{L} =
\begin{bmatrix}
  |L11| & |L12| \\
  |L21| & |L22|
\end{bmatrix}
.
\]
\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

aaStar :: DFA (Diagram B)
aaStar = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 ^& 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "a" --> 1
  ]

dia = drawDFA aaStar # frame 0.5
  \end{diagram}
  \caption{A DFA for $(aa)^*$}
  \label{fig:dfa-aa}
\end{figure}
The punchline is that we can take the recursive equation for $L$ and
simply apply the homomorphism to both sides, resulting in the matrix
equation
\[ \m{L} = \m{1 + XL} = \m{1} + \m{X} \m{L}, \] where $\m{X}$ is the transition matrix for $D$, namely
\[ \m{X} =
\begin{bmatrix}
  |0| & X_|a| \\ X_|a| & |0|
\end{bmatrix}.
\]
Expanding out this matrix equation and performing the indicated matrix
operations yields
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
    0 & X_a \\
    X_a & 0
  \end{bmatrix}
  \begin{bmatrix}
    |L11| & |L12| \\
    |L21| & |L22|
  \end{bmatrix}
  \\
  =
  \begin{bmatrix}
    1+X_a |L21| & X_a |L22| \\
    X_a |L11| & 1+ X_a |L12|
  \end{bmatrix}.
\end{multline*}

We can see that |L11| and |L22| are isomorphic, as are |L12| and
|L21|; this is because the DFA $D$ has a nontrivial automorphism
(ignoring start and accept states).  Thinking about the meaning of
paths through the DFA, we see that |L11| is the type of lists with
even length, and |L21|, lists with odd length. More familiarly:

> data EvenList a  = EvenNil | EvenCons a (OddList a)
> data OddList a   = OddCons a (EvenList a)

As another example, consider again the recursive tree type given by $T = X
+ T^2$, along with the two-state DFA for $(ab)^*$ shown in
\pref{fig:ab-star-dfa}.  Applying the homomorphism, we obtain
\[ \m{T} = \m{X + T^2} = \m{X} + \m{T}^2, \] where
\[ \m{X} =
  \begin{bmatrix}
    0 & X_a \\ X_b & 0
  \end{bmatrix}.
\]
This yields
\begin{multline*}
  \begin{bmatrix}
    |T11| & |T12| \\
    |T21| & |T22|
  \end{bmatrix}
  =
  \begin{bmatrix}
    0 & X_a \\
    X_b & 0
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
    |T11|^2 + |T12| |T21| & X_|a| + |T11| |T12| + |T12| |T22| \\
    X_|b| + |T21| |T11| + |T22| |T21| & |T21| |T12| + |T22|^2
  \end{bmatrix}.
\end{multline*}
Equating the left- and right-hand sides elementwise yields precisely
the definitions for $T_{ij}$ we derived in Section
\ref{sec:introduction}.

As a final example, consider the type $T = X + T^2$ again, but this
time constrained by the regular expression $b^* h a^*$, with
transition matrix $\begin{bmatrix} X_b & X_h \\ 0 &
  X_a \end{bmatrix}$.  Applying the homomorphism yields
\begin{multline*}
\begin{bmatrix}
  |T11| & |T12| \\
  |T21| & |T22|
\end{bmatrix}
=
\begin{bmatrix}
  X_b & X_h \\ 0 & X_a
\end{bmatrix}
+
\begin{bmatrix}
  |T11| & |T12| \\
  |T21| & |T22|
\end{bmatrix}^2 \\
=
\begin{bmatrix}
  X_b + |T11|^2 + |T12| |T21| & X_h + |T11| |T12| + |T12| |T22| \\
  |T21| |T11| + |T22| |T21| & X_a + |T21| |T12| + |T22|^2
\end{bmatrix}.
\end{multline*}
Here something strange happens: looking at the DFA, it is plain that
there are no paths from state $2$ to state $1$, and we therefore
expect the corresponding type |T21| to be empty.  However, it does not
look empty at first sight: we have $|T21| = |T21| |T11| + |T22|
|T21|$.  In fact, it \emph{is} empty, since we are interpreting
recursively defined functors via a least fixed point semantics, and it
is not hard to see that $0$ is in fact a fixed point of the above
equation for |T21|.  In practice, we can perform a reachability
analysis for a DFA beforehand (\eg by taking the star of its
transition matrix under $(|Bool|, \lor, \land)$) to see which states
are reachable from which other states; if there is no path from $i$ to
$j$ then we know $|Tij| = 0$, which can simplify calculations.  For
example, substituting $|T21| = 0$ into the above equation and
simplifying yields
\[
\begin{bmatrix}
  |T11| & |T12| \\
  |T21| & |T22|
\end{bmatrix} \\
=
\begin{bmatrix}
  X_b + |T11|^2 & X_h + |T11| |T12| + |T12| |T22| \\
  0 & X_a + |T22|^2
\end{bmatrix}.
\]

\section{An Alternative Representation}
\label{sec:alternative}

One way to look at the examples shown so far is that we have
essentially had to \emph{duplicate} the initial functor |F|, resulting
in several slightly different copies, each with a slightly different
set of ``constructors'', in order to keep track of which constructors
are allowed at which points.  Such encodings would be extremely trying
to work with in practice, requiring much tedious case analysis.  In a
language with a sufficiently expressive type system, however, we do
not need to duplicate anything, but can instead make use of types to
dictate which constructors are allowed in which situations.

What information, exactly, do we need to keep around at the level of
types?  It is not enough to just index by a pair of DFA states; the
problem is that each constructor may correspond to \emph{multiple}
possible pairs of states.  In fact, what we need is to index by an
entire \emph{driving function}.  Given some functor $T$, the idea is
to produce just a \emph{single} $n$-ary functor $T_\chi$ indexed by a
(total!) driving function $\chi : Q \to Q$. A value of type $|T|_\chi$
is a structure with a shape allowed by |T|, whose sequence of leaf
types, taken together, drives the DFA in the way encoded by $\chi$.
The desired type can then be selected as the sum of all types indexed
by driving functions taking the start state to some accepting state.

For details of this encoding, see Yorgey
\citep{yorgey2010onaproblem}. % citet
Encoding driving functions and their composition requires only natural
numbers and lists, so they can be encoded in any language which allows
encoding these at the level of types.

The above approach requires indexing by \emph{total} driving
functions.  As pointed out by an anonymous reviewer, one can also
index by \emph{relations} which can encode partial driving functions.
For example, considering again the DFA for $b^*ha^*$ shown in
\pref{fig:bstar-h-astar}, and the tree type $T = X + T^2$, we have the
following Haskell code.  |States| encodes the states of the DFA, and
|Trans| encodes a relation on states, with each constructor
corresponding to an edge in the DFA.  The original |Tree a| type is
transformed into |Tree'|, where the |Leaf| constructor is
parameterized by a transition, and the |Fork| constructor encodes a
sum via existential quantification of |k|.  |Tree'| could also be
parameterized over an arbitrary relation of the appropriate kind,
which allows constructing |Tree| variants constrained by any DFA over
an alphabet of size $3$.
%format S1
%format S2
%format ^^ = "\;"
\begin{spec}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, PolyKinds #-}

data States = S1 | S2

data Trans b h a :: State -> State -> * ^^ where
  B  ::  b  -> Trans b h a S1 S1
  H  ::  h  -> Trans b h a S1 S2
  A  ::  a  -> Trans b h a S2 S2

data Tree' :: * -> * -> * -> State -> State -> * ^^ where
  Leaf  :: Trans b h a i j -> Tree' r b h a i j
  Fork  :: Tree' r b h a i k -> Tree' r b h a k j -> Tree' r b h a i j
\end{spec}

\section{Derivatives, Again}
\label{sec:derivatives-again}
Now that we have seen the general framework, let's return to the
specific application of computing \emph{derivatives} of data types.
In order to compute a derivative, we need the DFA for the regular
expression $a^*ha^*$, shown in~\pref{fig:DFA-deriv}.
\begin{figure}
  \centering
  \begin{diagram}[width=100]
import TypeMatricesDiagrams

deriv :: DFA (Diagram B)
deriv = dfa
  [ 1 --> (False, origin)
  , 2 --> (True , 5 ^& 0)
  ]
  [ 1 >-- txt "a" --> 1
  , 1 >-- txt "h" --> 2
  , 2 >-- txt "a" --> 2
  ]

dia = drawDFA deriv # frame 0.5
  \end{diagram}
  \caption{A DFA for derivatives}
  \label{fig:DFA-deriv}
\end{figure}
The corresponding transition matrix is
\[ \m{X} =
\begin{bmatrix}
  X_a & X_h \\
  0 & X_a
\end{bmatrix}.
\]

Suppose we start with a functor defined as a product:
\[ F = G H \]
Expanding via the homomorphism to matrices of bifunctors, we obtain
\[
\begin{bmatrix}
  F_{11} & F_{12} \\
  0 & F_{22}
\end{bmatrix}
=
\begin{bmatrix}
  G_{11} & G_{12} \\
  0 & G_{22}
\end{bmatrix}
\begin{bmatrix}
  H_{11} & H_{12} \\
  0 & H_{22}
\end{bmatrix}
\]
(the occurrences of $0$ correspond to the observation that there are
no paths in the DFA from state $2$ to state $1$).  Let's consider each
of the nonzero $F_{ij}$ in turn.  First, we have
\[
F_{11} = G_{11} \times H_{11}
\]
$F_{11}$ is simply the type of structures whose leaves take the DFA
from state $1$ to itself and so whose leaves match the regular
expression $a^*$; hence we have $F_{11}\ a\ h \cong F\ a$ (and
similarly for $G_{11}$, $H_{11}$, $F_{22}$, $G_{22}$, and $H_{22}$).
We also have
\[
F_{12} = G_{11} H_{12}+G_{12} H_{22} \cong G H_{12} + G_{12} H.
\]
This looks suspiciously like the usual Leibniz law for the derivative
of a product (\ie the ``product rule'' for differentiation). We also
know that
\[
1_{12} = 0
\]
and
\[
X_{12} = X_h,
\]
and if $F = G + H$ then $F_{12} = G_{12} + H_{12}$.  If we substitute
the unit type for |h|, these are precisely the rules for
differentiating polynomials. So $F_{12}$ is the derivative of $F$.

There is another way to look at this. Write
\[
\m{X} =
\begin{bmatrix}
  X_a & X_h \\ 0 & X_a
\end{bmatrix}
=
X_a I + d
\]
where
\[ d =
\begin{bmatrix}
  |0| & X_h \\
  |0| & |0|
\end{bmatrix}
\]
Note that $d^2 = 0$.  Note also that \[ (X_a I) d =
\begin{bmatrix}
  0 & X_a X_h \\ 0 & 0
\end{bmatrix}
\] and \[ d (X_a I) =
\begin{bmatrix}
  0 & X_h X_a \\ 0 & 0
\end{bmatrix}.
\]
Treating the product of functors as
commutative is problematic in our setting, since we care about the
precise sequence of leaf types.  However, in this particular instance,
we can specify that $X_h$ commutes with everything, which corresponds
to letting the ``hole'' of type |h| ``float'' to the
outside---typically, when constructing a zipper structure, one does
this anyway, storing the focused element separately from the rest of
the structure.  Under this interpretation, then, $(X_a I)$ and $d$
commute even though matrix multiplication is not commutative in
general.  We then note that \[ (X_a I + d)^n = (X_a I)^n + n (X_a
I)^{n-1} d, \] making use of this special commutativity and the fact
that $d^2 = 0$, annihilating all the subsequent terms.  We can
linearly extend this to an entire polynomial $f$, that is,
\begin{align*}
f(\m{X}) &= f(X_a I + d)\\
&= f(X_a I) + f'(X_a I) d\\
&= \begin{bmatrix}
  f(X_a) & 0 \\
  0 & f(X_a)
\end{bmatrix}
+\begin{bmatrix}
  0 & f'(X_a) X_h \\
  0 & 0
\end{bmatrix}
\end{align*}
The matrix $d$ is thus playing a role similar to an ``infinitesimal''
in calculus, where the expression $dx$ is manipulated informally as if
$(dx)^2=0$.  (Compare with the dual numbers described by
\cite{DBLP:journals/lisp/SiskindP08}.)

\section{Dissection and Divided Differences}
\label{sec:divided-differences}

Consider again the regular expression $b^*ha^*$.  Data structures with
leaf sequences matching this pattern have a ``hole'' of type |h|, with
values of type $b$ to the left of the hole and values of type $a$ to
the right (\pref{fig:divided-tree}).\footnote{Typically we substitute
  the unit type for |h|, but it makes the theory work more smoothly if
  we represent it initially with a unique type variable.}

\todo{make sure this gets the right figure!}
\begin{figure}
  \centering
\begin{diagram}[width=150]
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import TypeMatricesDiagrams

t = nd
    [ nd
      [ nd $
          leaves [B, B]
      , lf B
      ]
    , nd
      [ nd
        [ lf H
        , nd $ leaves [A, A]
        ]
      , nd $ leaves [A, A]
      ]
    ]
  where nd     = Node Nothing
        lf x   = Node (Just x) []
        leaves = map lf

dia = renderT t # frame 0.5
\end{diagram}
%$
  \caption{A tree with leaf sequence matching $b^*ha^*$}
  \label{fig:divided-tree}
\end{figure}

\subsection{Dissection}
\label{sec:dissection}

Such structures have been considered by McBride
\citep{mcbride-dissection}, % citet
who refers to them as \term{dissections} and shows how they can be used,
for example, to generically derive tail-recursive maps and folds.

Given a functor $F$, McBride uses $\dissect F$ to denote the bifunctor
which is the dissection of $F$ (where the unit type has been
substituted for $h$).  We have \[ \dissect X\ b\ a = 1, \] since a
dissected $X$ consists merely of a hole, \[ \dissect 1\ b\ a = 0, \]
and \[ \dissect (F + G)\ b\ a = \dissect F\ b\ a + \dissect G\ b\
a. \] The central construction is the Leibniz rule for dissection of a
product, \[ \dissect (F \times G) = \clowns F \times \dissect G +
\dissect F \times \jokers G, \] where $(\clowns F)\ b\ a = F\ b$ and
$(\jokers F)\ b\ a = F\ a$.  That is, a dissection of an $(F \times
G)$-structure consists either of an $F$-structure containing only
elements of the first type paired with a $G$-dissection, or an
$F$-dissection paired with a $G$-structure containing only elements of
the second type.

As a simple example, consider the polynomial functor $L = 1 + XL$ of
finite lists.  Intuitively, the dissection of a list should consist of
a list of |b|'s, followed by a hole, and then a list of |a|'s, that
is, \[ \dissect L\ b\ a \cong L\ b \times L\ a. \] Applying the rules
above, we can derive
\begin{align*}
  \dissect L\ b\ a &= \dissect (1 + XL)\ b\ a \\
  &= (0 + \clowns X \times \dissect L + \dissect X \times \jokers L)\
  b\ a \\
  &= b \times (\dissect L\ b\ a) + L\ a
\end{align*}
and thus $\dissect L\ b\ a \cong L\ b \times L\ a$ as expected.

\subsection{Dissection via Matrices}
\label{sec:dissection-via-matrices}

The DFA recognizing $b^*ha^*$ is illustrated in
\pref{fig:bstar-h-astar}, and has transition matrix
\[ \begin{bmatrix} X_b & X_h \\ 0 & X_a \end{bmatrix}. \] There are clearly
no leaf sequences taking this DFA from state $2$ to state $1$; leaf
sequences matching $b^*$ or $a^*$ keep the
DFA in state $1$ or state $2$, respectively; and leaf sequences
matching $b^*ha^*$ take the DFA from state $1$ to state $2$.  That is,
under the homomorphism induced by this DFA, the functor $F$ maps to
the matrix of bifunctors \[ \begin{bmatrix} \clowns F & \dissect F
  \\ 0 & \jokers F \end{bmatrix}. \] Taking the product of two such
matrices indeed yields
\begingroup
\setlength{\arraycolsep}{5pt}
\[ \begin{bmatrix} \clowns F & \dissect F
  \\ 0 & \jokers F \end{bmatrix} \begin{bmatrix} \clowns G & \dissect
  G \\ 0 & \jokers G \end{bmatrix} = \begin{bmatrix} \clowns F \times
  \clowns G & \clowns F \times \dissect G + \dissect F \times \jokers G
  \\ 0 & \jokers F \times \jokers G \end{bmatrix}, \]
\endgroup
as expected.

\subsection{Divided Differences}
\label{sec:divided-diff}

Just as differentiation of types has an analytic analogue, dissection
has an analogue as well, known as \term{divided difference}.  Let $f :
\R \to \R$ be a real-valued function, and let $b,a \in \R$.  Then the
\term{divided difference} of $f$ at $b$ and $a$, notated\footnote{Our
  notation is actually ``backwards'' with respect to the usual
  notation---what we write as $f_{b,a}$ is often written $f[a,b]$ or
  $[a,b]f$---in order to better align with the combinatorial intuition
  discussed later.} $f_{b,a}$, is defined by
\[ f_{b,a} = \frac{f_b - f_a}{b - a}, \] where for consistency of notation
we write $f_b$ for $f(b)$, and likewise for $f_a$.  In the limit, as
$a \to b$, this yields the usual derivative of $f$.

We now consider the type-theoretic analogue of $f_{b,a}$.  We cannot
directly interpret subtraction and division of functors.  However, if
we multiply both sides by $(b - a)$ and rearrange a bit, we can derive
an equivalent relationship expressed in terms of only addition and
multiplication, namely,
\[ f_a + f_{b,a} \times b = a \times f_{b,a} + f_b. \]  This
equation corresponds exactly to the isomorphism witnessed by McBride's
function |right|,
\[ |right : F a + (| \dissect |F b a, b) -> (a,| \dissect |F b a) + F
b| \] We can now explain why the letters |b| and |a| are
``backwards''.  Intuitively, we can think of a dissection as a
``snapshot'' of a data structure in the midst of a traversal; values
of type |a| are ``unprocessed'' and values of type |b| are
``processed''.  The ``current position'' moves from left to right
through the structure, turning |a| values into |b| values.  This is
exactly what is accomplished by |right|: given a structure full of
unprocessed |a| values, or a dissected |F| with a focused |b| value,
it moves the focus right by one step, either focusing on the first
unprocessed |a|, or yielding a structure full of |b|s in the case that
all the values have been processed.

\subsection{Higher-Order Divided Differences}
\label{sec:higher-order-div-diff}

Higher-order divided differences, corresponding to higher derivatives,
are defined by the recurrence
\begin{equation} \label{eq:div-diff-rec}
f_{x_n \dots x_0} = \frac{f_{x_n
    \dots x_1} - f_{x_{n-1} \dots x_0}}{x_n - x_0}.
\end{equation}
Alternatively,
the higher-order divided differences of a function $f$ can be arranged
in a matrix, as, for example,
\begin{equation} \label{eq:div-diff-mat}
\dissect_{cba} f =
\begin{bmatrix}
f_c & f_{c,b} & f_{c,b,a} \\
0   & f_b    & f_{b,a}   \\
0   & 0      & f_a
\end{bmatrix}
\end{equation}
in such a way as to be a semiring homomorphism, that is,
$\dissect_{cba}(f + g) = \dissect_{cba} f + \dissect_{cba} g$ and
$\dissect_{cba} (fg) = \dissect_{cba} f \dissect_{cba} g$, and so on.
Proving that this yields a definition equivalent to the recurrence
\eqref{eq:div-diff-rec} boils down to showing that if $f = gh$ then
\begin{equation} \label{eq:div-diff-prod}
f_{x_n \dots x_0} = \sum_{j=0}^n g_{x_n \dots x_j} h_{x_j \dots
  x_0}.
\end{equation}
Proving \eqref{eq:div-diff-prod} is not entirely straightforward; in
fact, we conjecture that the computational content of the proof, in
the $n=2$ case, essentially consists of (the interesting part of) the
implementation of the isomorphism |right|.

\todo{make sure this gets the right figure!}
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import TypeMatricesDiagrams

deriv :: DFA (Diagram B)
deriv = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 ^& 0)
  , 3 --> (True , 10 ^& 0)
  ]
  [ 1 >-- txt "c" --> 1
  , 1 >-- txt "h" --> 2
  , 2 >-- txt "b" --> 2
  , 2 >-- txt "h" --> 3
  , 3 >-- txt "a" --> 3
  ]

dia = drawDFA deriv # frame 0.5
  \end{diagram}
  \caption{A DFA for higher-order divided difference}
  \label{fig:DFA-ho-divdiff}
\end{figure}

If we now consider the DFA $D$ in \pref{fig:DFA-ho-divdiff}, we can
see that \eqref{eq:div-diff-mat} corresponds to the matrix $\mD{F}$.
More generally, a DFA consisting of a sequence of $n$ states with
self-loops chained together by |h| transitions will have a
transition matrix corresponding to an order-$n$ matrix of divided
differences.  In general, $F_{ij}$ will consist of $j-i$ holes
interspersed among sequences of consecutive alphabet elements.

By analogy with the binary dissection case, we would expect
\eqref{eq:div-diff-rec} to yield an isomorphism with type \[
\dissect_{x_{n-1} \dots x_0} F + (\dissect_{x_n \dots x_0}, x_n) \to
(x_0, \dissect_{x_n \dots x_0} F) + \dissect_{x_n \dots x_1} F. \] We
have not yet been able to fully make sense of this, but hope to
understand it better in the future.  In particular, our intuition is
that this will yield a tail-recursive implementation of a structure
being processed by multiple coroutines.

\section{Discussion and Future Work}

This paper arose out of several blog posts by both authors
\cite{piponi2009finite}\cite{piponi2010tomography}\cite{piponi2010regular}\cite{yorgey2010onaproblem},
although the content of this paper is neither a strict subset nor
superset of the content of the blog posts.  There is much remaining to
be explored, in particular understanding the isomorphisms induced by
higher-order divided differences, and generalizing this framework to
$n$-ary functors and partial differentiation.  It seems likely that
$q$-derivatives can also fruitfully be seen in a similar light
\citep{stay2014q}.

There are several more practical aspects to this work that remain to
be explored.  At a fundamental level, there would be some interesting
engineering work involved in turning this into a practical library.
One might also wonder to what extent it is possible to take
\emph{operations} on some polynomial functor $T$ and automatically
lift them into operations on a constrained version of $T$.  At the
very least this would require checking that the operation actually
preserves the given constraints.

Some of the ideas in this paper are implicitly present in earlier
work; we note in particular Duchon \etal
\cite[p. 590]{duchon2004boltzmann}, % citet
who mention generating Boltzmann samplers for strings corresponding to
regular expressions, also via their DFAs.  It would be interesting to
explore the relationship in more detail. \bigskip

\noindent \textbf{Acknowledgements.} This work was partially supported by the
National Science Foundation, under NSF 1218002, CCF-SHF Small:
\emph{Beyond Algebraic Data Types: Combinatorial Species and
  Mathematically-Structured Programming}.

Our sincere thanks to the anonymous reviewers, who had many helpful
suggestions.  Thanks also to Lukas Mai for pointing out some errors in
a draft.

%% \printbibliography
\bibliographystyle{plain}
\bibliography{type-matrices}

\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Text that we might want to do something with eventually


%% One point worth mentioning is that \todo{Write about uniqueness of
%%   representation, see stuff in comments}

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

%% \todo{We need a better story about finite vs. infinite.  The above
%%   gives the standard presentation of DFAs for finite strings, but
%%   Haskell types can include infinite values.  So we want to do
%%   something like use the \emph{greatest} fixed point of $\Sigma^* =
%%   \varepsilon \union \Sigma \Sigma^*$ and say that an infinite string
%%   is in the language recognized by a DFA if it never causes the DFA to
%%   reject.  I'm not quite sure how this relates to the fact that
%%   least+greatest fixedpoints coincide in Haskell.}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Consider now the DFA for the regular expression $a^*1b^*$.
%% The corresponding diagram is
%% \dan{Diagram}
%% \[ \m{T} =
%% \begin{bmatrix}
%%   |a| & |1| \\
%%   |0| & |b|
%% \end{bmatrix}
%% \]
%% Just as when we considered derivatives, suppose a functor \dan{?} is a
%% product of two functors
%% \[
%% F = G \times H.
%% \]
%% Then
%% \[
%% F_{11} = G_{11}\times H_{11}+G_{12}\times H_{21}
%% \]
%% As before, $H_{21}$ contains sequences of leaves which take the DFA
%% from state $2$ to state $1$; but there are no such strings. So $H_{21}$ is the uninhabited type $0$.
%% So $F_{11} = G_{11}\times H_{11}$.
%% As before, $F_{11}$ is structures whose leaves take the DFA from state $1$ to itself and so whose
%% leaves match the regular expression $a^*$.
%% So we have simply that $F_{11}(a,b) = F(a)$.
%% However, we now have that $F_{22}(a,b) = F(b)$.
%% We also have
%% \[
%% F_{12} = G_{11}\times H_{12}+G_{12}\times H_{22}
%% \]
%% So
%% \[
%% F_{12}(a,b) = G(a)\times H_{12}(a,b)+G_{12}(a,b)\times H(b)
%% \]
%% This is the modified Leibniz rule described in \cite{mcbride-dissection}.
%% \dan{Do other operations}
%% We have already argued above in \pref{sec:zippers-and-dissections}
%% that the regular expression $a^*1b^*$
%% gives rise to dissections. We have now also shown how the algebraic rules for
%% dissections are actually statements about the transition matrices for the
%% corresponding DFA.

%% There is a more familiar interpretation of the dissection operation.
%% Given a function of a single real variable $f$,
%% the divided difference is the function of two variables mapping $x_0$, $x_1$ to $(f(x_0)-f(x_1)/(x_0-x_1))$ which is sometimes also written as $[x_0, x_1]f$.
%% \begin{multline*}
%% [x_0,x_1](fg) = (f(x_0)g(x_0)-f(x_1)g(x_1))/(x_0-x_1)\\
%% = (f(x_0)g(x_0)-f(x_0)g(x_1)+f(x_0)g(x_1)-f(x_1)g(x_1))/(x_0-x_1)\\
%% = f(x_0)[x_0,x_1]g+[x_0,x_1]fg(x_1)
%% \end{multline*}
%% This is McBride's modified Leibniz rule.
%% For polynomial types, dissection is the divided difference.
%% There is an important caveat: in the usual context of numerical
%% methods, divided differences are usually defined using
%% subtraction. Subtraction isn't meaningful for types.
%% But the Leibniz law above shows that for polynomials divided differences
%% could have been defined without making reference to subtraction and that
%% this definition carries over to types.
%% Notice how in the limit as $x_1\rightarrow x_0$ we recover the derivative.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Consider constructing a type of binary trees with data of two
%% different types, $a$ and $b$, at internal nodes---but with the
%% restriction that two values of type $a$ may never occur consecutively
%% in an inorder traversal.  This restriction corresponds to the DFA
%% shown in \pref{fig:DFA-no-consec-a}, with the transition matrix
%% \[ \m{X} =
%% \begin{bmatrix}
%%   X_|b| & X_|a| \\
%%   X_|b| & 0
%% \end{bmatrix}.
%% \]
%% \begin{figure}
%%   \centering
%%   \begin{diagram}[width=100]
%% import TypeMatricesDiagrams

%% noAA :: DFA (Diagram B)
%% noAA = dfa
%%   [ 1 --> (True, origin)
%%   , 2 --> (True, 5 ^& 0)
%%   ]
%%   [ 1 >-- txt "b" --> 1
%%   , 1 >-- txt "a" --> 2
%%   , 2 >-- txt "b" --> 1
%%   ]

%% dia = drawDFA noAA # frame 0.5
%%   \end{diagram}
%%   \caption{A DFA for avoiding consecutive $a$'s}
%%   \label{fig:DFA-no-consec-a}
%% \end{figure}

%% Beginning with $T = 1 + TXT$ and applying the homomorphism, we obtain
%% \[
%%   \begin{bmatrix}
%%     |T11| & |T12| \\
%%     |T21| & |T22|
%%   \end{bmatrix}
%%   =
%%   \begin{bmatrix}
%%     1 & 0 \\
%%     0 & 1
%%   \end{bmatrix}
%%   +
%%   \begin{bmatrix}
%%     |T11| & |T12| \\
%%     |T21| & |T22|
%%   \end{bmatrix}
%%   \begin{bmatrix}
%%     X_b & X_a \\
%%     X_b & 0
%%   \end{bmatrix}
%%   \begin{bmatrix}
%%     |T11| & |T12| \\
%%     |T21| & |T22|.
%%   \end{bmatrix}
%% \]
%% Expanding the right-hand side and equating elementwise yields
%% \begin{align*}
%%   |T11| &= 1 + (|T11| + |T12|)b|T11| + |T11|a|T21| \\
%%   |T12| &=     (|T11| + |T12|)b|T12| + |T11|a|T22| \\
%%   |T21| &=     (|T21| + |T22|)b|T11| + |T21|a|T21| \\
%%   |T22| &= 1 + (|T21| + |T22|)b|T12| + |T21|a|T22|,
%% \end{align*}
%% or in Haskell notation,

%% %format Empty11
%% %format B11
%% %format A11
%% %format B12
%% %format A12
%% %format B21
%% %format A21
%% %format Empty22
%% %format B22
%% %format A22

%% > data T11 a b
%% >   =  Empty11
%% >   |  B11 (Either (T11 a b) (T12 a b)) b (T11 a b)
%% >   |  A11 (T11 a b) a (T21 a b)
%% >
%% > data T12 a b
%% >   =  B12 (Either (T11 a b) (T12 a b)) b (T12 a b)
%% >   |  A12 (T11 a b) a (T22 a b)
%% >
%% > data T21 a b
%% >   =  B21 (Either (T21 a b) (T22 a b)) b (T11 a b)
%% >   |  A21 (T21 a b) a (T21 a b)
%% >
%% > data T22 a b
%% >   =  Empty22
%% >   |  B22 (Either (T21 a b) (T22 a b)) b (T12 a b)
%% >   |  A22 (T21 a b) a (T22 a b)

%% (We could also equivalently distribute out products such as $(|T11| +
%% |T12|)b|T11| = |T11| b |T11| + |T12| b |T11|$ and end up with more
%% constructors for each data type.) Since both states in the DFA are
%% accept states, we are actually looking for the sum type

%% > type T' a b = Either (T11 a b) (T12 a b)
