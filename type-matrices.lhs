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
           {dpiponi@gmail.com}
\authorinfo{Brent Yorgey}
           {University of Pennsylvania}
           {byorgey@cis.upenn.edu}

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

%    ---A->--
%   /        \
% (1)        (2)
%   \        /
%    --<-B---

%format Tree11=\VarID{Tree_{11}}
%format Tree12=\VarID{Tree_{12}}
%format Tree21=\VarID{Tree_{21}}
%format Tree22=\VarID{Tree_{22}}

%format Fork11=\VarID{Fork_{11}}
%format Fork11'=\VarID{Fork'_{11}}
%format Fork12=\VarID{Fork_{12}}
%format Fork12'=\VarID{Fork'_{12}}
%format Fork21=\VarID{Fork_{21}}
%format Fork21'=\VarID{Fork'_{21}}
%format Fork22=\VarID{Fork_{22}}
%format Fork22'=\VarID{Fork'_{22}}

%format Leaf11=\VarID{Leaf_{11}}
%format Leaf12=\VarID{Leaf_{12}}
%format Leaf21=\VarID{Leaf_{21}}
%format Leaf22=\VarID{Leaf_{22}}

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

\section{Matrices of types}
\label{sec:matrices-of-types}

\begin{itemize}
\item Work up to the full solution involving matrices of types.
  Matrices!  Of types!
\end{itemize}

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

\bibliographystyle{abbrvnat}

\end{document}
