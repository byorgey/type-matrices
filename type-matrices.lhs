% -*- LaTeX -*-
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

\begin{itemize}
\item Problem statement: how to constrain the leaves of a type to
  conform to a regular expression?

\item Maybe show an ad-hoc solution to a special case, to give a
  better sense of the problem.

I'm listing some elementary examples. We don't have to use all of them.

Ordinary lists:

> data List a = Nil | Cons a (List a)

Lists with alternating elements:

> data AList a b = ANil | ACons a (BList a b)
> data BList a b = BCons b (AList a b)

An |AList| corresponds to a regexp like $(AB)^*$.

Then trees:

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
%format Fork21'=\VarID{Fork'_{21}}
%format Fork22=\VarID{Fork_{22}}
%format Fork22'=\VarID{Fork'_{22}}

%format Leaf11=\VarID{Leaf_{11}}
%format Leaf12=\VarID{Leaf_{12}}
%format Leaf21=\VarID{Leaf_{21}}
%format Leaf22=\VarID{Leaf_{22}}

Maybe nobody wants to see this:

> data Tree a =  Leaf a | Fork (Tree a) (Tree a)
>                 deriving Show

> data Tree11 a b  =  Fork11  (Tree11 a b)  (Tree11 a b)
>                  |  Fork11' (Tree12 a b)  (Tree21 a b)
>                     deriving Show
> data Tree12 a b  = Leaf12 a
>                  |  Fork12  (Tree11 a b)  (Tree12 a b)
>                  |  Fork12' (Tree12 a b)  (Tree22 a b)
>                    deriving Show
> data Tree21 a b  = Leaf21 b
>                  |  Fork21  (Tree21 a b)  (Tree11 a b)
>                  |  Fork21' (Tree22 a b)  (Tree21 a b)
>                     deriving Show
> data Tree22 a b  =  Fork22  (Tree21 a b)  (Tree21 a b)
>                  |  Fork22' (Tree22 a b)  (Tree21 a b)
>                     deriving Show

> ex1 = Fork11' (Leaf12 1) (Leaf21 "a")
> ex2 = Fork11' (Fork12 ex1 (Leaf12 1)) (Leaf21 "b")

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

\end{itemize}

\section{Zippers and dissections}
\label{sec:zippers-and-dissections}


\begin{itemize}
\item To lend more weight to the problem, show that
  zippers/derivatives, dissection, and infinitesimals are special
  cases (or possibly only some of these).
\end{itemize}

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

% \bibliographystyle{abbrvnat}

\end{document}
