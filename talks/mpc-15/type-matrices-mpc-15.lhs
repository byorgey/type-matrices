%% -*- mode: LaTeX; compile-command: "cabal exec runhaskell Shake.hs" -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

%include polycode.fmt

%format Dissect = "\dissect"
%format <->     = "\cong"
%format *       = "\times"

\usepackage[all]{xy}
\usepackage{brent}
\usepackage{xspace}
\usepackage[backend=pgf,extension=pgf,input,outputdir=diagrams]{diagrams-latex}
\graphicspath{{images/}{../../symbols/}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Math typesetting

%% a bit more space for matrices
\setlength{\arraycolsep}{5pt}

% regular expression alternation/choice operator
\newcommand{\realt}{+}

\newcommand{\sem}[1]{\ensuremath{\left\llbracket #1 \right\rrbracket}}

% \newcommand{\m}[1]{\mathbf{#1}}
\newcommand{\m}[1]{\left[ {#1} \right]}
\newcommand{\mD}[1]{\m{#1}_D}

\newcommand{\dissect}{\includegraphics{Dissect}}
\newcommand{\clowns}{\includegraphics{Clowns}}
\newcommand{\jokers}{\includegraphics{Jokers}}

\newcommand{\Type}{\ensuremath{\mathbf{Type}}}

\newcommand{\sprod}{\bullet}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\etc}{\textit{etc.}}
\renewcommand{\eg}{\textit{e.g.}\xspace}
\renewcommand{\ie}{\textit{i.e.}\xspace}

\newcommand{\theschool}{Mathematics of Program Construction}
\newcommand{\thelocation}{K\"onigswinter, Germany}
\newcommand{\thedate}{29 June 2015}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\setbeamertemplate{items}[circle]

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  % XX remove this before giving actual talk!
  % \setbeamertemplate{footline}[frame number]
  % {%
  %   \begin{beamercolorbox}{section in head/foot}
  %     \vskip2pt
  %     \hfill \insertframenumber
  %     \vskip2pt
  %   \end{beamercolorbox}
  % }

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}

      \begin{center}
%        \includegraphics[width=2in]{\sectionimg}
%        \bigskip

        {\Huge \insertsectionhead}
      \end{center}
    \end{frame}
  }
}

\defbeamertemplate*{title page}{customized}[1][]
{
  \vbox{}
  \vfill
  \begin{centering}
    \begin{beamercolorbox}[sep=8pt,center,#1]{title}
      \usebeamerfont{title}\inserttitle\par%
      \ifx\insertsubtitle\@@empty%
      \else%
        \vskip0.25em%
        {\usebeamerfont{subtitle}\usebeamercolor[fg]{subtitle}\insertsubtitle\par}%
      \fi%
    \end{beamercolorbox}%
    \vskip1em\par
    {\usebeamercolor[fg]{titlegraphic}\inserttitlegraphic\par}
    \vskip1em\par
    \begin{beamercolorbox}[sep=8pt,center,#1]{author}
      \usebeamerfont{author}\insertauthor
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{institute}
      \usebeamerfont{institute}\insertinstitute
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{date}
      \usebeamerfont{date}\insertdate
    \end{beamercolorbox}
  \end{centering}
  \vfill
}

\newenvironment{xframe}[1][]
  {\begin{frame}[fragile,environment=xframe,#1]}
  {\end{frame}}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show only notes}

\renewcommand{\emph}{\textbf}

\title{Polynomial Functors Constrained by Regular Expressions}
\date{\theschool \\ \thelocation \\ \thedate}
\author{Dan Piponi \and \usebeamercolor[fg]{title}{Brent Yorgey}}
\titlegraphic{\includegraphics[width=1in]{deriv-tree}}

% Abstract
%
% Algebraic data types are central to typed functional programming,
% sitting at a happy intersection of theory and practice.  I will
% define and give examples of algebraic data types, and then go on to
% explain what is meant by the derivative of an algebraic data type.
% In the second part of the talk I will show how to constrain
% algebraic data types by a given regular expression, including
% finding derivatives a special case. No particular background is
% assumed; my goal is to convey not a particular result per se, but
% rather an appreciation for some of the beautiful overlap between
% algebra, combinatorics, calculus, and computer science.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{xframe}{}
   \titlepage
\end{xframe}

% \begin{xframe}
%   \begin{center}
%     Joint work with Dan Piponi \bigskip

%     \includegraphics[width=3in]{dan} \\
%   \end{center}
% \end{xframe}

\section{Introduction \& Motivation}
\label{sec:intro}

\begin{xframe}{What this talk is about}
  \begin{center}
    \begin{diagram}[width=150]
      dia = mconcat
        [ atPoints (triangle 20)
          $ map text    -- $
            [ "polynomial functors"
            , "linear algebra"
            , "regular expressions" ]
        , triangle 20
          # explodePath
          # concat
          # map (strokeLocTrail . doAdjust)
          # mconcat
        , text "semirings"
        ]
        where
          doAdjust locTr = adjust locTr opts
            where
              opts = with & adjMethod .~ ByAbsolute adjLen
                          & adjSide .~ Both
              adjLen || angleBetweenDirs
                          xDir
                          (direction (tangentAtStart locTr))
                        < (1/20 @@@@ turn)
                        = -15
                     || otherwise = -5
    \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}{Motivation}
  \begin{center}
    Recall that ``the \emph{derivative} of a type is its type of
    one-hole contexts'' (Huet, McBride, Joyal, \etc).
  \end{center}

  \begin{center}
    \begin{diagram}[width=200]
      import Diagrams
      tree1 = drawTree (trees !! 3) # frame 0.5
      tree2 = drawNTree (poke 3 (trees !! 3)) # frame 0.5
      dia = hsep 2 $ -- $
        map centerY
        [ tree1, strutX 0.5, text "$\\in T(\\N)$" # scale 1.5
        , strutX 5
        , tree2, strutX 0.5, text "$\\in \\partial T(\\N)$" # scale 1.5
        ]
    \end{diagram}
  \end{center}
  \begin{center}
    Application: \emph{zippers}
  \end{center}
\end{xframe}

\begin{xframe}{Motivation}
  \begin{center}
    Recall also \emph{dissection} (McBride, \textit{Clowns \& Jokers}).
  \end{center}

  \begin{center}
    \begin{diagram}[width=250]
      import Diagrams
      import           Diagrams.TwoD.Layout.Tree
      import Data.Char

      tree1 = drawTree (trees !! 3) # frame 0.5
      tree2 = drawNCTree (poke 4 (trees !! 3)) # frame 0.5
      dia = hsep 2 $ -- $
        map centerY
        [ tree1, strutX 0.5, text "$\\in T(\\N)$" # scale 1.5
        , strutX 5
        , tree2, strutX 0.2, text "$\\in$" # scale 1.5, dissect # scale 1.7
        , strutX 0.5, text "$T(\\N,C)$" # scale 1.5
        ]
      ht = 1.2
      dissect = triangle 1 # scaleToY ht # alignB <> vrule ht # alignB

      drawNCTree =
        maybe mempty (renderTree (nodeType nil node' hole) (~~))
        . symmLayoutBin' (with & slVSep .~ 3 & slHSep .~ 3)
      node' x = ((<> circle 1 # fc lightblue) . text) $ elt'
        where elt' || x < 10 = showElt (chr (ord 'a' + x))
                   || otherwise = showElt x
    \end{diagram}
  \end{center}

%   \begin{center}
% \begin{diagram}[width=150]
% import Diagrams.TwoD.Layout.Tree
% import Data.Tree
% import TypeMatricesDiagrams

% t = nd
%     [ nd
%       [ nd $
%           leaves [6, 7]
%       , lf 4
%       ]
%     , nd
%       [ nd
%         [ lf 12
%         , nd $ leaves [3, 5]
%         ]
%       , nd $ leaves [1, 6]
%       ]
%     ]
%   where nd     = Node Nothing
%         lf x   = Node (Just x) []
%         leaves = map lf

% dia = renderT t # frame 0.5
% \end{diagram}
% %$
%   \end{center}

  \begin{center}
    Application: tail-recursive traversals (maps and folds)
  \end{center}
\end{xframe}

\begin{xframe}{Motivation}

Questions:

\begin{itemize}
\item How are these related?
\item Where does the definition of dissection come from?
\item Where does |right| come from?
\end{itemize}

\begin{spec}
  right :: F A + (Dissect F B A * B) <-> (A * Dissect F B A) + F B
\end{spec}

%% XXX if time: make some pictures?

\end{xframe}

\section{Preliminaries}
\label{sec:prelim}

% \begin{xframe}{Polynomial functors}

%   \begin{center}
%   \[ F : \Set \to \Set \]
%   elements $\to$ structures \bigskip

% \begin{diagram}[width=200]
% import           Data.List.Split
% import           Diagrams

% elts = map node [1,2,3,4::Int]
% eltSet = atop (roundedRect 6 6 0.5)
%        . centerXY
%        . vsep 1 . map (hsep 1)
%        . chunksOf 2
%        $ elts    -- $

% dia = [eltSet, arrowV (5 ^& 0), lsD] # map centerY # hsep 2 # frame 0.5
% \end{diagram}
% \bigskip

% \onslide<2> aka \emph{algebraic data types}
%   % think: \emph{(parameterized) combinatorial families}
%   \end{center}
% \end{xframe}

\begin{xframe}{Polynomial functors}
  Polynomial functors are those functors $F : \Set \to \Set$ (or
  $\Type \to \Type$) inductively built from:
  \begin{align*}
    0(A) &= \varnothing \\
    1(A) &= \{\star\} \\
    X(A) &= A \\
    (F + G)(A) &= F(A) \uplus G(A) \\
    (F \cdot G)(A) &= F(A) \times G(A)
  \end{align*}

  \onslide<2-> Can easily generalize to multivariate polynomial
  functors \[ F : \Set^n \to \Set. \] $X$ generalizes to family of
  projections $X_j(A_1,\dots,A_n) = A_j$.
\end{xframe}

\begin{xframe}{Implicit/recursive definition}
  We also allow mutually recursive definitions:
  \begin{align*}
    F_1 &= \Phi_1(F_1, \dots, F_n) \\
    &\vdots \\
    F_n &= \Phi_n(F_1, \dots, F_n)
  \end{align*}
  interpreted as a least fixed point.
\end{xframe}

\begin{xframe}{Regular expressions}
  Regular expressions are a language of ``patterns'' for strings in
  $\Sigma^*$ (finite sequences of elements from ``alphabet'' $\Sigma$)

  \begin{align*}
    R &::= \varnothing && \text{never matches} \\
    &\mid \varepsilon && \text{empty string} \\
    &\mid a \in \Sigma && \text{``a''} \\
    &\mid R_1 \realt R_2 && \text{$R_1$ or $R_2$} \\
    &\mid R_1R_2 && \text{$R_1$ followed by $R_2$} \\
    &\mid R^* && \text{sequence of zero or more $R$}
  \end{align*}
\end{xframe}

\begin{xframe}{DFAs}
  \begin{center}
    \textbf{D}eterministic \textbf{F}inite \textbf{A}utomata \bigskip

  \begin{diagram}[width=150]
import TypeMatricesDiagrams

exampleDFA :: DFA (Diagram B, Bool)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 ^& 0)
  , 3 --> (True,  10 ^& 0)
  , 4 --> (False, 5 ^& (-5))
  ]
  [ 1 >-- txtN "A" --> 2
  , 2 >-- txtN "B" --> 1

  , 2 >-- txtN "A" --> 3
  , 3 >-- txtN "B" --> 2

  , 1 >-- (txt "B", True) --> 4
  , 3 >-- txtN "A" --> 4

  , 4 >-- txtN "A,B" --> 4
  ]

txtN s = (txt s, False)

dia = drawDFA exampleDFA # frame 0.5
  \end{diagram}
\end{center}
\end{xframe}

\begin{xframe}

  \begin{center}
    \textbf{D}eterministic \textbf{F}inite \textbf{A}utomata \bigskip

  \begin{diagram}[width=150]
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
  \end{diagram} \bigskip

  Drop sink states; DFA halts and rejects if it can't take a step.
% \medskip

% \onslide<2->
% (We can also drop \emph{finiteness}.)
  \end{center}
\end{xframe}

\begin{xframe}{Regular expressions \& DFAs}
  Well-known: DFAs and regular expressions are ``about the same
  thing'' (Kleene, 1951). Every regular expression has a corresponding
  DFA, and vice versa.
\end{xframe}

\begin{xframe}{Semirings}
  Up to isomorphism, both polynomial functors and regular expressions
  form commutative \emph{semirings} (aka \emph{rigs}):

  \begin{itemize}
  \item Associative operations $+$, $\sprod$ with identities $0$, $1$
  \item $+$ is commutative
  \item $\sprod$ distributes over $+$
  \item $+$ does \emph{not} necessarily have inverses (nor $\bullet$)
  \end{itemize}

  Other examples: $(\N,+,\times)$, $(\{\mathit{true},\mathit{false}\},
  \lor, \land)$, $(\R \union \{\infty\}, \max, +)$ \medskip

  \onslide<2->
  In fact, polynomial functors and regular expressions are both
  \emph{star semirings}, with $x^* = 1 + x \sprod x^*$.
\end{xframe}

\begin{xframe}{Transition matrices for DFAs}
  \begin{center}
  \begin{tabular}{m{2in}m{2in}}
  \begin{center}
  \begin{diagram}[width=130]
import TypeMatricesDiagrams

exampleDFA :: DFA (Diagram B, Bool)
exampleDFA = dfa
  [ 1 --> (False, origin)
  , 2 --> (False, 5 ^& 0)
  , 3 --> (True,  10 ^& 0)
  , 4 --> (False, 5 ^& (-5))
  ]
  [ 1 >-- txtN "A" --> 2
  , 2 >-- txtN "B" --> 1

  , 2 >-- txtN "A" --> 3
  , 3 >-- txtN "B" --> 2

  , 1 >-- (txt "B", True) --> 4
  , 3 >-- txtN "A" --> 4

  , 4 >-- txtN "A,B" --> 4
  ]

txtN s = (txt s, False)

dia = drawDFA exampleDFA # frame 0.5
  \end{diagram}
  \end{center}
  &
\[
\begin{bmatrix}
  \cdot & A & \cdot & B \\
  B & \cdot & A & \cdot \\
  \cdot & B & \cdot & A \\
  \cdot & \cdot & \cdot & A+B
\end{bmatrix}
\]
\end{tabular}

\onslide<2-> Interpret edge labels in an arbitrary semiring
(weighted automata theory; O'Connor 2011, Dolan 2013)
  \end{center}
\end{xframe}

\section{Constrained polynomial functors}
\label{sec:constrained}

\begin{xframe}{Constrained polynomial functors}
  \begin{itemize}
  \item Given a (univariate) $F$ and some regular expression $R$ over
    $\Sigma = \{A_1, \dots, A_n\}$
  \item Want to have a restricted version $F_R$ of $F\ (A_1 + \dots +
    A_n)$ so the sequences of $A_i$ (obtained from an inorder
    traversal) always match $R$.
  \end{itemize}

  \begin{center}
    \begin{diagram}[width=250]
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import TypeMatricesDiagrams

t1 = nd
    [ nd
      [ nd $
          leaves [B, C]
      , lf B
      ]
    , nd
      [ nd
        [ lf A
        , nd $ leaves [C, C]
        ]
      , nd $ leaves [A, B]
      ]
    ]
  where nd     = Node Nothing
        lf x   = Node (Just x) []
        leaves = map lf

t2 = nd
    [ nd
      [ nd $
          leaves [A, A]
      , lf A
      ]
    , nd
      [ nd
        [ lf B
        , nd $ leaves [B, C]
        ]
      , nd $ leaves [C, C]
      ]
    ]
  where nd     = Node Nothing
        lf x   = Node (Just x) []
        leaves = map lf

dia = [ vsep 3 [ renderT t1, text "$T(A+B+C)$" # scale 1.5 ]
      , vsep 3 [ renderT t2, text "$T_{A^*B^*C^*}(A,B,C)$" # scale 1.5 ]
      ]
      # hsep 10 # frame 0.5
\end{diagram}
%$
  \end{center}
\end{xframe}

% \begin{xframe}{
%   \item<2-> That is, find a multivariate $F_R$ with the ``same shape'' as $F$ but
%     whose allowed sequences of element types always match $R$.
%   \item<3-> (``Same shape'' = natural injection $F_R\ A\ \dots\ A \to F\ A$)

%   \end{itemize}
% \end{xframe}

\begin{xframe}{Example}
     \begin{center}
       \[ L = 1 + X \times L \]
       \[ R = (AA)^* \]

  \begin{tabular}{c m{3in}}
  $L_R(\N) =$ &
  \begin{diagram}[width=200]
    import           Diagrams

    ls2 = [[], [3,4 :: Int], [1,4,2,6], [3,9,2,0,8,4]]

    dia = vsep 1 (map drawList ls2) # frame 0.5
  \end{diagram}
  \end{tabular}
  \end{center}
\end{xframe}

\begin{xframe}{Example}
  \[ P = X + P^2 \]
  \[ R = A^*HA^* \]
  \begin{center}
  \begin{tabular}{c m{3in}}
  $P_R(A,H) \ni$ &
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
\end{tabular}

\onslide<2-> \dots this is differentiation!  $P'(A) = P_R(A,1)$.
  \end{center}
\end{xframe}

\begin{xframe}{Example: Dissection}
  \[ P = X + P^2 \]
  \[ R = B^*HA^* \]
  \begin{center}
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
        [ lf O
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
  \end{center}
\end{xframe}

\begin{xframe}{The problem}
  \begin{center}
    \textbf{Given a polynomial functor $F$ and regular expression $R$,
      compute a (system of mutually recursive, multivariate)
      polynomial functor(s) representing $F_R$.}
  \end{center}
\end{xframe}

\begin{xframe}{The setup}
  Given:
  \begin{itemize}
  \item Polynomial functor $F$
  \item DFA $D$
  \end{itemize} \medskip

  \onslide<2->
  Let $F_{ij}$ denote the (multivariate) polynomial functor
  \begin{itemize}
    \item with same shape as $F$
    \item constrained by sequences which take the DFA from state $i$
      to state $j$
  \end{itemize} \medskip

  \onslide<3->
  Ultimately we are interested in $\sum_{q \in \mathrm{final}(D)} F_{1q}$.
\end{xframe}

\begin{xframe}
  \[ 0_{ij} = 0 \]

  \begin{center}
    $0$ is the only thing with the same shape as $0$.
  \end{center}
\end{xframe}

\begin{xframe}
  \[  1_{ij} = \begin{cases} 1 \quad i = j \\ 0 \quad i \neq
    j \end{cases} \]

  \begin{center}
    $0$ and $1$ are the only things with the same shape as $1$.  A
    $1$-structure doesn't make the DFA transition at all.
  \end{center}
\end{xframe}

\begin{xframe}
  \[ X_{ij} = \sum_{i \stackrel{A}{\to} j} X_A \]

  \begin{center}
    \begin{diagram}[width=200]
import TypeMatricesDiagrams

i2jDFA =
  mconcat
  [ (txt "i" <> circle 1 # fc (nodeColors !! 0))
  , (txt "j" <> circle 1 # fc (nodeColors !! 1)) # translateX 5
  , arcArrow origin (5 ^& 0) 1 1.4 (txt "A")
  , arcArrow origin (5 ^& 0) (-1) 1.4 (txt "B")
  ]

aORb = hsep 2 [ drawType A, txt "OR", drawType B ]

dia = hsep 4 [i2jDFA, aORb]
  \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}
  \[ (F + G)_{ij} = F_{ij} + G_{ij} \]
  \bigskip

  \begin{center}
    \begin{diagram}[width=250]
      import TypeMatricesDiagrams

      i2j q0 q1 lab = mconcat
        [ mkNode 0 q0
        , mkNode 1 q1 # translateX 7
        ]
        # connectStates q0 q1 lab 1
        # centerX

      li2j = i2j "i" "j"

      dia = vsep 1
        [ li2j "$(F+G)_{ij}$"
        , txt "="
        , hsep 2 [ li2j "$F_{ij}$", txt "OR", li2j "$G_{ij}$" ]
          # centerX
        ]
    \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}
  \[ (F \sprod G)_{ij} = \sum_{q \in \mathrm{states}(D)} F_{iq}
  G_{qj} \]

  \begin{center}
    \begin{diagram}[width=200]
      import TypeMatricesDiagrams

      dia = mconcat
        [ mkNode 0 "i"
        , mkNode 2 "$q_0$" # translate (7 ^& 4)
        , mkNode 2 "$q_1$" # translate (7 ^& 1)
        , vellipsis # translate (7 ^& (-1.5))
        , mkNode 2 "$q_k$" # translate (7 ^& (-4))
        , mkNode 1 "j" # translateX 14
        ]
        # applyAll
        [ connectStates "i" ("$q_" ++ x ++ "$") ("$F_{iq_" ++ x ++ "}$") off
        . connectStates ("$q_" ++ x ++ "$") "j" ("$G_{q_" ++ x ++ "j}$") off
        || (x,off) <- [("0",1), ("1",-1), ("k",-1)]
        ]
      vellipsis = vsep 0.3 (replicate 3 (circle 0.1 # fc black)) # centerY
    \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}
  \begin{align*}
  0_{ij} &= 0 \\
   1_{ij} &= \begin{cases} 1 \quad i = j \\ 0 \quad i \neq
     j \end{cases} \\
  X_{ij} &= \sum_{i \stackrel{A}{\to} j} X_A \\
  (F + G)_{ij} &= F_{ij} + G_{ij} \\
  (F \sprod G)_{ij} &= \sum_{q \in \mathrm{states}(D)} F_{iq} G_{qj}
  \end{align*}

  \onslide<2->
  \begin{center}
    These are matrix operations!  $X_{ij}$ is the transition matrix
    for the DFA, interpreted in the semiring of polynomial functors.
  \end{center}
\end{xframe}

\begin{xframe}
    Given a DFA $D$,
    \[ F \mapsto \begin{bmatrix} F_{11} & \dots & F_{1n} \\
      \vdots & \ddots & \vdots \\ F_{n1} & \dots &
      F_{nn} \end{bmatrix} \]
    is a \emph{semiring homomorphism} from (unary) polynomial functors
    to $n \times n$ matrices of (arity-$||\Sigma||$) polynomial
    functors.
\end{xframe}

\begin{xframe}{Example}
\[ L = 1 + XL \qquad R = (AA)^* \]
\begin{center}
  \begin{tabular}{m{1in}m{1in}}
  \begin{center}
  \begin{diagram}[width=75]
import TypeMatricesDiagrams

aaStar :: DFA (Diagram B)
aaStar = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 ^& 0)
  ]
  [ 1 >-- txt "A" --> 2
  , 2 >-- txt "A" --> 1
  ]

dia = drawDFA aaStar # frame 0.5
  \end{diagram}
  \end{center}
  &
  \[ \begin{bmatrix}
     0 & X_A \\ X_A & 0
     \end{bmatrix}
  \]
\end{tabular}

\begin{multline*}
  \begin{bmatrix}
    L_{11} & L_{12} \\
    L_{21} & L_{22}
  \end{bmatrix}
  =
  \begin{bmatrix}
    1 & 0 \\
    0 & 1
  \end{bmatrix}
  +
  \begin{bmatrix}
    0 & X_A \\
    X_A & 0
  \end{bmatrix}
  \begin{bmatrix}
    L_{11} & L_{12} \\
    L_{21} & L_{22}
  \end{bmatrix}
  \\
  =
  \begin{bmatrix}
    1 + X_A L_{21} & X_A L_{22} \\
    X_A L_{11} & 1+ X_A L_{12}
  \end{bmatrix}.
\end{multline*}
\end{center}
\end{xframe}

\begin{xframe}{Example}
  \[ T = 1 + XT^2 \qquad R = A^*HA^* \]
  \begin{center}
  \begin{tabular}{m{1in}m{1in}}
  \begin{center}
  \begin{center}
  \begin{diagram}[width=75]
import TypeMatricesDiagrams

aaStar :: DFA (Diagram B)
aaStar = dfa
  [ 1 --> (False, origin)
  , 2 --> (True, 5 ^& 0)
  ]
  [ 1 >-- txt "H" --> 2
  , 1 >-- txt "A" --> 1
  , 2 >-- txt "A" --> 2
  ]

dia = drawDFA aaStar # frame 0.5
  \end{diagram}
  \end{center}
  \end{center}
  &
  \[ \begin{bmatrix}
    X_A & X_H \\ 0 & X_A
  \end{bmatrix} \]
  \end{tabular}
  \begin{multline*}
  \begin{bmatrix}
    T_{11} & T_{12} \\
    0 & T_{22}
  \end{bmatrix}
  =
  \begin{bmatrix}
    1 & 0 \\
    0 & 1
  \end{bmatrix}
  +
  \begin{bmatrix}
    X_A & X_H \\
    0 & X_A
  \end{bmatrix}
  \begin{bmatrix}
    T_{11} & T_{12} \\
    0 & T_{22}
  \end{bmatrix}^2
  \\
  =
  \begin{bmatrix}
    X_A T_{11}^2 & X_A(T_{11}T_{12} + T_{12}T_{22}) + X_HT_{22}^2 \\
    0 & X_A T_{22}^2
  \end{bmatrix}.
  \end{multline*}
  \end{center}
\end{xframe}

\section{Derivative and dissection}
\label{sec:deriv-dissect}

\begin{xframe}{Derivative}
  \begin{center}
  \begin{tabular}{m{1in}m{1in}}
  \begin{diagram}[width=75]
import TypeMatricesDiagrams

deriv :: DFA (Diagram B)
deriv = dfa
  [ 1 --> (False, origin)
  , 2 --> (True , 5 ^& 0)
  ]
  [ 1 >-- txt "A" --> 1
  , 1 >-- txt "H" --> 2
  , 2 >-- txt "A" --> 2
  ]

dia = drawDFA deriv # frame 0.5
  \end{diagram}
  &
  \[
  \begin{bmatrix}
    X_A & X_H \\ 0 & X_A
  \end{bmatrix}
  \]
  \end{tabular}
  \end{center}
  \[ F \mapsto
  \begin{bmatrix}
    F & F' \\ 0 & F
  \end{bmatrix}
  \]

  \onslide<2->
  \[
  \begin{bmatrix}
    F & F' \\ 0 & F
  \end{bmatrix}
  \begin{bmatrix}
    G & G' \\ 0 & G
  \end{bmatrix}
  =
  \begin{bmatrix}
    FG & FG' + F'G \\
    0 & FG
  \end{bmatrix}
  \]
\end{xframe}

\begin{xframe}{Dissection}
  \begin{center}
\begin{diagram}[width=100]
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

\begin{tabular}{m{1.5in}m{1.5in}}
    \begin{diagram}[width=75]
import TypeMatricesDiagrams

bstarhastar :: DFA (Diagram B)
bstarhastar = dfa
  [ 1 --> (False, origin)
  , 2 --> (True, 5 ^& 0)
  ]
  [ 1 >-- txt "H" --> 2

  , 1 >-- txt "B" --> 1
  , 2 >-- txt "A" --> 2
  ]

dia = drawDFA bstarhastar # frame 0.5
  \end{diagram}
  &
  \[
  \begin{bmatrix}
    X_B & X_H \\
    0 & X_A
  \end{bmatrix}
  \]
  \end{tabular}
  \[
    F \mapsto
    \begin{bmatrix}
      \clowns F & \dissect F \\ 0 & \jokers F
    \end{bmatrix}
    \qquad
    \left( \begin{array}{c}\clowns F\ B\ A = F\ B \\ \jokers F\ B\ A
        = F\ A\end{array} \right)
  \]
  \end{center}
\end{xframe}

\begin{xframe}{Dissection}
  \[ \dissect (FG) = \clowns F \dissect G + \dissect F \clowns G \]

  \onslide<2->
  \[
  \begin{bmatrix}
    \clowns F & \dissect F \\
    0 & \jokers F
  \end{bmatrix}
  \begin{bmatrix}
    \clowns G & \dissect G \\
    0 & \jokers G
  \end{bmatrix}
  =
  \begin{bmatrix}
    \clowns F \clowns G & \clowns F \dissect G + \dissect F \jokers G
    \\
    0 & \jokers F \jokers G
  \end{bmatrix}
  \]
\end{xframe}

\begin{xframe}{Divided differences}
  \[ f_{b,a} = \frac{f_b - f_a}{b - a} \]

  \onslide<2->
  $f_{b,a}$ is the \emph{average} change in $f$ from $a$ to $b$, \ie
  the secant slope. \medskip

  Note $f_{b,a} \to f'(a)$ as $b \to a$.
\end{xframe}

\begin{xframe}{Divided differences and dissection?}
  \onslide<2->
  Well-known that
  \[ f \mapsto
  \begin{bmatrix}
    f_b & f_{b,a} \\ 0 & f_a
  \end{bmatrix}
  \]
  is a semiring homomorphism. \medskip

  Proof (interesting bit):
  \begin{align*}
    (fg)_{b,a} &= \frac{(fg)_b - (fg)_a}{b - a} \\
    &= \frac{(fg)_b - f_bg_a + f_bg_a - (fg)_a}{b-a} \\
    &= \frac{f_b(g_b - g_a) + (f_b - f_a)g_a}{b-a} \\
    &= f_b g_{b,a} + f_{b,a} g_a.
\end{align*}
\end{xframe}

\begin{xframe}{Divided differences and |right|}
  Rearranging $f_{b,a} = \frac{f_b - f_a}{b - a}$ yields
  \[ f_a + f_{b,a} \times b = a \times f_{b,a} + f_b \]
  aka
\begin{spec}
  right :: F A + (Dissect F B A * B) <-> (A * Dissect F B A) + F B
\end{spec}
\end{xframe}

\begin{xframe}{Higher-order divided differences?}
\begin{equation*}
f \mapsto
\begin{bmatrix}
f_c & f_{c,b} & f_{c,b,a} \\
0   & f_b    & f_{b,a}   \\
0   & 0      & f_a
\end{bmatrix}
\end{equation*}

\onslide<2->
  \begin{center}
    \begin{tabular}{m{1.5in}m{1.5in}}
      \begin{center}
  \begin{diagram}[width=100]
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
\end{center}
&
\begin{center}
\begin{diagram}[width=100]
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import TypeMatricesDiagrams

t = nd
    [ nd
      [ nd $
          leaves [C, C]
      , lf H
      ]
    , nd
      [ nd
        [ lf B
        , nd $ leaves [B, B]
        ]
      , nd $ leaves [H, A]
      ]
    ]
  where nd     = Node Nothing
        lf x   = Node (Just x) []
        leaves = map lf

dia = renderT t # frame 0.5
\end{diagram}
%$
\end{center}

\end{tabular}
\end{center}

\end{xframe}

\begin{xframe}{Higher-order divided differences?}
\begin{equation*}
f_{x_n \dots x_0} = \frac{f_{x_n
    \dots x_1} - f_{x_{n-1} \dots x_0}}{x_n - x_0}.
\end{equation*}

Corresponding isomorphism??
\end{xframe}

\begin{xframe}
  \begin{center}
    Thank you! \bigskip

    \includegraphics[width=1in]{deriv-tree}
  \end{center}
\end{xframe}

% \begin{xframe}{Derivative}
%   \[
%   \begin{bmatrix}
%     X_A & X_H \\ 0 & X_A
%   \end{bmatrix}
%   =
%   X_A I +
%   \begin{bmatrix}
%     0 & X_H \\ 0 & 0
%   \end{bmatrix}
%   = X_A I + d
%   \]
%   \begin{center}
%     Note $d^2 = 0$. \[ (X_A I + d)^n \cong (X_A I)^n + n(X_A I)^{n-1}
%     d \]
%     XXX extend to polynomial???  Maybe I should just leave this part out?
%   \end{center}

% \end{xframe}

\end{document}