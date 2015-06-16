%% -*- mode: LaTeX; compile-command: "cabal exec runhaskell Shake.hs" -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

%include polycode.fmt

%format Dissect = "\dissect"

\usepackage[all]{xy}
\usepackage{brent}
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\etc}{\textit{etc.}}

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
%% XXX todo fix title graphic to use same color scheme as the rest of
%% the slides
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

  XXX this picture is deceptive.

  \begin{center}
    \begin{diagram}[width=200]
      import Diagrams
      tree1 = drawTree (trees !! 3) # frame 0.5
      tree2 = drawNTree (poke 3 (trees !! 3)) # frame 0.5
      dia = hsep 2 $ -- $
        map centerY [text "$\\partial$" # scale 3, tree1, arrowV (5 ^& 0), tree2]
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
  right :: p j + (Dissect p c j, c) -> (j, Dissect p c j) + p c
\end{spec}

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
  Polynomial functors are those functors $F : \Set \to \Set$
  inductively built from:
  \begin{align*}
    0(A) &= \varnothing \\
    1(A) &= \{\star\} \\
    X(A) &= A \\
    (F + G)(A) &= F(A) \uplus G(A) \\
    (F \cdot G)(A) &= F(A) \times G(A)
  \end{align*}

  \onslide<2-> Can easily generalize to multivariate polynomial
  functors \[ F : \Set^n \to \Set. \] $X$ generalizes to projections
  $X_j(A_1,\dots,A_n) = A_j$.
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

\onslide<2->
(We can actually drop \emph{finite})
  \end{center}
\end{xframe}

\begin{xframe}{Regular expressions \& DFAs}
  Well-known: DFAs and regular expressions are ``about the same
  thing'' (Kleene, 1951). Every regular expression has a corresponding
  DFA, and vice versa.
\end{xframe}

\begin{xframe}{Semirings}
  Up to isomorphism, both polynomial functors and regular expressions
  form commutative \emph{semirings}:

  \begin{itemize}
  \item Associative operations $+$, $\cdot$ with identities $0$, $1$
  \item $+$ is commutative
  \item $\cdot$ distributes over $+$
  \item $+$ does \emph{not} necessarily have inverses
  \end{itemize}

  Other examples: $(\N,+,\cdot)$, $(\{\mathit{true},\mathit{false}\},
  \lor, \land)$, $(\R \union \{\infty\}, \max, +)$
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

\onslide<2->
Interpret edge labels in an arbitrary semiring $\to$ XXX
XXX citations (Dolan, O'Connor, etc.)
  \end{center}
\end{xframe}

\section{Constrained polynomial functors}
\label{sec:constrained}

\begin{xframe}{Constrained polynomial functors}
  \begin{itemize}
  \item Given a (univariate) $F$ and some regular expression $R$ over
    $\Sigma = \{A_1, \dots, A_n\}$
  \item Find a multivariate $F_R$ with the ``same shape'' as $F$ but
    whose allowed sequences of element types always match $R$
  \item (``Same shape'' = natural injection $F_R\ A\ \dots\ A \to F\ A$)

  \end{itemize}
\end{xframe}

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

    \onslide<2-> \dots this is differentiation!
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
  \textbf{Given a polynomial functor $F$ and regular expression $R$, compute
  a (system of mutually recursive, multivariate) polynomial functor(s)
  corresponding to $F$ constrained by $R$.}
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
      mkNode i q = (txt q <> circle 1 # fc (nodeColors !! i)) # named q

      i2j q0 q1 lab = mconcat
        [ mkNode 0 q0
        , mkNode 1 q1 # translateX 7
        ]
        # connectStates q0 q1 lab
        # centerX

      connectStates q0 q1 lab
        = ( withNames [q0, q1] $ \ss ->   -- $
              let [p0,p1] = map location ss
                  theLab  = txt lab # scale 0.8
                  labLoc  = lerp 0.5 p0 p1 # translate (perp (p1 .-. p0) # signorm)
                  -- XXX compute rotation
              in  atop (theLab # moveTo labLoc)
          )
        . connectOutside' opts q0 q1

      opts = with & gaps .~ local 0.5
                  & headLength .~ local 0.5
                  & arrowShaft .~ wiggle

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
  \[ (F \cdot G)_{ij} = \sum_{q \in \mathrm{states}(D)} F_{iq}
  G_{qj} \]

  \begin{center}
    \begin{diagram}[width=200]
      dia = circle 1
    \end{diagram}
  \end{center}
\end{xframe}

\begin{xframe}
  \begin{itemize}
  \item $0_{ij} = 0$
  \item $ 1_{ij} = \begin{cases} 1 \quad i = j \\ 0 \quad i \neq
      j \end{cases}$
  \item $X_{ij} = \sum_{i \stackrel{A}{\to} j} X_A$
  \item $(F + G)_{ij} = F_{ij} + G_{ij}$
  \item $(F \cdot G)_{ij} = \sum_{q \in \mathrm{states}(D)} F_{iq} G_{qj}$
  \end{itemize} \bigskip

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
\[ L = 1 + XL, R = (AA)^* \]
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
  \]
  \end{center}
\end{xframe}

\begin{xframe}{Dissection}
  XXX central rule is Leibniz rule for products.

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
  XXX define divided differences (for $n=2$)
\end{xframe}

\begin{xframe}{Divided differences}
  XXX show equivalent matrix formulation
\end{xframe}

\begin{xframe}{Divided differences}
  XXX derive isomorphism |right|
\end{xframe}

\begin{xframe}{Higher-order divided differences}
  XXX show higher-order.
\end{xframe}

\begin{xframe}
  \begin{center}
    Thank you! \bigskip

    \includegraphics[width=1in]{deriv-tree}
  \end{center}
\end{xframe}

\begin{xframe}{Derivative}
  \[
  \begin{bmatrix}
    X_A & X_H \\ 0 & X_A
  \end{bmatrix}
  =
  X_A I +
  \begin{bmatrix}
    0 & X_H \\ 0 & 0
  \end{bmatrix}
  = X_A I + d
  \]
  \begin{center}
    Note $d^2 = 0$. \[ (X_A I + d)^n \cong (X_A I)^n + n(X_A I)^{n-1}
    d \]
    XXX extend to polynomial???  Maybe I should just leave this part out?
  \end{center}

\end{xframe}

\end{document}