{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module TypeMatricesDiagrams where

import qualified Data.Map                  as M
import           Data.Maybe                (fromMaybe)
import           Data.Tree
import           Diagrams.Backend.PGF
import           Diagrams.Core.Envelope
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Text
import           Linear.V2                 (perp)

type Dia = QDiagram PGF V2 Double Any

data Type = A | B | H | O

drawType A = text "A" # italic # centerX # translateX (-0.05) <> square 2 # fc lightblue
drawType B = text "B" # italic # centerX # translateX (-0.1) <> circle 1 # fc lightgreen
drawType H = text "H" # italic # centerX # translateX (-0.1) <> drawType O
drawType O = circle 1 # fc white # dashingG [0.2,0.2] 0

renderT :: Tree (Maybe Type) -> Diagram B
renderT
  = renderTree
      (\x -> case x of
          Nothing -> mempty
          Just t  -> drawType t
      )
      (~~)
  . symmLayout' (with & slHSep .~ 4 & slVSep .~ 3)

arcArrow :: P2 Double -> P2 Double -> Double -> Double -> Diagram B -> Diagram B
arcArrow p1 p2 ht offs label
    =  aDia
    <> label
       # moveTo (lerp 0.5 p1 p2 .+^ (signum ht *^ ((h + envelopeS ((-signum ht) *^ perp v) label) *^ signorm (perp v))))
  where
    h = abs ht
    straight = h < 0.00001
    v  = p2 .-. p1
    d  = norm (p2 .-. p1)
    th = acos ((d*d - 4*h*h)/(d*d + 4*h*h))
    r = d/(2*sin th)
    phi | straight = 0 @@ rad
        | otherwise = (offs/r) @@ rad
    mid | ht >= 0   = (tau/4) @@ rad
        | otherwise = (3*tau/4) @@ rad
    st  = mid ^-^ (th @@ rad) ^+^ phi
    end = mid ^+^ (th @@ rad) ^-^ phi
    a | straight
      = hrule (d - 2*offs) # alignL # translateX offs
      | otherwise
      = arc (xDir # rotate st) (end ^-^ st)
      # scale r
      # translateY ((if ht > 0 then negate else id) (r-h))
      # translateX (d/2)
      # (if ht > 0 then reversePath else id)
    endPt = atEnd . head . pathTrails $ a
    hd = triangle 0.4 # rotateBy (-1/4) # alignR # fc black # scaleY 0.7
       # rotate (if ht >= 0 then st ^-^ ((tau/4) @@ rad) else ((3*tau/4) @@ rad) ^-^ st)
    aDia
      = ( hd # moveTo endPt
        <>
          a  # stroke
        )
        # rotate (signedAngleBetween v unitX)
        # moveTo p1

data DFA e = DFA (M.Map Int (Bool, P2 Double)) (M.Map (Int,Int) e)

class DrawableEdge e where
  drawEdge :: M.Map Int (Bool, P2 Double) -> (Int,Int) -> e -> Diagram B

instance DrawableEdge (Dia, Bool) where
  drawEdge states (i,j) (label,flp)
    | i == j
    = arcArrow
        (pti # translateY (-1.4) # rotateAround pti (negated theta))
        (pti # translateY (-1.4) # rotateAround pti theta)
        (-1.3)
        0
        label
    | otherwise
    = arcArrow pti ptj (if flp then (-1) else 1) 1.4 label
    where
      theta = 20 @@ deg
      stPos ix = fromMaybe (1000 ^& 1000) $ snd <$> M.lookup ix states
      pti = stPos i
      ptj = stPos j

instance DrawableEdge Dia where
  drawEdge states e label = drawEdge states e (label, False)

infixr 3 >--
infixr 3 -->
i >-- (a,j) = ((i,j),a)
(-->) = (,)

dfa states edges = DFA (M.fromList states) (M.fromList edges)

drawDFA :: (DrawableEdge e) => DFA e -> Diagram B
drawDFA (DFA states edges) =
  drawEdges states (M.assocs edges) <> drawStates (M.assocs states)

drawStates = mconcat . map drawState
  where
    drawState (n,(final,pos))
      = (text (show n) <> circle 1 <> (if final then circle 1.2 else mempty))
      # moveTo pos

drawEdges states = mconcat . map (uncurry (drawEdge states))

testDFA = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 ^& 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1
  ]

txt s = text s # italic # scale 0.8 <> square 1 # lw none

-- main = defaultMain $ drawDFA testDFA

