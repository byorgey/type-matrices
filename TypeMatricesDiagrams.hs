{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns              #-}

module TypeMatricesDiagrams where

import qualified Data.Map                       as M
import           Data.Maybe                     (fromMaybe)
import           Data.Tree
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Backend.Postscript
import           Diagrams.Core.Envelope
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Text

data Type = A | B | H

drawType A = text "a" # italic # centerX <> square 2 # fc yellow
drawType B = text "b" # italic # centerX <> circle 1 # fc red
drawType H = text "1" # centerX <> circle 1 # fc white # dashing [0.2,0.2] 0

renderT :: (Renderable Text b, Renderable (Path R2) b) => Tree (Maybe Type) -> Diagram b R2
renderT
  = renderTree
      (\x -> case x of
          Nothing -> mempty
          Just t  -> drawType t
      )
      (~~)
  . symmLayout' with { slHSep = 4, slVSep = 3 }

arcArrow :: Renderable (Path R2) b => P2 -> P2 -> Double -> Double -> Diagram b R2 -> Diagram b R2
arcArrow p1 p2 ht offs label
    =  aDia
    <> label
       # moveTo (alerp p1 p2 0.5 .+^ ((h + envelopeS (negateV (perp v)) label) *^ normalized (perp v)))
  where
    perp (coords -> x :& y) = (-y) & x
    h = abs ht
    straight = h < 0.00001
    v  = p2 .-. p1
    d = magnitude (p2 .-. p1)
    th  = acos ((d*d - 4*h*h)/(d*d + 4*h*h))
    r = d/(2*sin th)
    phi | straight = 0
        | otherwise = Rad $ offs/r
    mid | ht >= 0    = tau/4
        | otherwise = 3*tau/4
    st  = mid - Rad th + phi
    end = mid + Rad th - phi
    a | straight
      = hrule (d - 2*offs) # alignL # translateX offs
      | otherwise
      = arc st end
      # scale r
      # translateY ((if ht > 0 then negate else id) (r-h))
      # translateX (d/2)
      # (if ht > 0 then reversePath else id)
    endPt = (\(p,t) -> p .+^ trailOffset t) . head . pathTrails $ a
    hd = triangle 0.4 # rotateBy (-1/4) # alignR # fc black # scaleY 0.7
       # rotate (if ht >= 0 then st - Rad (tau/4) else Rad (3*tau/4) - st)
    aDia
      = ( hd # moveTo endPt
        <>
          a  # stroke
        )
        # rotateBy (direction v)
        # moveTo p1

data DFA a = DFA (M.Map Int (Bool,P2)) (M.Map (Int,Int) a)

infixr 3 >--
infixr 3 -->
i >-- (a,j) = ((i,j),a)
(-->) = (,)

dfa states edges = DFA (M.fromList states) (M.fromList edges)

drawDFA :: (Renderable Text b, Renderable (Path R2) b)
        => DFA (Diagram b R2) -> Diagram b R2
drawDFA (DFA states edges) =
  drawEdges states (M.assocs edges) <> drawStates (M.assocs states)

drawStates = mconcat . map drawState
  where
    drawState (n,(final,pos))
      = (text (show n) <> circle 1 <> (if final then circle 1.2 else mempty))
      # moveTo pos

drawEdges states = mconcat . map drawEdge
  where
    drawEdge ((i,j),label) = arcArrow (stPos i) (stPos j) 1 1.4 label
    stPos i = fromMaybe (1000 & 1000) $ snd <$> M.lookup i states

testDFA = dfa
  [ 1 --> (True, origin)
  , 2 --> (False, 5 & 0)
  ]
  [ 1 >-- txt "a" --> 2
  , 2 >-- txt "b" --> 1
  ]

txt s = text s <> square 1 # lw 0

main = defaultMain $ drawDFA testDFA

