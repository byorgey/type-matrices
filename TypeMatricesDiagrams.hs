module TypeMatricesDiagrams where

import           Data.Tree
import           Diagrams.Backend.Postscript
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree

data Type = A | B | H

drawType A = text "a" # italic # centerX <> square 2 # fc yellow
drawType B = text "b" # italic # centerX <> circle 1 # fc red
drawType H = text "1" # centerX <> circle 1 # fc white # dashing [0.2,0.2] 0

renderT :: Tree (Maybe Type) -> Diagram Postscript R2
renderT
  = renderTree
      (\x -> case x of
          Nothing -> mempty
          Just t  -> drawType t
      )
      (~~)
  . symmLayout' with { slHSep = 4, slVSep = 3 }
