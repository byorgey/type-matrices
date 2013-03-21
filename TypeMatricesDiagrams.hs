module TypeMatricesDiagrams where

import           Data.Tree
import           Diagrams.Backend.Postscript
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree

data Type = A | B | H

drawType A = text "a" # italic <> square 2 # fc blue
drawType B = text "b" # italic <> circle 1 # fc red
drawType H = text "1" <> circle 1 # fc white # dashing [0.1,0.1] 0

renderT :: Tree (Maybe Type) -> Diagram Postscript R2
renderT
  = renderTree
      (\x -> case x of
          Nothing -> mempty
          Just t  -> drawType t
      )
      (~~)
  . symmLayout' with { slHSep = 4, slVSep = 3 }
