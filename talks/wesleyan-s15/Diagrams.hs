{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}

module Diagrams where

import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Text

data NodeType a = Nil | Value a | Hole

nodeType :: b -> (a -> b) -> b -> NodeType a -> b
nodeType n _ _ Nil = n
nodeType _ f _ (Value a) = f a
nodeType _ _ h Hole = h

trees :: [BTree Int]
trees =
  [ Empty
  , leaf 3
  , BNode 7 (leaf 2) Empty
  , BNode 4 (leaf 17) (BNode 3 (leaf (-6)) Empty)
  ]

poke :: Eq a => a -> BTree a -> BTree (NodeType a)
poke a = fmap (\case { Value a' | a == a' -> Hole ; n -> n }) . toNTree

toNTree :: BTree a -> BTree (NodeType a)
toNTree Empty = leaf Nil
toNTree (BNode a l r) = BNode (Value a) (toNTree l) (toNTree r)

nil = square 0.4 # fc black
node = ((<> circle 1 # fc lightblue) . text . showElt)
hole = circle 1 # dashingG [0.1,0.1] 0 # fc white
renderNode = nodeType nil node hole

class Elt e where
  showElt :: e -> String

instance Elt Char where
  showElt = (:[])

instance Elt [Char] where
  showElt = id

instance Elt Int where
  showElt = show

-- drawNTree :: ( V b ~ V2, Ord (N b), TypeableFloat (N b)
--              , Renderable (Path V2 (N b)) b
--              , Renderable (Text (N b)) b
--              , Show a)
--              => BTree (Maybe a) -> Diagram b
drawNTree =
    maybe mempty (renderTree renderNode (~~))
  . symmLayoutBin' (with & slVSep .~ 3 & slHSep .~ 3)
  where

drawTree = drawNTree . toNTree

ellipsis = hsep 0.5 $ replicate 3 dot
  where
    dot = circle 0.3 # fc black

drawNList l = nodes #
    (withNames [0 :: Int, length l - 1 :: Int] $ \[s,e] ->
       beneath (location s ~~ location e)
    )
  where
    nodes =
      hsep s
      (zipWith (\i n -> renderNode n # named i) [0 :: Int ..] l)
    s = 1

drawList l = drawNList (map Value l ++ [Nil])

ls = [[1::Int,1], [1,2,4], [2,1,4,3,1,2]]
drawLists ls = vsep 1 (map drawList ls ++ [ellipsis # rotateBy (1/4)])
lsD = drawLists ls
