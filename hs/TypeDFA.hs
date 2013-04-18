{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

import Data.Void
import GHC.TypeLits

data Tree a = Leaf a | Fork (Tree a) (Tree a)

data Tree' :: Nat -> Nat -> * -> * -> * where
  Leaf' :: Sing (i :: Nat) -> Sing (j :: Nat) -> Transition i j a b -> Tree' i j a b
  Fork' :: Sing (i :: Nat) -> Sing (j :: Nat) -> Sing (k :: Nat)
        -> Tree' i k a b -> Tree' k j a b -> Tree' i j a b

-- could generalize this more, along the lines of what was in some of
-- the blog posts
type family Transition (i :: Nat) (j :: Nat) a b :: *
type instance Transition 0 0 a b = Void
type instance Transition 0 1 a b = a
type instance Transition 1 0 a b = b
type instance Transition 1 1 a b = Void

data ExTree :: * -> * -> * where
  ExTree :: Tree' i j a b -> ExTree a b

leafA :: a -> ExTree a b
leafA a = ExTree (Leaf' (sing :: Sing 0) (sing :: Sing 1) a)

leafB :: b -> ExTree a b
leafB b = ExTree (Leaf' (sing :: Sing 1) (sing :: Sing 0) b)

fork :: ExTree a b -> ExTree a b -> Maybe (ExTree a b)
fork = undefined  -- hmm
