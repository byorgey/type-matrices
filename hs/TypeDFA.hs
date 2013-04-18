{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

import Data.Void
import GHC.TypeLits

data Tree a = Leaf a | Fork (Tree a) (Tree a)
  deriving Show

data Tree' :: Nat -> Nat -> * -> * -> * where
  Leaf' :: Transition i j a b -> Tree' i j a b
  Fork' :: Tree' i k a b -> Tree' k j a b -> Tree' i j a b

-- could generalize this more, along the lines of what was in some of
-- the blog posts
type family Transition (i :: Nat) (j :: Nat) a b :: *
type instance Transition 0 0 a b = Void
type instance Transition 0 1 a b = a
type instance Transition 1 0 a b = b
type instance Transition 1 1 a b = Void

{- aha, the above isn't good enough.  e.g.

>>> :t Fork' (Leaf' 'x') (Leaf' (3 :: Int)) :: Tree' 0 0 Char Int

<interactive>:1:14:
    Couldn't match type `Transition 0 k0 Char Int' with `Char'
    The type variable `k0' is ambiguous
    Possible fix: add a type signature that fixes these type variable(s)
    Expected type: Transition 0 k0 Char Int
      Actual type: Char
    In the first argument of Leaf', namely 'x'
    In the first argument of Fork', namely `(Leaf' 'x')'
    In the expression:
        Fork' (Leaf' 'x') (Leaf' (3 :: Int)) :: Tree' 0 0 Char Int

We need to be able to infer the second state from the first state and
the input type (just like a real DFA's transition function).

-}

data ExTree :: * -> * -> * where
  ExTree :: Sing (i :: Nat) -> Sing (j :: Nat) -> Tree' i j a b -> ExTree a b

toTree :: ExTree a b -> Tree (Either a b)
toTree = undefined

-- Need some sort of typed fold for working with a Tree'?

leafA :: a -> ExTree a b
leafA a = ExTree (sing :: Sing 0) (sing :: Sing 1) (Leaf' a)

leafB :: b -> ExTree a b
leafB b = ExTree (sing :: Sing 1) (sing :: Sing 0) (Leaf' b)

data (:=:) (a :: Nat) (b :: Nat) where
  Refl :: a :=: a

eqNat :: Sing (i :: Nat) -> Sing (j :: Nat) -> Maybe (i :=: j)
eqNat i j = case (isZero i, isZero j) of
              (IsZero, IsZero)       -> Just Refl
              (IsSucc i', IsSucc j') -> case eqNat i' j' of
                                          Nothing   -> Nothing
                                          Just Refl -> Just Refl
              _                      -> Nothing

fork :: ExTree a b -> ExTree a b -> Maybe (ExTree a b)
fork (ExTree i k1 t1) (ExTree k2 j t2)
  = case eqNat k1 k2 of
      Nothing   -> Nothing
      Just Refl -> Just $ ExTree i j (Fork' t1 t2)
