{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

import Data.Void
import GHC.TypeLits

----------------------------------------------------------------------
-- Initial binary tree type

data Tree a = Leaf a | Fork (Tree a) (Tree a)
  deriving Show

treeFold :: (a -> r) -> (r -> r -> r) -> Tree a -> r
treeFold f g = go
  where
    go (Leaf a)   = f a
    go (Fork l r) = g (go l) (go r)

----------------------------------------------------------------------
-- Derived, restricted type, for the regex (ab)*

data Tree' :: Nat -> Nat -> * -> * -> * where
  Leaf' :: Transition i j a b -> Tree' i j a b
  Fork' :: Tree' i k a b -> Tree' k j a b -> Tree' i j a b

deriving instance (Show a, Show b) => Show (Tree' i j a b)

tree'Fold :: (forall i j. Transition i j a b -> r) -> (r -> r -> r) -> Tree' i j a b -> r
tree'Fold f _ (Leaf' a)   = f a
tree'Fold f g (Fork' l r) = g (tree'Fold f g l) (tree'Fold f g r)

-- could generalize this more, along the lines of what was in some of
-- the blog posts
data Transition :: Nat -> Nat -> * -> * -> * where
  T01 :: a -> Transition 0 1 a b
  T10 :: b -> Transition 1 0 a b

deriving instance (Show a, Show b) => Show (Transition i j a b)

{- Having Transition be a GADT instead of a type family is important.
   Here is what happened when it was a type family:

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

-}

----------------------------------------------------------------------
-- Existentially wrapping Tree' to hide the DFA state indices

data ExTree :: * -> * -> * where
  ExTreeError :: ExTree a b
  ExTree      :: Sing (i :: Nat) -> Sing (j :: Nat) -> Tree' i j a b -> ExTree a b
    -- The singleton arguments allow us to do case analysis on the
    -- type indices i and j at runtime.

instance (Show a, Show b) => Show (ExTree a b) where
  show (ExTreeError)  = "ExTreeError"
  show (ExTree _ _ t) = show t

----------------------------------------------------------------------
-- Automatically building type-correct trees with dynamic checks

leafA :: a -> ExTree a b
leafA a = ExTree sing sing (Leaf' (T01 a))

leafB :: b -> ExTree a b
leafB b = ExTree sing sing (Leaf' (T10 b))

-- fork does runtime case analysis of the existential DFA state
-- indices.  Calling eqNat checks whether they are the same, and if
-- so, actually makes that fact known to the type checker.
fork :: ExTree a b -> ExTree a b -> ExTree a b
fork (ExTree i k1 t1) (ExTree k2 j t2)
  = case eqNat k1 k2 of
      Nothing   -> ExTreeError
      Just Refl -> ExTree i j (Fork' t1 t2)
fork _ _ = ExTreeError

----------------------------------------------------------------------
-- Converting to and from restricted trees

toTree :: ExTree a b -> Maybe (Tree (Either a b))
toTree ExTreeError    = Nothing
toTree (ExTree _ _ t) = Just $ tree'Fold leafToEither Fork t
  where
    leafToEither (T01 a) = Leaf (Left a)
    leafToEither (T10 b) = Leaf (Right b)

fromTree :: Tree (Either a b) -> ExTree a b
fromTree = treeFold (either leafA leafB) fork

-- Dynamically check whether a tree conforms to (ab)*
checkTree :: Tree (Either a b) -> Maybe (Tree (Either a b))
checkTree = toTree . fromTree

----------------------------------------------------------------------
-- This stuff is probably already in a library somewhere

data (:=:) (a :: Nat) (b :: Nat) where
  Refl :: a :=: a

eqNat :: Sing (i :: Nat) -> Sing (j :: Nat) -> Maybe (i :=: j)
eqNat i j = case (isZero i, isZero j) of
              (IsZero, IsZero)       -> Just Refl
              (IsSucc i', IsSucc j') -> case eqNat i' j' of
                                          Nothing   -> Nothing
                                          Just Refl -> Just Refl
              _                      -> Nothing
--------------------------------------------------

