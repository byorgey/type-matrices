{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

import           Data.Foldable
import           Data.Traversable

data Parens a where
  Leaf :: a -> Parens a
  Branch :: Parens a -> Parens a -> Parens a
  deriving (Show, Functor, Foldable, Traversable)

p :: Parens Int
p = Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Branch (Leaf 3) (Leaf 4)) (Leaf 5))

data Parens2 a b where
  Hole  :: Parens2 a b
  HoleL :: Parens2 a b -> Parens a -> Parens2 a b
  HoleR :: Parens b -> Parens2 a b -> Parens2 a b
  deriving Show

-- P[a,b] = (P[b] - P[a])/(b - a)
-- b P[a,b] + P[a] = P[b] + a P[a,b]

-- Can we write this code more generically, without specific reference to
-- the constructors of Parens or Parens2?  I do not look forward to writing
-- similar code for Parens3.  How does 'jokers & clowns' write this code?
moveR2 :: Either (Parens a) (b, Parens2 a b) -> Either (a, Parens2 a b) (Parens b)
moveR2 (Left (Leaf a)) = Left (a, Hole)
moveR2 (Left (Branch l r)) =
  case moveR2 (Left l) of
    Left (a, dl) -> Left (a, HoleL dl r)
    Right bs     -> undefined  -- can this case ever happen??
moveR2 (Right (b, Hole)) = Right (Leaf b)
moveR2 (Right (b, (HoleL bsas as))) =    -- maybe we are not using the right data
  case moveR2 (Right (b, bsas)) of       -- structures.  Need to represent pointed
                                         -- things explicitly so we don't need
                                         -- to pass b around etc.
    Left (a, bsas') -> Left (a, HoleL bsas' as)
    Right bs        ->
      case moveR2 (Left as) of
        Left (a, as') -> Left (a, HoleR bs as')
        Right bs2     -> Right (Branch bs bs2)   -- can this case ever happen?
moveR2 (Right (b, (HoleR bs bsas))) =
  case moveR2 (Right (b, bsas)) of
    Left (a, bsas') -> Left (a, HoleR bs bsas')
    Right bs2 -> Right (Branch bs bs2)

-- Right, of course, Clowns & Jokers does it *generically*.

-- algebra of 1-ary functors

data Void1 a
  deriving (Functor)
instance Show (Void1 a) where
  show _ = undefined

refute1 :: Void1 a -> r
refute1 _ = undefined

data K1 b a = K1 b
  deriving (Show, Functor)

type Unit1 = K1 ()

data Id1 a = Id1 a
  deriving (Show, Functor)

data (Plus1 f g) a = Inl1 (f a) | Inr1 (g a)
  deriving (Show, Functor)

data (Times1 f g) a = Pair1 (f a) (g a)
  deriving (Show, Functor)

-- algebra of 2-ary functors

class Bifunctor h where
  bimap :: (a1 -> b1) -> (a2 -> b2) -> h a1 b2 -> h a2 b2

refute2 :: Void2 c j -> a
refute2 _ = undefined

data Void2 c j
instance Bifunctor Void2 where
  bimap f g v = refute2 v

instance Show (Void2 c j) where
  show v = refute2 v

data K2 x c j = K2 x
  deriving (Show)
instance Bifunctor (K2 x) where
  bimap _ _ (K2 x) = K2 x

type Unit2 = K2 ()

data Plus2 f g c j = Inl2 (f c j) | Inr2 (g c j)
  deriving (Show)
instance (Bifunctor f, Bifunctor g) => Bifunctor (Plus2 f g) where
  bimap h k (Inl2 f) = Inl2 (bimap h k f)
  bimap h k (Inr2 g) = Inr2 (bimap h k g)

-- Dissection

class HasD2 (f :: * -> *) where
  type D2 f :: * -> * -> *

  right :: Either (f j) (D2 f c j, c) -> Either (j, D2 f c j) (f c)

instance HasD2 Void1 where
  type D2 Void1 = Void2

  right (Left v) = refute1 v
  right (Right (v,_)) = refute2 v

instance HasD2 (K1 b) where
  type D2 (K1 b) = Void2

  right (Left (K1 b)) = Right (K1 b)

instance HasD2 Id1 where
  type D2 Id1 = Unit2

  right (Left (Id1 j))     = Left (j, K2 ())
  right (Right (K2 (), c)) = Right (Id1 c)

instance (HasD2 f, HasD2 g) => HasD2 (Plus1 f g) where
  type D2 (Plus1 f g) = Plus2 (D2 f) (D2 g)

  right (Left (Inl1 fj)) = case right (Left fj) of
                             Left  (j, f') -> Left (j, Inl2 f')
                             Right fc -> Right (Inl1 fc)
  right (Left (Inr1 gj)) = case right (Left gj) of
                             Left (j, g') -> Left (j, Inr2 g')
                             Right gc -> Right (Inl1 gc)
  right (Right (Inl2 f', c)) = case right (Right (f', c)) of
                                 Left (j, f') -> _
                                 Right fc -> _
  right (Right (Inr2 g', c)) = _

main :: IO ()
main = print 'x'
