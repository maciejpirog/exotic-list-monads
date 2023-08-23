{-# LANGUAGE Trustworthy #-} -- can't use Safe due to IsList instances
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE AllowAmbiguousTypes #-} -- these are needed for numerical monoids
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

-- The following two extensions are used only in examples:

-- {-# LANGUAGE OverloadedLists #-}
-- {-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Control.Monad.List.Exotic
-- Description : Non-standard monads on the list functor
-- Copyright   : (c) Dylan McDermott, Maciej Piróg, Tarmo Uustalu, 2020
-- License     : MIT
-- Maintainer  : maciej.adam.pirog@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- The usual list monad is only one of infinitely many ways to turn
-- the List functor into a monad. This module collects a number of
-- such exotic "list monads". Most of them have been introduced in the
-- papers:
-- 
-- * [Degrading Lists](https://raw.githubusercontent.com/maciejpirog/exotic-list-monads/master/degrading-lists.pdf)
-- by Dylan McDermott, Maciej Piróg, Tarmo Uustalu (PPDP 2020).
-- 
-- * [Counting Monads on Lists](https://cla.tcs.uj.edu.pl/pdfs/McDermott-Pirog-Uustalu-Abstract.pdf)
-- by Dylan McDermott, Maciej Piróg, Tarmo Uustalu (CLA 2023).
--
-- __Notes:__
--
-- * Types marked with \"(?)\" have not been formally verified to be
-- monads (yet), though they were thoroughly tested with billions of
-- QuickCheck tests.
--
-- * Monads in this module are presented in terms of @join@ rather
-- than '>>='. In each case 'return' is singleton (it is not known if
-- there exists a monad on lists with a different return).
--
-- * For readability, code snippets in this documentation assume the
-- @OverloadedLists@ and @OverloadedStrings@ extensions, which allow
-- us to omit some @newtype@ constructors. Example definitions of
-- joins of monads always skip the @newtype@ constructors, that is,
-- assume '>>=' is always defined as follows for a particular local
-- @join@:
--
-- @
-- m '>>=' f = 'wrap' $ join $ 'map' ('unwrap' . f) $ 'unwrap' m
--  where
--   join = ...
-- @
--
-- * The definitions of monads are optimized for readability and not
-- run-time performance. This is because the monads in this module
-- don't seem to be of any practical use, they are more of a
-- theoretical curiosity.
module Control.Monad.List.Exotic
  (
  -- * List monads in general

    ListMonad(wrap, unwrap)
  , DualListMonad(..)
  , isSingle

  -- * Monads with finite presentation

  -- $finite_presentation
  
  -- ** Pointed magmas

  , PointedMagma(..)
  , FreeRBPM(..)

  -- ** The Global Failure monad
  
  , ZeroSemigroup
  , GlobalFailure(..)

  -- ** The Maze Walk monad

  , PalindromeAlgebra
  , palindromize
  , MazeWalk(..)
  
  -- ** The Discrete Hybrid monad

  , LeaningAlgebra
  , safeLast
  , DiscreteHybrid(..)
    
  -- ** The List Unfold monad
    
  , SkewedAlgebra
  , ListUnfold(..)

  -- ** The Stutter monad

  , StutterAlgebra
  , replicateLast
  , Stutter(..)

  -- ** The Stutter-Keeper monad  

  , StutterKeeperAlgebra
  , StutterKeeper(..)
  
  -- ** The Stutter-Stutter monad

  , StutterStutterAlgebra
  , StutterStutter(..)

  -- * Monads from numerical monoids

  -- $numerical_monoids
  
  -- ** The Mini monad

  , Mini(..)
  
  -- ** The Odd monad

  , Odd(..)

  -- ** The At Least monad

  , AtLeast(..)

  -- ** The Numerical Monoid monad

  , NumericalMonoidGenerators(..)
  , NumericalMonoidMonad(..)
  
  -- * Other list monads

  -- ** The Continuum-of-Monads monad

  -- $continuum-monads

  , SetOfNats(..)
  , ContinuumOfMonads(..)
  
  -- ** The Short Stutter-Keeper monad (?)

  , ShortStutterKeeper(..)
  
  ) where

import Prelude hiding ((<>))
import Control.Monad (ap, join)
import GHC.Exts (IsList(..), IsString(..), Constraint)
import GHC.TypeLits
import Data.Proxy
import qualified Data.Monoid (Monoid)

----------------------------
-- List monads in general --
----------------------------

-- | In this module, a \"list monad\" is a monad in which the
-- underlying functor is isomorphic to List. We require:
--
-- @
-- wrap . unwrap  ==  id
-- unwrap . wrap  ==  id
-- @
--
-- There is a default implementation provided if @m@ is known to be a
-- list (meaning @m a@ is an instance of 'GHC.Exts.IsList' for all
-- @a@).
class (Monad m) => ListMonad m where

  wrap   :: [a] -> m a
  default wrap   :: (IsList (m a), Item (m a) ~ a) => [a] -> m a
  wrap = fromList
  
  unwrap :: m a -> [a]
  default unwrap :: (IsList (m a), Item (m a) ~ a) => m a -> [a]
  unwrap = toList

instance ListMonad []

liftListFun :: (ListMonad m) => ([a] -> [a]) -> m a -> m a
liftListFun f = wrap . f . unwrap

-- | Every list monad has a dual, in which join is defined as
--
-- @
-- join . reverse . fmap reverse
-- @
--
-- (where join is the join of the original list monad), while return is
--
-- @
-- reverse . return
-- @
--
-- (where return is the return of the original list monad).
newtype DualListMonad m a = DualListMonad { unDualListMonad :: m a }
 deriving (Functor)

instance (ListMonad m) => Applicative (DualListMonad m) where
  pure  = return
  (<*>) = ap

instance (ListMonad m) => Monad (DualListMonad m) where
  return = DualListMonad . liftListFun reverse . return
  DualListMonad m >>= f = DualListMonad $ liftListFun reverse $
    liftListFun reverse m >>= liftListFun reverse . unDualListMonad . f

instance (ListMonad m, IsList (m a)) => IsList (DualListMonad m a) where
  type Item (DualListMonad m a) = Item (m a)
  toList (DualListMonad m) = toList m
  fromList xs = DualListMonad (fromList xs)

instance (ListMonad m) => ListMonad (DualListMonad m) where
  wrap   = DualListMonad . wrap
  unwrap = unwrap . unDualListMonad 

-- | Checks if a given list is a singleton (= list of length one).
isSingle :: [a] -> Bool
isSingle [_] = True
isSingle _   = False

-- $finite_presentation
--
-- This section contains monads that come about from free algebras of
-- theories with a finite number of operations, represented as type
-- classes. Coincidentally, all theories in this module have one
-- binary and one nullary operation, that is, each is a subclass of
-- "PointedMagma" with additional laws. (So does the usual list monad,
-- where the subclass is monoid.) It is not known if there exists a
-- list monad that has a finite presentation but necessarily with a
-- different set of operations (there are such monads on non-empty
-- lists, for example, 'Control.Monad.List.NonEmpty.Exotic.HeadTails'
-- and 'Control.Monad.List.NonEmpty.Exotic.HeadsTail').

---------------------
-- Pointed magamas --
---------------------

-- | Pointed magmas are structures with one binary operation and one
-- constant. In general, no laws are imposed.
class PointedMagma a where
  eps  :: a
  (<>) :: a -> a -> a

instance PointedMagma [a] where
  eps  = []
  (<>) = (++)

-- | A class for __free right-braketed__ (subclasses of)
-- __pointed magmas__.
--
-- Most of the monads defined in this module arise from subclasses of
-- 'PointedMagma', in which we do not assume any additional methods,
-- but require the instances to satisfy additional equations. This
-- means that the monad is not only an instance of such a class that
-- defines a type of algebra, but it is /free/ such algebra.
--
-- In particular, we consider theories @c@ in which the equations have
-- the following shapes:
--
-- @
-- x '<>' 'eps'       ==  ...
-- 'eps' '<>' x       ==  ...
-- (x '<>' y) '<>' z  ==  ...
-- @
--
-- Moreover, when read left-to-right, they form a terminating and
-- confluent rewriting system with normal forms of the following
-- shape:
--
-- @
-- 'eps'
-- x '<>' (y '<>' ( ... (z '<>' t) ... ))
-- @
--
-- This class offers a witness that a particular list monad @m@ is a free algebra of
-- the theory @c@. This gives us the function
--
-- @
-- foldRBPM _ ('unwrap' -> []) = 'eps'
-- foldRBPM f ('unwrap' -> xs) = 'foldr1' ('<>') ('map' f xs)
-- @
--
-- which is the unique lifting of an interpretation of generators to a
-- homomorphism (between algebras of this sort) from the list monad to
-- any algebra (an instance) of @c@.
--
-- Note that the default definition of 'foldRBPM' is always the right
-- one for right-bracketed subclasses of 'PointedMagma', so it is
-- enough to declare the relationship, for example:
--
-- @
-- instance FreeRBPM [] 'Data.Monoid.Monoid'
-- @
class (ListMonad m) => FreeRBPM m (c :: * -> Constraint) | m -> c where
  foldRBPM :: (PointedMagma a, c a) => (x -> a) -> m x -> a
  foldRBPM _ (unwrap -> []) = eps
  foldRBPM f (unwrap -> xs) = foldr1 (<>) (map f xs)

instance FreeRBPM [] Data.Monoid.Monoid

------------------------------
-- The Global Failure monad --
------------------------------

-- | A zero semigroup has an associative binary operation and a
-- constant that is absorbing on both sides. That is, the following
-- equations hold:
--
-- @
-- x '<>' 'eps'       ==  'eps'
-- 'eps' '<>' x       ==  'eps'
-- (x '<>' y) '<>' z  ==  x '<>' (y '<>' z)
-- @
class (PointedMagma a) => ZeroSemigroup a

-- | The Global Failure monad arises from free zero semigroups. It
-- implements a kind of nondeterminism similar to the usual List
-- monad, but failing (= producing an empty list) in one branch makes
-- the entire computation fail.  Its join is defined as:
--
-- @
-- join xss | any null xss = []
--          | otherwise    = concat xss
-- @
--
-- For example:
--
-- >>> [1, 2, 3] >>= (\n -> [1..n]) :: GlobalFailure Int
-- GlobalFailure [1,1,2,1,2,3]
-- >>> [1, 0, 3] >>= (\n -> [1..n]) :: GlobalFailure Int
-- GlobalFailure []
newtype GlobalFailure a = GlobalFailure { unGlobalFailure :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (GlobalFailure Char)

instance Applicative GlobalFailure where
  pure  = return
  (<*>) = ap

instance Monad GlobalFailure where
  return x = GlobalFailure [x]
  GlobalFailure xs >>= f = GlobalFailure $ join $ map (unGlobalFailure . f) xs 
   where
    join xss | any null xss = []
             | otherwise    = concat xss

instance IsList (GlobalFailure a) where
  type Item (GlobalFailure a) = a
  toList   = unGlobalFailure
  fromList = GlobalFailure

instance ListMonad GlobalFailure

instance PointedMagma (GlobalFailure a) where
  m <> t = join $ GlobalFailure $ [m, t]
  eps    = GlobalFailure []

instance ZeroSemigroup (GlobalFailure a)

instance FreeRBPM GlobalFailure ZeroSemigroup

-------------------------
-- The Maze Walk monad --
-------------------------

-- | A palindrome algebra is a pointed magma that satisfies the
-- following equations:
--
-- @
-- x '<>' 'eps'       ==  'eps'
-- 'eps' '<>' x       ==  'eps'
-- (x '<>' y) '<>' z  ==  x '<>' (y '<>' (x '<>' z))
-- @
class (PointedMagma a) => PalindromeAlgebra a

-- | Turns a list into a palindrome by appending it and its reversed
-- init. For example:
--
-- @
-- palindromize []       ==  []
-- palindromize \"Ringo\"  ==  \"RingogniR\"
-- @
palindromize :: [a] -> [a]
palindromize [] = []
palindromize xs = xs ++ reverse (init xs)

-- | The Maze Walk monad arises from free palindrome algebras. Its
-- join is defined as:
--
-- @
-- join xss | null xss     = []
--          | any null xss = []
--          | otherwise    = concatMap palindromize (init xss) ++ last xss
-- @
--
-- Intuitively, it is a list of values one encounters when walking a
-- path in a maze.  The bind operation attaches to each value a new
-- "corridor" to visit.  In our walk we explore every such
-- corridor. For example, consider the following expression:
--
-- >>> join ["John", "Paul", "George", "Ringo"] :: MazeWalk Char
-- MazeWalk "JohnhoJPauluaPGeorgegroeGRingo"
--
-- It represents a walk through the following maze (the entrance is
-- marked with \">\"):
--
-- @
--   ┌────┬──────┐
--   │L U │ N G O│
--   ├─┤A ┴ I┌───┘
--  > J P G R│
-- ┌─┘O ┬ E ┌┘
-- │N H │ O └──┐
-- └────┤ R G E│
--      └──────┘
-- @
--
-- First, we take the J-O-H-N path. When we reach its end, we turn
-- around and go back to J, so our walk to this point is J-O-H-N-H-O-J
-- (hence the connection with palindromes).  Then, we explore the
-- P-A-U-L corridor, adding P-A-U-L-U-A-P to our walk. The same
-- applies to G-E-O-R-G-E. But when at the end of R-I-N-G-O, we have
-- explored the entire maze, so our walk is done (this is why we do
-- not palindromize the last element).
--
newtype MazeWalk a = MazeWalk { unMazeWalk :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (MazeWalk Char)

instance Applicative MazeWalk where
  pure  = return
  (<*>) = ap

instance Monad MazeWalk where
  return x = MazeWalk [x]
  MazeWalk xs >>= f = MazeWalk $ join $ map (unMazeWalk . f) xs 
   where
    join xss | null xss || any null xss
             = []
             | otherwise
             = concatMap palindromize (init xss) ++ last xss

instance IsList (MazeWalk a) where
  type Item (MazeWalk a) = a
  toList   = unMazeWalk
  fromList = MazeWalk
  
instance ListMonad MazeWalk

instance PointedMagma (MazeWalk a) where
  m <> t = join $ MazeWalk $ [m, t]
  eps    = MazeWalk []

instance PalindromeAlgebra (MazeWalk a)

instance FreeRBPM MazeWalk PalindromeAlgebra

-------------------------------
-- The Discrete Hybrid monad --
-------------------------------

-- | Instances should satisfy the following:
--
-- @
-- x '<>' 'eps'       ==  'eps'
-- 'eps' '<>' x       ==  x
-- (x '<>' y) '<>' z  ==  y '<>' z
-- @
class (PointedMagma a) => LeaningAlgebra a

-- | A singleton list with the last element of the argument,
-- if it exists. Otherwise, empty.
--
-- @
-- safeLast \"Roy\"  ==  \"y\"
-- safeLast []     ==  []
-- @
safeLast :: [a] -> [a]
safeLast [] = []
safeLast xs = [last xs]

-- | The Discrete Hybrid monad arises from free leaning algebras. Its
-- join is defined as:
--
-- @
-- join xss | null xss        = []
--          | null (last xss) = []
--          | otherwise       = concatMap safeLast (init xss) ++ last xss
-- @
--
-- For example:
--
-- >>> join ["Roy", "Kelton", "Orbison"] :: DiscreteHybrid Char
-- DiscreteHybrid "ynOrbison"
-- >>> join ["Roy", "", "Orbison"] :: DiscreteHybrid Char
-- DiscreteHybrid "yOrbison"
--
-- Different versions of hybrid monads originate from Renato Neves's
-- [PhD thesis](http://alfa.di.uminho.pt/~nevrenato/pdfs/thesis.pdf).
newtype DiscreteHybrid a = DiscreteHybrid { unDiscreteHybrid :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (DiscreteHybrid Char)

instance Applicative DiscreteHybrid where
  pure  = return
  (<*>) = ap

instance Monad DiscreteHybrid where
  return x = DiscreteHybrid [x]
  DiscreteHybrid xs >>= f = DiscreteHybrid $ join $ map (unDiscreteHybrid . f) xs 
   where
    join xss | null xss        = []
             | null (last xss) = []
             | otherwise       = concatMap safeLast (init xss) ++ last xss

instance IsList (DiscreteHybrid a) where
  type Item (DiscreteHybrid a) = a
  toList   = unDiscreteHybrid
  fromList = DiscreteHybrid
  
instance ListMonad DiscreteHybrid

instance PointedMagma (DiscreteHybrid a) where
  m <> t = join $ DiscreteHybrid $ [m, t]
  eps    = DiscreteHybrid []

instance LeaningAlgebra (DiscreteHybrid a)

instance FreeRBPM DiscreteHybrid LeaningAlgebra

---------------------------
-- The List Unfold monad --
---------------------------

-- | A skewed algebra allows only right-nested composition of the
-- binary operation. Every other expression is equal to 'eps'.
--
-- @
-- x '<>' 'eps'       ==  'eps'
-- 'eps' '<>' x       ==  'eps'
-- (x '<>' y) '<>' z  ==  'eps'
-- @
class (PointedMagma a) => SkewedAlgebra a

-- | The List Unfold monad arises from free skewed algebras. It
-- implements a form of nondeterminism similar to the usual list
-- monad, but new choices may arise only in the last element (so the
-- bind operation can only rename other elements), essentially
-- unfolding a list. If new choices arise in the "init" of the list,
-- the entire computation fails. Also, failure is always global. The
-- join operation is defined as follows:
--
-- @
-- join xss | null xss                        = []
--          | any null xss                    = []
--          | any (not . isSingle) (init xss) = []
--          | otherwise                       = concat xss
-- @
--
-- For example:
--
-- >>> [1,1,1,4] >>= \x -> [1..x] :: ListUnfold Int
-- ListUnfold [1,1,1,1,2,3,4]
-- >>> [1,2,1,4] >>= \x -> [1..x] :: ListUnfold Int
-- ListUnfold []
-- >>> [1,0,1,4] >>= \x -> [1..x] :: ListUnfold Int
-- ListUnfold []
newtype ListUnfold a = ListUnfold { unListUnfold :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (ListUnfold Char)

instance Applicative ListUnfold where
  pure  = return
  (<*>) = ap

instance Monad ListUnfold where
  return x = ListUnfold [x]
  ListUnfold xs >>= f = ListUnfold $ join $ map (unListUnfold . f) xs 
   where
    join xss | null xss || any null xss
             = []
             | any (not . isSingle) (init xss)
             = []
             | otherwise
             = concat xss

instance IsList (ListUnfold a) where
  type Item (ListUnfold a) = a
  toList   = unListUnfold
  fromList = ListUnfold
  
instance ListMonad ListUnfold

instance PointedMagma (ListUnfold a) where
  m <> t = join $ ListUnfold $ [m, t]
  eps    = ListUnfold []

instance SkewedAlgebra (ListUnfold a)

instance FreeRBPM ListUnfold SkewedAlgebra

-----------------------
-- The Stutter monad --
-----------------------

-- | A stutter algebra (for a given natural number @n@) is a pointed
-- magma that satisfies the following equations:
--
-- @
-- x '<>' 'eps'       ==  'foldr1' ('<>') ('replicate' (n + 2) x)
-- 'eps' '<>' x       ==  'eps'  
-- (x '<>' y) '<>' z  ==  'eps'
-- @
class (KnownNat n, PointedMagma a) => StutterAlgebra n a

-- | Repeat the last element on the list @n@ additional times, that is:
--
-- @
-- replicateLast n [] = []
-- replicateLast n xs = xs ++ replicate n (last xs)
-- @
replicateLast :: Int -> [a] -> [a]
replicateLast _ [] = []
replicateLast n xs = xs ++ replicate n (last xs)

-- | The Stutter monad arises from free stutter algebras. Its join is
-- a concat of the longest prefix consisting only of singletons with a
-- \"stutter\" on the last singleton (that is, the last singleton is
-- additionally repeated @n+1@ times for an @n@ fixed in the type). It
-- doesn't stutter only when the init consists only of singletons and
-- the last list is non-empty. The join can thus be defined as follows
-- (omitting the conversion of the type-level 'Nat' @n@ to a run-time
-- value):
--
-- @
-- join xss | null xss
--          = []
--          | any (not . isSingle) (init xss) || null (last xss)
--          = replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
--          | otherwise
--          = concat xss
-- @
--
-- The 'Stutter' monad is quite similar to 'ListUnfold'. The
-- difference is that when the latter fails (that is, its join results
-- in an empty list), the former stutters on the last singleton.
--
-- Examples:
--
-- >>> join ["1", "2", "buckle", "my", "shoe"] :: Stutter 5 Char
-- Stutter "12222222"
-- >>> join ["1", "2", "buckle"] :: Stutter 5 Char
-- Stutter "12buckle"
-- >>> join ["1", "2", "", "my", "shoe"] :: Stutter 5 Char
-- Stutter "12222222"
newtype Stutter (n :: Nat) a = Stutter { unStutter :: [a] }
 deriving (Functor, Show, Eq)

deriving instance (KnownNat n) => IsString (Stutter n Char)

instance (KnownNat n) => Applicative (Stutter n) where
  pure  = return
  (<*>) = ap

instance (KnownNat n) => Monad (Stutter n) where
  return x = Stutter [x]
  Stutter xs >>= f = Stutter $ join $ map (unStutter . f) xs
   where
    join xss | null xss
             = []
             | any (not . isSingle) (init xss) || null (last xss)
             = let n = fromIntegral $ natVal (Proxy :: Proxy n)
               in  replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
             | otherwise
             = concat xss

instance (KnownNat n) => IsList (Stutter n a) where
  type Item (Stutter n a) = a
  toList   = unStutter
  fromList = Stutter 

instance (KnownNat n) => ListMonad (Stutter n) 

instance (KnownNat n) => PointedMagma (Stutter n a) where
  m <> t = join $ Stutter $ [m, t]
  eps    = Stutter []

instance (KnownNat n) => StutterAlgebra n (Stutter n a)

instance (KnownNat n) => FreeRBPM (Stutter n) (StutterAlgebra n)

------------------------------
-- The Stutter-Keeper monad --
------------------------------

-- | A stutter-keeper algebra (for a given natural number @n@) is a pointed
-- magma that satisfies the following equations:
--
-- @
-- x '<>' 'eps'       ==  'foldr1' ('<>') ('replicate' (n + 2) x)
-- 'eps' '<>' x       ==  'eps'  
-- (x '<>' y) '<>' z  ==  x '<>' y
-- @
class (KnownNat n, PointedMagma a) => StutterKeeperAlgebra n a

-- | The stutter-keeper monad arises from free stutter-keeper
-- algebras. Its join stutters (as in the 'Stutter' monad) if the
-- first non-singleton list in empty. Otherwise, it keeps the
-- singleton prefix, and keeps the first non-singleton list. The join
-- can thus be defined as follows (omitting the conversion of the
-- type-level 'Nat' @n@ to a run-time value):
--
-- @
-- join xss | null xss
--          = []
--          | null (head (dropWhile isSingle (init xss) ++ [last xss]))
--          = replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
--          | otherwise
--          = map head (takeWhile isSingle (init xss))
--             ++ head (dropWhile isSingle (init xss) ++ [last xss])
-- @
--
-- Examples:
--
-- >>> join ["1", "2", "buckle", "my", "shoe"] :: StutterKeeper 5 Char
  -- StutterKeeper "12buckle"
-- >>> join ["1", "2", "buckle"] :: StutterKeeper 5 Char
-- StutterKeeper "12buckle"
-- >>> join ["1", "2", "", "my", "shoe"] :: StutterKeeper 5 Char
-- StutterKeeper "12222222"
newtype StutterKeeper (n :: Nat) a = StutterKeeper { unStutterKeeper :: [a] }
 deriving (Functor, Show, Eq)

deriving instance (KnownNat n) => IsString (StutterKeeper n Char)

instance (KnownNat n) => Applicative (StutterKeeper n) where
  pure  = return
  (<*>) = ap

instance (KnownNat n) => Monad (StutterKeeper n) where
  return x = StutterKeeper [x]
  StutterKeeper xs >>= f = StutterKeeper $ join $ map (unStutterKeeper . f) xs
   where
    join xss | null xss
             = []
             | null (head (dropWhile isSingle (init xss) ++ [last xss]))
             = let n = fromIntegral $ natVal (Proxy :: Proxy n)
               in  replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
             | otherwise
             = map head (takeWhile isSingle (init xss))
                ++ head (dropWhile isSingle (init xss) ++ [last xss])

instance (KnownNat n) => IsList (StutterKeeper n a) where
  type Item (StutterKeeper n a) = a
  toList   = unStutterKeeper
  fromList = StutterKeeper 

instance (KnownNat n) => ListMonad (StutterKeeper n) 

instance (KnownNat n) => PointedMagma (StutterKeeper n a) where
  m <> t = join $ StutterKeeper $ [m, t]
  eps    = StutterKeeper []

instance (KnownNat n) => StutterKeeperAlgebra n (StutterKeeper n a)

instance (KnownNat n) => FreeRBPM (StutterKeeper n) (StutterKeeperAlgebra n)

------------------------------
-- The StutterStutter monad --
------------------------------

-- | A stutter-stutter algebra (for given natural numbers @n@ and @m@)
-- is a pointed magma that satisfies the following equations:
--
-- @
-- x '<>' 'eps'       ==  'foldr1' ('<>') ('replicate' (n + 2) x)
-- 'eps' '<>' x       ==  'eps'  
-- (x '<>' y) '<>' z  ==  'foldr1' ('<>') ('replicate' (m + 2) x)
-- @
class (KnownNat n, KnownNat m, PointedMagma a) => StutterStutterAlgebra n m a

-- | The stutter-stutter monad arises from free stutter-stutter
-- algebras. It is similar to 'StutterKeeper', but instead of keeping
-- the first non-singleton list, it stutters on its first element
-- (unless the first non-singleton list is also the last list, in
-- which case it is kept in the result). The join can thus be defined
-- as follows (omitting the conversion of the type-level nats to
-- run-time values):
--
-- @
-- join xss | null xss
--          = []
--          | null (head (dropWhile isSingle (init xss) ++ [last xss]))
--          = replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
--          | any (not . isSingle) (init xss) || null (last xss)
--          = concat (takeWhile isSingle (init xss))
--             ++ replicate (m + 2) (head (head (dropWhile isSingle (init xss))))
--          | otherwise
--          = concat xss
-- @
--
-- Examples:
--
-- >>> join ["1", "2", "buckle", "my", "shoe"] :: StutterStutter 5 10 Char
-- StutterStutter "12bbbbbbbbbbbb"
-- >>> join ["1", "2", "buckle"] :: StutterStutter 5 10 Char
-- StutterStutter "12buckle"
-- >>> join ["1", "2", "", "my", "shoe"] :: StutterStutter 5 10 Char
-- StutterStutter "12222222"
newtype StutterStutter (n :: Nat) (m :: Nat) a = StutterStutter { unStutterStutter :: [a] }
 deriving (Functor, Show, Eq)

deriving instance (KnownNat n, KnownNat m) => IsString (StutterStutter n m Char)

instance (KnownNat n, KnownNat m) => Applicative (StutterStutter n m) where
  pure  = return
  (<*>) = ap

instance (KnownNat n, KnownNat m) => Monad (StutterStutter n m) where
  return x = StutterStutter [x]
  StutterStutter xs >>= f = StutterStutter $ join $ map (unStutterStutter . f) xs
   where
    join xss | null xss
             = []
             | null (head (dropWhile isSingle (init xss) ++ [last xss]))
             = let n = fromIntegral $ natVal (Proxy :: Proxy n)
               in  replicateLast (n + 1) (concat $ takeWhile isSingle (init xss))
             | any (not . isSingle) (init xss) || null (last xss)
             = let m = fromIntegral $ natVal (Proxy :: Proxy m)
               in  concat (takeWhile isSingle (init xss))
                    ++ replicate (m + 2) (head (head (dropWhile isSingle (init xss))))
             | otherwise
             = concat xss

instance (KnownNat n, KnownNat m) => IsList (StutterStutter n m a) where
  type Item (StutterStutter n m a) = a
  toList   = unStutterStutter
  fromList = StutterStutter 

instance (KnownNat n, KnownNat m) => ListMonad (StutterStutter n m) 

instance (KnownNat n, KnownNat m) => PointedMagma (StutterStutter n m a) where
  m <> t = join $ StutterStutter $ [m, t]
  eps    = StutterStutter []

instance (KnownNat n, KnownNat m)
  => StutterStutterAlgebra n m (StutterStutter n m a)

instance (KnownNat n, KnownNat m)
  => FreeRBPM (StutterStutter n m) (StutterStutterAlgebra n m)

-- $numerical_monoids
-- 
-- A /numerical monoid/ is a subset of the set of natural numbers that
-- contains 0 and is closed under addition. That is,
-- \(M \subseteq \mathbb N\)
-- is a numerical monoid if
--
--  * \(0 \in M\),
--
--  * if \(x,y \in M\), then \(x+y \in M\).
--
-- Representing a numerical monoid \(M\) using its characteristic
-- function @m :: Int -> Bool@ (revealing if a given number belongs to
-- \(M\)), we can define a monad as follows:
--
-- @
-- join xss | isSingle xss || all isSingle xss                         = concat xss
--          | null xss || any null xss                                 = []
--          | m (length xss - 1) && all (\\xs -> m $ length xs - 1) xss = concat xss
--          | otherwise                                                = []
-- @
--
-- Below, we first show a couple of concrete examples of monads
-- arising from particular numerical monoids, and then the general
-- version via a set of generators.

--------------------
-- The Mini monad --
--------------------

-- | The Mini monad is, in a sense, a minimal list monad, meaning that
-- its join fails (= results in an empty list) for all values except
-- the ones that appear in the unit laws (i.e., a singleton or a list
-- of singletons):
--
-- @
-- join xss | isSingle xss || all isSingle xss = concat xss
--          | otherwise                        = []
-- @
--
-- For example:
--
-- >>> join ["HelloThere"] :: Mini Char
-- Mini "HelloThere"
-- >>> join ["Hello", "There"] :: Mini Char
-- Mini ""
-- >>> join ["H", "T"] :: Mini Char
-- Mini "HT"
--
-- This monad arises from the numerical monoid \(\{0\}\).
--
-- It does not arise from a subclass of 'PointedMagma' (or any
-- algebraic theory with a finite number of operations for that 
-- matter).
newtype Mini a = Mini { unMini :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (Mini Char)

instance Applicative Mini where
  pure  = return
  (<*>) = ap

instance Monad Mini where
  return x = Mini [x]
  Mini xs >>= f = Mini $ join $ map (unMini . f) xs 
   where
    join xss | isSingle xss || all isSingle xss = concat xss
             | otherwise                        = []

instance IsList (Mini a) where
  type Item (Mini a) = a
  toList   = unMini
  fromList = Mini

instance ListMonad Mini

-------------------
-- The Odd monad --
-------------------

-- | The join of the Odd monad is a concat of the inner lists provided
-- there is an odd number of them, and that all of them are of odd
-- length themselves. Otherwise (modulo cases needed for the unit
-- laws), it returns an empty list.
--
-- @
-- join xss | isSingle xss || all isSingle xss  = concat xss
--          | odd (length xss)
--             && all (odd . length) xss        = concat xss 
--          | otherwise                         = []
-- @
--
-- For example:
--
-- >>> join ["Elvis", "Presley"] :: Odd Char
-- Odd ""
-- >>> join ["Elvis", "Aaron", "Presley"] :: Odd Char
-- Odd "ElvisAaronPresley"
-- >>> join ["Roy", "Kelton", "Orbison"] :: Odd Char
-- Odd ""
--
-- It arises from the numerical monoid \(\{0,2,4,6,\ldots\}\). -- Note that the sum of even numbers is always even, which cannot be said of odd numbers!
--
--
-- At the moment, it is unclear whether it comes from a finite
-- algebraic theory.
newtype Odd a = Odd { unOdd :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (Odd Char)

instance Applicative Odd where
  pure  = return
  (<*>) = ap

instance Monad Odd where
  return x = Odd [x]
  Odd xs >>= f = Odd $ join $ map (unOdd . f) xs 
   where
    join xss | isSingle xss || all isSingle xss
             = concat xss
             | odd (length xss) && all (odd . length) xss
             = concat xss
             | otherwise
             = []

instance IsList (Odd a) where
  type Item (Odd a) = a
  toList   = unOdd
  fromList = Odd

instance ListMonad Odd

------------------------
-- The At Least monad --
------------------------

-- | The join of the @AtLeast n@ monad is a concat of the inner lists
-- provided there are at least @n@ inner lists and all the inner lists
-- are of length at least @n@ or 1.
--
-- The join can thus be defined as follows (omitting the conversion of
-- the type-level nats to run-time values):
--
-- @
-- join xss | isSingle xss || all isSingle xss  = concat xss
--          | otherwise = let ok :: forall x. [x] -> Bool
--                            ok xs = length xs >= n || length xs == 1
--                        in if ok xss && all ok xss
--                             then concat xss
--                             else []
-- @
--
-- For example:
--
-- >>> join ["Strawberry", "Fields", "Forever"] :: AtLeast 3 Char
-- AtLeast "StrawberryFieldsForever"
-- >>> join ["All", "You", "Need", "Is", "Love"] :: AtLeast 3 Char
-- AtLeast []
-- >>> join ["I", "Want", "You"] :: AtLeast 3 Char
-- AtLeast "IWantYou"
-- >>> join ["I", "Am", "The", "Walrus"] :: AtLeast 3 Char
-- AtLeast []
--
-- The monad @AtLeast n@ arises from the numerical monoid \(\{0, n-1, n, n+1, n+2,\ldots\}\).
newtype AtLeast (n :: Nat) a = AtLeast { unAtLeast :: [a] }
 deriving (Functor, Show, Eq)

deriving instance (KnownNat n) => IsString (AtLeast n Char)

instance (KnownNat n) => Applicative (AtLeast n) where
  pure  = return
  (<*>) = ap

instance (KnownNat n) => Monad (AtLeast n) where
  return x = AtLeast [x]
  AtLeast xs >>= f = AtLeast $ join $ map (unAtLeast . f) xs 
   where
    join xss | isSingle xss     = concat xss
             | all isSingle xss = concat xss
             | otherwise        = let n = fromIntegral $ natVal (Proxy :: Proxy n)
                                      ok :: forall x. [x] -> Bool
                                      ok xs = length xs >= n || length xs == 1
                                  in if ok xss && all ok xss
                                       then concat xss
                                       else []

instance (KnownNat n) => IsList (AtLeast n a) where
  type Item (AtLeast n a) = a
  toList   = unAtLeast
  fromList = AtLeast

instance (KnownNat n) => ListMonad (AtLeast n)

--------------------------------
-- The Numerical Monoid monad --
--------------------------------

-- | An interesting property of numerical monoids is that they are
-- always finitely generated. This means that every numerical monoid
-- can be constructed by starting out with a finite set of nautral
-- numbers and closing it under addition. For example, the set
-- \(\{0,2,4,6,\ldots\}\) is generated by \(\{2\}\), because every
-- even number is of the form \(2k\) for some \(k\).
--
-- The class @'NumericalMonoidGenerators'@ represents a set of
-- generators given as a type-level list of nats.
class NumericalMonoidGenerators (ns :: [Nat]) where
  -- | Check if a given number is in the numerical monoid generatted
  -- by @ns@. It is the characteristic function of the generated
  -- numerical monoid.
  isInNumericalMonoid :: Int -> Bool

instance NumericalMonoidGenerators '[] where
  isInNumericalMonoid = (== 0)

instance (KnownNat g, NumericalMonoidGenerators gs) => NumericalMonoidGenerators (g ': gs) where
  isInNumericalMonoid x
     | x < 0     = False
     | otherwise =  isInNumericalMonoid @gs x
                 || x >= g && g > 0 && isInNumericalMonoid @(g ': gs) (x - g)
   where
    g = fromIntegral $ natVal (Proxy :: Proxy g)

-- | The monad generated by the numerical monoid generated by a set of generators @ns@.
--
-- @
-- join xss | null xss || any null xss                                     = []
--          | isInNumericalMonoid \@ns (length xss - 1)
--             && all (\\xs -> isInNumericalMonoid \@ns (length xs - 1)) xss = concat xss
--          | otherwise                                                    = []
-- @
--
-- In particular:
--
-- * @'Mini'@ is @NumericalMonoidMonad '[]@,
--
-- * @'Odd'@ is @NumericalMonoidMonad '[2]@,
--
-- * @'AtLeast' n@ is @NumericalMonoidMonad '[n-1, n, n+1, ..., 2n-3]@.
newtype NumericalMonoidMonad (ns :: [Nat]) a = NumericalMonoidMonad { unNumericalMonoidMonad :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (NumericalMonoidMonad ns Char)

instance (NumericalMonoidGenerators ns) => Applicative (NumericalMonoidMonad ns) where
  pure  = return
  (<*>) = ap

instance (NumericalMonoidGenerators ns) => Monad (NumericalMonoidMonad ns) where
  return x = NumericalMonoidMonad [x]
  NumericalMonoidMonad xs >>= f = NumericalMonoidMonad $ join $ map (unNumericalMonoidMonad . f) xs 
   where
    join xss | isSingle xss || all isSingle xss                          = concat xss
             | null xss || any null xss                                  = []
             | isInNumericalMonoid @ns (length xss - 1)
             && all (\xs -> isInNumericalMonoid @ns (length xs - 1)) xss = concat xss
             | otherwise                                                 = []

instance IsList (NumericalMonoidMonad ns a) where
  type Item (NumericalMonoidMonad ns a) = a
  toList   = unNumericalMonoidMonad
  fromList = NumericalMonoidMonad

instance (NumericalMonoidGenerators ns) => ListMonad (NumericalMonoidMonad ns)

-----------------------------------
-- The Continuum-of-Monads monad --
-----------------------------------

-- $continuum-monads
--
-- The "Continuum of Monads" monad construction was introduced in
-- [this
-- paper](https://cla.tcs.uj.edu.pl/pdfs/McDermott-Pirog-Uustalu-Abstract.pdf)
-- to show that the set of list monads is a
-- [continuum](https://en.wikipedia.org/wiki/Cardinality_of_the_continuum)
-- (that is, that there are as many list monads in the category of
-- sets as there are real numbers, and more than there are natural
-- numbers).
--
-- We define a family of monads @'ContinuumOfMonads'@, which is
-- parameterised by a subset of the set of natural numbers
-- (@'SetOfNats'@).

-- | The @SetOfNats@ class defines a subset of the set of natural
-- numbers (from which we are actually interested in odd numbers
-- only).
--
-- For example:
--
-- >>> filter (elemOf @"Primes") [0..100]
-- [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
-- >>> filter (elemOf @"Fib") [0..100]
-- [0,1,2,3,5,8,13,21,34,55,89]
class SetOfNats (a :: Symbol) where
  -- | The characteristic function of the defined set.
  elemOf :: Int -> Bool

-- Example sets:

primes :: [Int]
primes = sieve [2..] where sieve ps = head ps : sieve [x | x <- tail ps, x `mod` head ps > 0]

-- | The set of prime numbers.
instance SetOfNats "Primes" where elemOf n = n `elem` takeWhile (<= n) primes

fib :: [Int]
fib = 0 : 1 : zipWith (+) fib (tail fib)

-- | The set of Fibonacci numbers.
instance SetOfNats "Fib" where elemOf n = n `elem` takeWhile (<= n) fib

-- | The @'ContinuumOfMonads'@ monad is parameterised by a set of
-- natural numbers (@'SetOfNats'@). This means that the user can write a
-- monad as follows:
--
-- >>> :k ContinuumOfMonads Primes
-- ContinuumOfMonads Primes :: * -> *
--
-- One can define different sets by instantiating the @'SetOfNats'@ class.
--
-- The @join@ of @ContinuumOfMonads s@ is defined as follows:
--
-- @
-- join xss       | isSingle xss    || all isSingle xss      = concat xss
--                | null xss        || any null xss          = []
-- join [[x], xs] | odd (length xs) && elemOf @s (length xs) = x : xs
-- join _                                                    = []
-- @
newtype ContinuumOfMonads (s :: Symbol) a = ContinuumOfMonads { unContinuumOfMonads :: [a] }
 deriving (Functor, Show, Eq)

deriving instance IsString (ContinuumOfMonads s Char)

instance (SetOfNats s) => Applicative (ContinuumOfMonads s) where
  pure  = return
  (<*>) = ap

instance (SetOfNats s) => Monad (ContinuumOfMonads s) where
  return x = ContinuumOfMonads [x]
  ContinuumOfMonads xs >>= f = ContinuumOfMonads $ join $ map (unContinuumOfMonads . f) xs 
   where
    join xss | isSingle xss || all isSingle xss               = concat xss
             | null xss || any null xss                       = []
    join [[x], xs] | odd (length xs) && elemOf @s (length xs) = x : xs
    join _                                                    = []

instance IsList (ContinuumOfMonads s a) where
  type Item (ContinuumOfMonads s a) = a
  toList   = unContinuumOfMonads
  fromList = ContinuumOfMonads

instance (SetOfNats s) => ListMonad (ContinuumOfMonads s)

------------------------------------
-- The Short Stutter-Keeper monad --
------------------------------------

-- | This monad works just like the 'StutterKeeper' monad but it takes
-- a prefix of the result of join of length @p+2@ (unless the unit
-- laws say otherwise). Thus, its join is defined as follows (omitting
-- the conversion of the type-level 'Nat' @p@ to a run-time value):
--
-- @
-- join xss | isSingle xss     = concat xss
--          | all isSingle xss = concat xss
--          | otherwise        = take (p + 2) $ toList
--                                 ((Control.Monad.join $ StutterKeeper $ fmap StutterKeeper xss)
--                                   :: StutterKeeper n _)
-- @
--
-- For example:
--
-- >>> join ["1", "2", "buckle", "my", "shoe"] :: ShortStutterKeeper 5 2 Char
-- ShortStutterKeeper "12bu"
-- >>> join ["1", "2", "buckle"] :: ShortStutterKeeper 5 2 Char
-- ShortStutterKeeper "12bu"
-- >>> join ["1", "2", "", "my", "shoe"] :: ShortStutterKeeper 5 2 Char
-- ShortStutterKeeper "1222"
--
-- Compare the 'Control.Monad.List.NonEmpty.Exotic.ShortFront' monad
-- on non-empty lists.
newtype ShortStutterKeeper (n :: Nat) (p :: Nat) a =
  ShortStutterKeeper { unShortStutterKeeper :: [a] }
 deriving (Functor, Show, Eq)

deriving instance (KnownNat n, KnownNat p) => IsString (ShortStutterKeeper n p Char)

instance (KnownNat n, KnownNat p) => Applicative (ShortStutterKeeper n p) where
  pure  = return
  (<*>) = ap

instance (KnownNat n, KnownNat p) => Monad (ShortStutterKeeper n p) where
  return x = ShortStutterKeeper [x]
  ShortStutterKeeper xs >>= f = ShortStutterKeeper $ join $ map (unShortStutterKeeper . f) xs
   where
    join :: forall x. [[x]] -> [x]
    join xss | isSingle xss = concat xss
             | all isSingle xss = concat xss
             | otherwise =
                  let p = fromIntegral $ natVal (Proxy :: Proxy p)
                  in  take (p + 2) $ toList
                      ((Control.Monad.join $ StutterKeeper $ fmap StutterKeeper xss)
                        :: StutterKeeper n x)

instance (KnownNat n, KnownNat p) => IsList (ShortStutterKeeper n p a) where
  type Item (ShortStutterKeeper n p a) = a
  toList   = unShortStutterKeeper
  fromList = ShortStutterKeeper 

instance (KnownNat n, KnownNat p) => ListMonad (ShortStutterKeeper n p) 
