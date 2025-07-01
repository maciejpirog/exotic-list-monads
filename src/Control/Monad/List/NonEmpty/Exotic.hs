{-# LANGUAGE Trustworthy #-} -- can't use Safe due to IsList instance
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedLists #-}


-- {-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Control.Monad.List.NonEmpty.Exotic
-- Description : Non-standard monads on the non-empty list functor
-- Copyright   : (c) Dylan McDermott, Maciej Piróg, Tarmo Uustalu, 2020
-- License     : MIT
-- Maintainer  : maciej.adam.pirog@gmail.com
-- Stability   : experimental
-- Portability : portable
--
-- The usual list monad is only one of infinitely many ways to turn
-- the 'NonEmpty.NonEmpty' (list) functor into a monad. This module
-- collects a number of such exotic "non-empty list monads".  Most of
-- them have been introduced in the paper [Degrading
-- Lists](https://raw.githubusercontent.com/maciejpirog/exotic-list-monads/master/degrading-lists.pdf)
-- by Dylan McDermott, Maciej Piróg, Tarmo Uustalu (PPDP 2020).
--
-- __Notes:__
--
-- * Types marked with \"(?)\" have not been formally verified to be
-- monads (yet),  though they were thoroughly tested with billions of
-- QuickCheck tests.
--
-- * Monads in this module are presented in terms of @join@ rather
-- than '>>=', while 'return' is singleton, unless stated otherwise
-- for a particular monad (e.g., 'HeadTails', 'HeadsTail', or
-- 'IdXList').
--
-- * For readability, code snippets in this documentation assume the
-- @OverloadedLists@ and @OverloadedStrings@ extensions, which allow
-- us to omit some @newtype@ constructors. Example definitions of
-- joins of monads always skip the @newtype@ constructors, that is,
-- assume '>>=' is always defined as follows for a particular local
-- @join@.
--
-- @
-- m '>>=' f = 'wrap' $ join $ 'fmap' ('unwrap' . f) $ 'unwrap' m
--  where
--   join = ...
-- @
--
-- * Sometimes it is more readable to define the join in terms of
-- possibly-empty lists. In such a case, we call the local function
-- @joinList@:
--
-- @
-- m '>>=' f = 'wrap' $ 'GHC.Exts.fromList' $ joinList $ 'map' ('GHC.Exts.toList' . 'unwrap' . f) $ 'GHC.Exts.toList' $ 'unwrap' m
--  where
--   joinList = ...
-- @
--
-- 
-- * The definitions of monads are optimized for readability and not
-- run-time performance. This is because the monads in this module
-- don't seem to be of any practical use, they are more of a
-- theoretical curiosity.


module Control.Monad.List.NonEmpty.Exotic
  (
  -- * Non-empty monads in general

    IsNonEmpty(..)
  , NonEmptyMonad(..)
    
  -- ** More on non-empty lists

  , isSingle
  , splitSnoc
  , nonEmptyConcat
  , (+++)
  , nonEmptyAll
  , nonEmptyAny
    
  -- * Monads from magmas

  -- $magmas
  
  , Magma(..)
  , FreeRBM(..)

  -- ** The Keeper monad

  , XY
  , Keeper(..)
  
  -- ** The Non-Empty Discrete Hybrid monad

  , YZ
  , DiscreteHybridNE(..)
  
  -- ** The Non-Empty Discrete Op-Hybrid monad

  , XZ
  , OpDiscreteHybridNE(..)

  -- ** The Non-Empty Maze Walk monad

  , PalindromeMagma
  , MazeWalkNE(..)

  -- ** The Non-Empty Stutter monad

  , StutterMagma
  , StutterNE(..)
  
  -- * Other monads with finite presentation

  -- $others
  
  -- ** The Head-Tails monad

  , HeadTailTail(..)
  , HeadTails(..)
  , foldHeadTails

  -- ** The Heads-Tail monad

  , HeadHeadTail(..)
  , HeadsTail(..)
  , foldHeadsTail
  
  -- * Other monads

  -- ** The ΑΩ monad (?)

  , AlphaOmega(..)

  -- ** The ΑⁿΩᵏ monad (?)

  , AlphaNOmegaK(..)

  -- * Constructions on non-empty monads

  -- ** The dual non-empty list monad

  , DualNonEmptyMonad(..)

  -- ** The @Identity@ ⨉ @List@ monad

  , IdXList(..)

  -- ** Short-front monads

  , HasShortFront
  , ShortFront(..)

  -- ** Short-rear monads

  , HasShortRear
  , ShortRear(..)
  
  ) where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Prelude hiding ((<>))
import Control.Monad (ap, join)
import Data.Kind (Type)
import GHC.Exts (IsList(..), IsString(..), Constraint)
-- import GHC.TypeLits
import GHC.TypeNats
import Data.Proxy
import qualified Data.Semigroup (Semigroup)
import Control.Monad.List.Exotic (ListMonad, palindromize)
import qualified Control.Monad.List.Exotic as List.Exotic (ListMonad(..))

---------------------------
-- Non-empty list monads --
---------------------------

-- | This class collects types that are isomorphic to non-empty
-- lists. It mimics the 'GHC.Exts.IsList' class.
class IsNonEmpty l where
  type ItemNE l
  fromNonEmpty :: NonEmpty (ItemNE l) -> l
  toNonEmpty   :: l -> NonEmpty (ItemNE l)

instance IsNonEmpty (NonEmpty a) where
  type ItemNE (NonEmpty a) = a
  fromNonEmpty = id
  toNonEmpty   = id

-- | In this module, a \"non-empty monad\" is a monad in which the
-- underlying functor is isomorphic to 'Data.List.NonEmpty.NonEmpty'.
class (Monad m) => NonEmptyMonad m where

  wrap   :: NonEmpty a -> m a
  default wrap   :: (IsNonEmpty (m a), ItemNE (m a) ~ a) => NonEmpty a -> m a
  wrap = fromNonEmpty
  
  unwrap :: m a -> NonEmpty a
  default unwrap :: (IsNonEmpty (m a), ItemNE (m a) ~ a) => m a -> NonEmpty a
  unwrap = toNonEmpty

instance NonEmptyMonad NonEmpty

-- | Split a non empty list to reveal the last element.
splitSnoc :: NonEmpty a -> ([a], a)
splitSnoc (x :| []) = ([], x)
splitSnoc (x :| xs) = (x : init xs, last xs)

-- | Check if a list is a singleton.
isSingle :: NonEmpty a -> Bool
isSingle (_ :| []) = True
isSingle _         = False

-- | 'concat' for non-empty lists.
nonEmptyConcat :: NonEmpty (NonEmpty a) -> NonEmpty a
nonEmptyConcat = join

-- | '++' for non-empty lists.
(+++) :: NonEmpty a -> NonEmpty a -> NonEmpty a
a +++ b = nonEmptyConcat [a, b]  -- OverloadedLists

-- | 'all' for non-empty lists.
nonEmptyAll :: (a -> Bool) -> NonEmpty a -> Bool
nonEmptyAll p (x :| xs) = p x && all p xs

-- | 'any' for non-empty lists.
nonEmptyAny :: (a -> Bool) -> NonEmpty a -> Bool
nonEmptyAny p (x :| xs) = p x || any p xs

------------
-- Magmas --
------------

-- $magmas
--
-- This section contains monads that come about from free algebras of
-- theories with one binary operation, that is, subcalsses of 'Magma'
-- with no additional methods, but additional equations.

-- | A very simple algebraic theory with one binary operations and no
-- equations.
class Magma a where
  (<>) :: a -> a -> a

-- | The name of the class stands for __free right-braketed__
-- (subclass of) __magma__. (compare
-- 'Control.Monad.List.Exotic.FreeRBPM' for more detailed
-- explanation).
--
-- We consider theories @c@ with one equation of the following shape:
--
-- @
-- (x '<>' y) '<>' z  ==  ...
-- @
--
-- and normal forms of the following shape:
--
-- @
-- x '<>' (y '<>' ( ... (z '<>' t) ... ))
-- @
--
-- An instance @FreeRBM m c@ means that the monad @m@ comes about from
-- free algebras of the theory @c@. For such monads and theories, we
-- can define the following function:
--
-- @
-- foldRBM f (toNonEmpty -> toList -> xs) = foldr1 (<>) (map f xs)
-- @
--
-- which is the unique lifting of an interpretation of generators to a
-- homomorphism (between algebras of this theory) from the list monad
-- to any algebra (an instance) of @c@.
--
-- Note that the default definition of 'foldRBM' is always the right
-- one for right-bracketed subclasses of 'Magma', so it is
-- enough to declare the relationship, for example:
--
-- @
-- instance FreeRBM 'NonEmpty' 'Data.Semigroup.Semigroup'
-- @
class (NonEmptyMonad m) => FreeRBM m (c :: Type -> Constraint) | m -> c where
  foldRBM :: (Magma a, c a) => (x -> a) -> m x -> a
  foldRBM f (unwrap -> toList -> xs) = foldr1 (<>) (map f xs)

instance FreeRBM NonEmpty Data.Semigroup.Semigroup

----------------------
-- The Keeper monad --
----------------------

-- | Instances should satisfy the following equation:
--
-- @
-- (x '<>' y) '<>' z  ==  x '<>' y
-- @
class (Magma a) => XY a

-- | The keeper monad arises from free 'XY' magmas. Its join (in terms
-- of @joinList@) is given as follows:
--
-- @
-- joinList xss = map head (takeWhile 'Control.Monad.List.Exotic.isSingle' (init xss))
--                 ++ head (dropWhile 'Control.Monad.List.Exotic.isSingle' (init xss) ++ [last xss])
-- @
--
-- Examples:
--
-- >>> toList $ unwrap (join ["a", "b", "c", "hello", "there"] :: Keeper Char)
-- "abchello"
-- >>> toList $ unwrap (join ["a", "b", "c", "hello"] :: Keeper Char)
-- "abchello"
newtype Keeper a = Keeper { unKeeper :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative Keeper where
  pure a = Keeper $ [a]  -- OverloadedLists
  (<*>)  = ap

instance Monad Keeper where
  Keeper xs >>= f =
    Keeper $ join $ NonEmpty.map (unKeeper . f) xs
   where
    join (splitSnoc -> (xss, xs)) = fromList $
      map NonEmpty.head (takeWhile isSingle xss)
       ++ toList (head (dropWhile isSingle xss ++ [xs])) -- OverloadedLists

instance IsNonEmpty (Keeper a) where
  type ItemNE (Keeper a) = a
  fromNonEmpty = Keeper
  toNonEmpty = unKeeper

instance NonEmptyMonad Keeper

instance Magma (Keeper a) where
  m <> t = join $ Keeper $ [m, t]

instance XY (Keeper a)

instance FreeRBM Keeper XY

-- The following two are needed for examples in the docs:

instance IsList (Keeper a) where
  type Item (Keeper a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance IsString (Keeper Char) where
  fromString = fromList

-----------------------------------------
-- The Non-Empty Discrete Hybrid monad --
-----------------------------------------

-- | Instances should satisfy the following equation:
--
-- @
-- (x '<>' y) '<>' z  ==  y '<>' z
-- @
class (Magma a) => YZ a

-- | The non-empty discrete hybrid monad arises from free 'YZ'
-- magmas. Its join (in terms of @joinList@) can be given as follows:
--
-- @
-- joinList xss = map last (init xss) ++ last xss
-- @
--
-- See the possibly-empty version
-- ('Control.Monad.List.Exotic.DiscreteHybrid') for more details.
newtype DiscreteHybridNE a =
  DiscreteHybridNE { unDiscreteHybridNE :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative DiscreteHybridNE where
  pure a = DiscreteHybridNE $ [a]  -- OverloadedLists
  (<*>)  = ap

instance Monad DiscreteHybridNE where
  DiscreteHybridNE xs >>= f =
    DiscreteHybridNE $ join $ NonEmpty.map (unDiscreteHybridNE . f) xs
   where
    join (splitSnoc -> (xss, xs)) = fromList (map NonEmpty.last xss ++ toList xs)
  
instance IsNonEmpty (DiscreteHybridNE a) where
  type ItemNE (DiscreteHybridNE a) = a
  fromNonEmpty = DiscreteHybridNE
  toNonEmpty = unDiscreteHybridNE

instance NonEmptyMonad DiscreteHybridNE

instance Magma (DiscreteHybridNE a) where
  m <> t = join $ DiscreteHybridNE $ [m, t]

instance YZ (DiscreteHybridNE a)

instance FreeRBM DiscreteHybridNE YZ

--------------------------------------------
-- The Non-Empty Discrete Op-Hybrid monad --
-------------------------------------------

-- | Instances should satisfy the following equation:
--
-- @
-- (x '<>' y) '<>' z  ==  x '<>' z
-- @
class (Magma a) => XZ a

-- | The non-empty discrete op-hybrid monad arises from free 'XZ'
-- magmas. It is dual to the 'DiscreteHybridNE' monad (but in a
-- different dimension than 'DualNonEmptyMonad'). Its join (in terms
-- of @joinList@) can be given as follows:
--
-- @
-- joinList xss = map head (init xss) ++ last xss
-- @
--
-- Examples:
--
-- >>> toList $ unwrap (join ["John", "Ronald", "Reuel", "Tolkien"] :: OpDiscreteHybridNE Char)
-- "JRRTolkien"
--
-- Surprisingly, while the 'DiscreteHybridNE' monad has a counterpart
-- for possibly-empty lists
-- ('Control.Monad.List.Exotic.DiscreteHybrid'), the would-be
-- counterpart of @OpDiscreteHybridNE@ obtained by taking first
-- elements in the init is __not__ a monad.
newtype OpDiscreteHybridNE a =
  OpDiscreteHybridNE { unOpDiscreteHybridNE :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative OpDiscreteHybridNE where
  pure a = OpDiscreteHybridNE $ [a]  -- OverloadedLists
  (<*>)  = ap

instance Monad OpDiscreteHybridNE where
  OpDiscreteHybridNE xs >>= f =
    OpDiscreteHybridNE $ join $ NonEmpty.map (unOpDiscreteHybridNE . f) xs
   where
    join (splitSnoc -> (xss, xs)) = fromList (map NonEmpty.head xss ++ toList xs)

instance IsNonEmpty (OpDiscreteHybridNE a) where
  type ItemNE (OpDiscreteHybridNE a) = a
  fromNonEmpty = OpDiscreteHybridNE
  toNonEmpty = unOpDiscreteHybridNE

instance NonEmptyMonad OpDiscreteHybridNE

instance Magma (OpDiscreteHybridNE a) where
  m <> t = join $ OpDiscreteHybridNE $ [m, t]

instance XZ (OpDiscreteHybridNE a)

instance FreeRBM OpDiscreteHybridNE XZ

-- The following two are needed for examples in the docs:

instance IsList (OpDiscreteHybridNE a) where
  type Item (OpDiscreteHybridNE a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance IsString (OpDiscreteHybridNE Char) where
  fromString = fromList

--------------------------------------------
-- The Non-empty Maze Walk monad --
-------------------------------------------

-- | Instances should satisfy the following equation:
--
-- @
-- (x '<>' y) '<>' z  ==  x '<>' (y '<>' (x '<>' z))
-- @
class (Magma a) => PalindromeMagma a

-- | The non-empty maze walk monad arises from free
-- 'PalindromeMagma'-s. Its join (in terms of @joinList@) can be given
-- as follows:
--
-- @
-- joinList xss = map 'Control.Monad.List.Exotic.palindromize' (init xss) ++ last xss
-- @
--
-- See the possibly-empty version
-- ('Control.Monad.List.Exotic.MazeWalk') for more details.
newtype MazeWalkNE a =
  MazeWalkNE { unMazeWalkNE :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative MazeWalkNE where
  pure a = MazeWalkNE $ [a]  -- OverloadedLists
  (<*>)  = ap

instance Monad MazeWalkNE where
  MazeWalkNE xs >>= f =
    MazeWalkNE $ join $ NonEmpty.map (unMazeWalkNE . f) xs
   where
    join :: NonEmpty (NonEmpty a) -> NonEmpty a
    join (splitSnoc -> (xss, xs)) = fromList $
      concatMap (palindromize . toList) xss ++ toList xs 

instance IsNonEmpty (MazeWalkNE a) where
  type ItemNE (MazeWalkNE a) = a
  fromNonEmpty = MazeWalkNE
  toNonEmpty = unMazeWalkNE

instance NonEmptyMonad MazeWalkNE

instance Magma (MazeWalkNE a) where
  m <> t = join $ MazeWalkNE $ [m, t]

instance PalindromeMagma (MazeWalkNE a)

instance FreeRBM MazeWalkNE PalindromeMagma

---------------------------------
-- The Non-empty Stutter monad --
---------------------------------

-- | Instances should satisfy the following equation:
--
-- @
-- (x '<>' y) '<>' z  ==  'foldr1' ('<>') ('replicate' (n + 2) x)
-- @
class (KnownNat n, Magma a) => StutterMagma n a

-- | The non-empty stutter monad arises from free 'StutterMagma'-s.
-- Its join (in terms of @joinList@) can be given as follows:
--
-- @
-- joinList xss | any (not . 'Control.Monad.List.Exotic.isSingle') (init xss)
--              = map head (takeWhile 'Control.Monad.List.Exotic.isSingle' (init xss))
--                 ++ replicate (n + 2) (head (head (dropWhile 'Control.Monad.List.Exotic.isSingle' (init xss))))
--              | otherwise
--              = map head (init xss) ++ last xss
-- @
--
-- Examples:
--
-- >>> toList $ unwrap (join ["a", "b", "c", "hello", "there"] :: StutterNE 5 Char)
-- "abchhhhhhh"
-- >>> toList $ unwrap (join ["a", "b", "c", "hello"] :: StutterNE 5 Char)
-- "abchello"

newtype StutterNE (n :: Nat) a =
  StutterNE { unStutterNE :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance (KnownNat n) => Applicative (StutterNE n) where
  pure a = StutterNE $ [a]  -- OverloadedLists
  (<*>)  = ap

instance (KnownNat n) => Monad (StutterNE n) where
  StutterNE xs >>= f =
    StutterNE $ join $ NonEmpty.map (unStutterNE . f) xs
   where
    join :: NonEmpty (NonEmpty a) -> NonEmpty a
    join (splitSnoc -> (xss', xs))
      | any (not . isSingle) xss'
      = let n = fromIntegral $ natVal (Proxy :: Proxy n)
        in  fromList $
              map NonEmpty.head (takeWhile isSingle xss')
               ++ replicate (n + 2)
                  (NonEmpty.head $ head $ dropWhile isSingle xss')
      | otherwise
      = fromList $ map NonEmpty.head xss' ++ toList xs
      
instance (KnownNat n) => IsNonEmpty (StutterNE n a) where
  type ItemNE (StutterNE n a) = a
  fromNonEmpty = StutterNE
  toNonEmpty = unStutterNE

instance (KnownNat n) => NonEmptyMonad (StutterNE n)

instance (KnownNat n) => Magma (StutterNE n a) where
  m <> t = join $ StutterNE $ [m, t]

instance (KnownNat n) => StutterMagma n (StutterNE n a)

instance (KnownNat n) => FreeRBM (StutterNE n) (StutterMagma n)

-- The following two are needed for examples in the docs:

instance (KnownNat n) => IsList (StutterNE n a) where
  type Item (StutterNE n a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance (KnownNat n) => IsString (StutterNE n Char) where
  fromString = fromList

--------------------------
-- The Head-Tails monad --
--------------------------

-- $others
--
-- In contrast to the possibly-empty-list case, there are known
-- non-empty monads that arise from algebraic theories, but ones that
-- cannot be presented with one binary operations (as in monads that
-- come about from subclasses of 'Magma').

-- | The head-tail-tail algebra has two operations: unary 'hd'
-- (intuitively, it produces a singleton list with the head of the
-- argument as the element) and ternary 'htt' (intuitively, it
-- produces the concat of the head of the first argument and tails of
-- the other two arguments).
--
-- Instances should satisfy the following equations:
--
-- @
-- x                         ==  'htt' x x ('hd' x)
-- 'hd' ('hd' x)                 ==  'hd' x
-- 'hd' ('htt' x y z)            ==  'hd' x
-- 'htt' x y ('hd' z)            ==  'htt' x y ('hd' y)
-- 'htt' x y ('htt' z v w)       ==  'htt' x y ('htt' y v w)
-- 'htt' x ('hd' y) ('hd' z)       ==  'hd' x
-- 'htt' x ('hd' y) ('htt' z v w)  ==  'htt' x v w
-- 'htt' x ('htt' y z v) w       ==  'htt' x z ('htt' z v w)
-- 'htt' ('hd' x) y z            ==  'htt' x y z
-- 'htt' ('htt' x y z) v w       ==  'htt' x v w
-- @
--
-- Moreover, when read left-to-right they form a terminating and
-- confluent rewriting system with normal forms of the following
-- shape:
--
-- @
-- 'htt' x y $ 'htt' y z $ 'htt' z v $ ... $ 'htt' w t ('hd' t)
-- @
class HeadTailTail a where
  hd  :: a -> a
  htt :: a -> a -> a -> a

-- | The Head-Tails monad arises from free head-tail-tail algebras. Its unit is a dubleton, that is:
--
-- @
-- return x = HeadTails (x :| [x])
-- @
--
-- Its join is defined as:
--
-- @
-- join ((x :| _) :| xss) = x :| concatMap NonEmpty.tail xss
-- @
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: HeadTails Char)
-- "Jauleorgeingo"
newtype HeadTails a = HeadTails { unHeadTails :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative HeadTails where
  pure a = HeadTails $ [a,a]  -- OverloadedLists
  (<*>)  = ap

instance Monad HeadTails where
  HeadTails xs >>= f = HeadTails $ join $ NonEmpty.map (unHeadTails . f) xs
   where
    join ((x :| _) :| xss) = x :| concatMap NonEmpty.tail xss

instance IsNonEmpty (HeadTails a) where
  type ItemNE (HeadTails a) = a
  fromNonEmpty = HeadTails
  toNonEmpty = unHeadTails

instance NonEmptyMonad HeadTails

instance HeadTailTail (HeadTails a) where
  hd  a     = join $ HeadTails [a]        -- OverloadedLists
  htt a b c = join $ HeadTails [a, b, c]  -- OverloadedLists

-- | The 'HeadTails' monad arises from free head-tail-tail algebras,
-- so an interpretation of generators @g@ to a head-tail-tail algebra
-- @a@ can be (uniquely) lifted to a homomorphism between
-- head-tail-tail algebras.
foldHeadTails :: (HeadTailTail a) => (g -> a) -> HeadTails g -> a
foldHeadTails f (HeadTails (x :| [])) = hd (f x)
foldHeadTails f (HeadTails (x :| (y : ys))) =
  htt (f x) (f y) (foldHeadTails f $ HeadTails $ y :| ys)

-- The following two are needed for examples in the docs:

instance IsList (HeadTails a) where
  type Item (HeadTails a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance IsString (HeadTails Char) where
  fromString = fromList

--------------------------
-- The Heads-Tail monad --
--------------------------

-- | Instances should satisfy the following equations:
--
-- @
-- x                    ==  'ht' x x
-- 'hd'' ('hd'' x)          ==  'hd'' x
-- 'hd'' ('ht' x y)         ==  'hd'' x
-- 'hd'' ('hht' x y z)      ==  'hd'' x
-- 'ht' x ('hd'' y)         ==  'hd'' x
-- 'ht' x ('ht' y z)        ==  'ht' x z
-- 'ht' x ('hht' y z v)     ==  'hht' x z v
-- 'ht' ('hd'' x) y         ==  'ht' x y
-- 'ht' ('ht' x y) z        ==  'ht' x z
-- 'ht' ('hht' x y z) v     ==  'ht' x v
-- 'hht' x y ('hd'' z)      ==  'hd'' x
-- 'hht' x y ('ht' z v)     ==  'hht' x y v
-- 'hht' x y ('hht' z v w)  ==  'hht' x y ('hht' y v w)
-- 'hht' x ('hd'' y) z      ==  'hht' x y z
-- 'hht' x ('ht' y z) v     ==  'hht' x y v
-- 'hht' x ('hht' y z v) w  ==  'hht' x y w
-- 'hht' ('hd'' x) y z      ==  'hht' x y z
-- 'hht' ('ht' x y) z v     ==  'hht' x z v
-- 'hht' ('hht' x y z) v w  ==  'hht' x v w
-- @
--
-- Moreover, when read left-to-right they form a terminating and
-- confluent rewriting system with normal forms of the following
-- shape:
--
-- @
-- 'hd'' x
-- 'ht' x y
-- 'hht' x y $ 'hht' y z $ 'hht' z v $ ... $ 'hht' w t u
-- @
class HeadHeadTail a where
  hd' :: a -> a
  ht  :: a -> a -> a
  hht :: a -> a -> a -> a
  
-- | The Heads-Tail monad arises from free head-head-tail algebras. Its unit is a dubleton, that is:
--
-- @
-- return x = HeadsTail (x :| [x])
-- @
--
-- Its join is defined as:
--
-- @
-- join xss\@('splitSnoc' -> (xss', xs\@(_:|ys)))
--   | 'isSingle' xss || 'isSingle' xs
--   = (NonEmpty.head $ NonEmpty.head xss) :| []
--   | otherwise
--   = fromList $ map NonEmpty.head xss' ++ ys
-- @
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: HeadsTail Char)
-- "JPGingo"
newtype HeadsTail a = HeadsTail { unHeadsTail :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative HeadsTail where
  pure a = HeadsTail $ [a,a]  -- OverloadedLists
  (<*>)  = ap

instance Monad HeadsTail where
  HeadsTail xs >>= f = HeadsTail $ join $ NonEmpty.map (unHeadsTail . f) xs
   where
    join xss@(splitSnoc -> (xss', xs@(_:|ys)))
      | isSingle xss || isSingle xs
      = [NonEmpty.head $ NonEmpty.head xss]  -- OverloadedLists 
      | otherwise
      = fromList $ map NonEmpty.head xss' ++ ys
                                       
instance IsNonEmpty (HeadsTail a) where
  type ItemNE (HeadsTail a) = a
  fromNonEmpty = HeadsTail
  toNonEmpty = unHeadsTail

instance NonEmptyMonad HeadsTail

instance HeadHeadTail (HeadsTail a) where
  hd' a     = join $ HeadsTail [a]        -- OverloadedLists
  ht  a b   = join $ HeadsTail [a, b]     -- OverloadedLists
  hht a b c = join $ HeadsTail [a, b, c]  -- OverloadedLists

-- | The 'HeadsTail' monad arises from free head-head-tail algebras,
-- so an interpretation of generators @g@ to a head-head-tail algebra
-- @a@ can be (uniquely) lifted to a homomorphism between
-- head-head-tail algebras.
foldHeadsTail :: (HeadHeadTail a) => (g -> a) -> HeadsTail g -> a
foldHeadsTail f (HeadsTail (x :| []))       = hd' (f x)
foldHeadsTail f (HeadsTail (x :| [y]))      = ht (f x) (f y)
foldHeadsTail f (HeadsTail (x :| [y, z]))   = hht (f x) (f y) (f z)
foldHeadsTail f (HeadsTail (x :| (y : ys))) =
  hht (f x) (f y) (foldHeadsTail f $ HeadsTail $ y :| ys)

-- The following two are needed for examples in the docs:

instance IsList (HeadsTail a) where
  type Item (HeadsTail a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance IsString (HeadsTail Char) where
  fromString = fromList

------------------
-- The ΑΩ monad --
------------------

-- | The join of the ΑΩ (Alpha-Omega) monad takes the first element of
-- the first list and the last element of the last list (unless the
-- unit laws require otherwise):
--
-- @
-- join xss | isSingle xss || nonEmptyAll isSingle xss
--          = nonEmptyConcat xss
--          | otherwise
--          =  NonEmpty.head (NonEmpty.head xss)
--          :| NonEmpty.last (NonEmpty.last xss) : []
-- @
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: AlphaOmega Char)
-- "Jo"
newtype AlphaOmega a = AlphaOmega { unAlphaOmega :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance Applicative AlphaOmega where
  pure a = AlphaOmega [a]                           -- OverloadedLists
  (<*>)  = ap

instance Monad AlphaOmega where
  AlphaOmega xs >>= f = AlphaOmega $ join $ NonEmpty.map (unAlphaOmega . f) xs
   where
    join xss | isSingle xss || nonEmptyAll isSingle xss
             = nonEmptyConcat xss
             | otherwise
             = [ NonEmpty.head (NonEmpty.head xss)   -- OverloadedLists
               , NonEmpty.last (NonEmpty.last xss) ]

instance IsNonEmpty (AlphaOmega a) where
  type ItemNE (AlphaOmega a) = a
  fromNonEmpty = AlphaOmega
  toNonEmpty = unAlphaOmega

instance NonEmptyMonad AlphaOmega

-- The following two are needed for examples in the docs:

instance IsList (AlphaOmega a) where
  type Item (AlphaOmega a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

instance IsString (AlphaOmega Char) where
  fromString = fromList

-----------------------
-- The Α^n-Ω^k monad --
-----------------------

-- | A generalisation of the ΑΩ monad in which we replicate the first element
-- @n@ times and the last element @k@ times. It is a monad when @n + k >= 2@.
--
-- @
-- join xss | isSingle xss || nonEmptyAll isSingle xss
--          = nonEmptyConcat xss
--          | otherwise
--          = fromList $
--              replicate n (NonEmpty.head $ NonEmpty.head xss) ++
--              replicate k (NonEmpty.last $ NonEmpty.last xss)
-- @
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: AlphaOmega 2 3 Char)
-- "JJooo"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: AlphaOmega 0 6 Char)
-- "oooooo"
newtype AlphaNOmegaK (n :: Nat) (k :: Nat) a = AlphaNOmegaK { unAlphaNOmegaK :: NonEmpty a }
 deriving (Functor, Show, Eq)

instance (KnownNat n, KnownNat k, 2 <= n + k) => Applicative (AlphaNOmegaK n k) where
  pure a = AlphaNOmegaK [a]                         -- OverloadedLists
  (<*>)  = ap

instance (KnownNat n, KnownNat k, 2 <= n + k) => Monad (AlphaNOmegaK n k) where
  AlphaNOmegaK xs >>= f = AlphaNOmegaK $ join $ NonEmpty.map (unAlphaNOmegaK . f) xs
   where
    join xss | isSingle xss || nonEmptyAll isSingle xss
             = nonEmptyConcat xss
             | otherwise
             = let n = fromIntegral $ natVal (Proxy :: Proxy n)
                   k = fromIntegral $ natVal (Proxy :: Proxy k)
               in fromList $
                    replicate n (NonEmpty.head $ NonEmpty.head xss) ++
                    replicate k (NonEmpty.last $ NonEmpty.last xss)

instance (KnownNat n, KnownNat k, 2 <= n + k) => IsNonEmpty (AlphaNOmegaK n k a) where
  type ItemNE (AlphaNOmegaK n k a) = a
  fromNonEmpty = AlphaNOmegaK
  toNonEmpty = unAlphaNOmegaK

instance (KnownNat n, KnownNat k, 2 <= n + k) => NonEmptyMonad (AlphaNOmegaK n k)

instance (KnownNat n, KnownNat k, 2 <= n + k) => IsList (AlphaNOmegaK n k a) where
  type Item (AlphaNOmegaK n k a) = a
  fromList = fromNonEmpty . fromList
  toList = toList . toNonEmpty

-- The following is needed for the examples in the docs:

instance (KnownNat n, KnownNat k, 2 <= n + k) => IsString (AlphaNOmegaK n k Char) where
  fromString = fromList

-------------------------------
-- Dual non-empty list monad --
-------------------------------

liftNEFun :: (NonEmptyMonad m)
          => (NonEmpty a -> NonEmpty a) -> m a -> m a
liftNEFun f = wrap . f . unwrap

-- | Every non-empty list monad has a dual, in which join is defined
-- as
--
-- @
-- reverse . join . reverse . fmap reverse
-- @
--
-- (where join is the join of the original list monad).
--
-- return is the same as in the original monad.
newtype DualNonEmptyMonad m a =
  DualNonEmptyMonad { unDualNonEmptyMonad :: m a }
 deriving (Functor, Show, Eq)

instance (NonEmptyMonad m) => Applicative (DualNonEmptyMonad m) where
  pure = DualNonEmptyMonad . liftNEFun NonEmpty.reverse . pure
  (<*>)  = ap

instance (NonEmptyMonad m) => Monad (DualNonEmptyMonad m) where
  DualNonEmptyMonad m >>= f = DualNonEmptyMonad $ liftNEFun NonEmpty.reverse $
    liftNEFun NonEmpty.reverse m >>=
      liftNEFun NonEmpty.reverse . unDualNonEmptyMonad . f

instance (IsNonEmpty (m a)) => IsNonEmpty (DualNonEmptyMonad m a) where
  type ItemNE (DualNonEmptyMonad m a) = ItemNE (m a)
  toNonEmpty (DualNonEmptyMonad m)    = toNonEmpty m
  fromNonEmpty xs                     = DualNonEmptyMonad (fromNonEmpty xs)

instance (NonEmptyMonad m) => NonEmptyMonad (DualNonEmptyMonad m) where
  wrap   = DualNonEmptyMonad . wrap
  unwrap = unwrap . unDualNonEmptyMonad

---------------------------------------
-- Product of Identity and ListMonad --
---------------------------------------

-- | @'NonEmpty' a@ is isomorphic to the product @(a, [a])@. Thus, we
-- can define a monadic structure on it by a product of the identity
-- monad with any list monad. In particular:
--
-- @
-- return x          = IdXList x (return x)
-- IdXList x m >>= f = IdXList (componentId $ f x) (m >>= componentM . f)
-- @
--
-- where 'return' and '>>=' in definition bodies come from the
-- transformed monad.
data IdXList m a = IdXList { componentId :: a, componentM :: m a }
 deriving (Functor, Show, Eq)

instance (ListMonad m) => Applicative (IdXList m) where
  pure x = IdXList x (pure x)
  (<*>)  = ap

instance (ListMonad m) => Monad (IdXList m) where
  IdXList x m >>= f = IdXList (componentId $ f x) (m >>= componentM . f)

instance (ListMonad m) => IsNonEmpty (IdXList m a) where
  type ItemNE (IdXList m a)  = a
  fromNonEmpty (x :| xs)     = IdXList x $ List.Exotic.wrap xs
  toNonEmpty   (IdXList x m) = x :| List.Exotic.unwrap m
  
instance (ListMonad m) => NonEmptyMonad (IdXList m)

---------------------------
-- The Short Front monad --
---------------------------

-- | Instances of this class are non-empty list monads for which the
-- 'ShortFront' construction gives a monad.
class (NonEmptyMonad m) => HasShortFront m

instance HasShortFront NonEmpty

-- | (?)
instance HasShortFront Keeper

-- | (?)
instance HasShortFront OpDiscreteHybridNE

-- | (?)
instance HasShortFront MazeWalkNE

-- | (?)
instance (KnownNat n) => HasShortFront (StutterNE n)

-- | (?)
instance HasShortFront AlphaOmega

instance (KnownNat n, KnownNat k, 2 <= n + k) => HasShortFront (AlphaNOmegaK n k)

instance (HasShortRear m) => HasShortFront (DualNonEmptyMonad m)

-- | This is a transformer for a number of monads (instances of the
-- 'HasShortFront' class), whose return is singleton and join takes
-- the prefix of length @p + 2@ of the result of the join of the
-- transformed monad (unless the unit laws require otherwise):
--
-- @
-- joinList xss | 'Control.Monad.List.Exotic.isSingle' xss || all 'Control.Monad.List.Exotic.isSingle' xss = concat xss
--              | otherwise = take (p + 2) (joinList xss)
-- @
--
-- where @joinList@ in the @otherwise@ branch is the @joinList@ of the transformed monad.
--
-- While there are quite a few \"short front\" monads on non-empty
-- lists, only one such monad on possibly-empty lists is known,
-- 'Control.Monad.List.Exotic.StutterKeeper' (the short version is
-- 'Control.Monad.List.Exotic.ShortStutterKeeper').
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront NonEmpty 4 Char)
-- "JohnPa"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront MazeWalkNE 4 Char)
-- "Johnho"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront OpDiscreteHybridNE 4 Char)
-- "JPGRin"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront Keeper 4 Char)
-- "John"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront (StutterNE 2) 4 Char)
-- "JJJJ"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortFront (StutterNE 6) 4 Char)
-- "JJJJJJ"
newtype ShortFront m (p :: Nat) a = ShortFront { unShortFront :: m a }
 deriving (Functor, Show, Eq)

instance (HasShortFront m, KnownNat p) => Applicative (ShortFront m p) where
  pure  = ShortFront . return
  (<*>) = ap

instance (HasShortFront m, KnownNat p) => Monad (ShortFront m p) where
  ShortFront m >>= f | isSingle (unwrap m)
                     || nonEmptyAll isSingle
                          (unwrap $ unwrap . unShortFront . f <$> m)
                     = ShortFront $ m >>= unShortFront . f
                     | otherwise
                     = let p = fromIntegral $ natVal (Proxy :: Proxy p)
                       in  ShortFront $ liftNEFun (fromList . NonEmpty.take (p + 2))
                                      $ m >>= unShortFront . f

instance (IsNonEmpty (m a), KnownNat p) => IsNonEmpty (ShortFront m p a) where
  type ItemNE (ShortFront m p a) = ItemNE (m a)
  toNonEmpty (ShortFront m) = toNonEmpty m
  fromNonEmpty xs = ShortFront (fromNonEmpty xs)

instance (HasShortFront m, KnownNat p) => NonEmptyMonad (ShortFront m p) where
  wrap   = ShortFront . wrap
  unwrap = unwrap . unShortFront

-- The following two are needed for examples in the docs:

instance (HasShortFront m, KnownNat p) => IsList (ShortFront m p a) where
  type Item (ShortFront m p a) = a
  fromList = wrap . fromList
  toList = toList . unwrap

instance (HasShortFront m, KnownNat p) => IsString (ShortFront m p Char) where
  fromString = fromList

---------------------------
-- The Short Rear monad --
---------------------------

-- | Instances of this class are non-empty list monads for which the
-- 'ShortRear' construction gives a monad.
class (NonEmptyMonad m) => HasShortRear m

instance HasShortRear NonEmpty

-- | (?)
instance HasShortRear DiscreteHybridNE

-- | (?)
instance HasShortRear AlphaOmega

instance (KnownNat n, KnownNat k, 2 <= n + k) => HasShortRear (AlphaNOmegaK n k)

instance (HasShortFront m) => HasShortRear (DualNonEmptyMonad m)

-- | Similar to 'ShortFront', but gives a monad if restricted to a
-- suffix of the length @p + 2@.
--
-- For example:
--
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortRear NonEmpty 5 Char)
-- "geRingo"
-- >>> toList $ unwrap (join ["John", "Paul", "George", "Ringo"] :: ShortRear DiscreteHybridNE 5 Char)
-- "leRingo"
--
newtype ShortRear m (p :: Nat) a = ShortRear { unShortRear :: m a }
 deriving (Functor, Show, Eq)

instance (HasShortRear m, KnownNat p) => Applicative (ShortRear m p) where
  pure  = ShortRear . pure
  (<*>) = ap

nonEmptyTakeRear :: Int -> NonEmpty a -> [a]
nonEmptyTakeRear p = reverse . NonEmpty.take p . NonEmpty.reverse

instance (HasShortRear m, KnownNat p) => Monad (ShortRear m p) where
  ShortRear m >>= f | isSingle (unwrap m)
                    || nonEmptyAll isSingle
                         (unwrap $ unwrap . unShortRear . f <$> m)
                    = ShortRear $ m >>= unShortRear . f
                    | otherwise
                    = let p = fromIntegral $ natVal (Proxy :: Proxy p)
                      in  ShortRear $ liftNEFun (fromList . nonEmptyTakeRear (p + 2))
                                    $ m >>= unShortRear . f

instance (IsNonEmpty (m a), KnownNat p) => IsNonEmpty (ShortRear m p a) where
  type ItemNE (ShortRear m p a) = ItemNE (m a)
  toNonEmpty (ShortRear m) = toNonEmpty m
  fromNonEmpty xs = ShortRear (fromNonEmpty xs)

instance (HasShortRear m, KnownNat p) => NonEmptyMonad (ShortRear m p) where
  wrap   = ShortRear . wrap
  unwrap = unwrap . unShortRear

-- The following two are needed for examples in the docs:

instance (HasShortRear m, KnownNat p) => IsList (ShortRear m p a) where
  type Item (ShortRear m p a) = a
  fromList = wrap . fromList
  toList = toList . unwrap

instance (HasShortRear m, KnownNat p) => IsString (ShortRear m p Char) where
  fromString = fromList
