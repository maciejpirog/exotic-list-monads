{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Control.Monad.List.NonEmpty.ExoticSpec (spec) where

import Prelude hiding ((<>))
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Monad.List.NonEmpty.Exotic
import Control.Monad.List.Exotic (MazeWalk(..))
import Control.Monad (join, liftM2)
import Data.Proxy
-- import GHC.Exts (IsList(..))

instance (Arbitrary a) => Arbitrary (NonEmpty.NonEmpty a) where
  arbitrary = liftM2 (:|) (arbitrary :: Gen a) (arbitrary :: Gen [a])

deriving instance (Arbitrary a) => Arbitrary (MazeWalk a)

instance (Arbitrary a, Arbitrary (m a)) =>  Arbitrary (IdXList m a) where
  arbitrary = liftM2 IdXList (arbitrary :: Gen a) (arbitrary :: Gen (m a))

deriving instance (Arbitrary a, Arbitrary (m a)) => Arbitrary (DualNonEmptyMonad m a)
deriving instance (Arbitrary a) => Arbitrary (Keeper a)
deriving instance (Arbitrary a) => Arbitrary (DiscreteHybridNE a)
deriving instance (Arbitrary a) => Arbitrary (OpDiscreteHybridNE a)
deriving instance (Arbitrary a) => Arbitrary (MazeWalkNE a)
deriving instance (Arbitrary a) => Arbitrary (StutterNE 0 a)
deriving instance (Arbitrary a) => Arbitrary (StutterNE 1 a)
deriving instance (Arbitrary a) => Arbitrary (StutterNE 2 a)
deriving instance (Arbitrary a) => Arbitrary (StutterNE 5 a)
deriving instance (Arbitrary a) => Arbitrary (HeadTails a)
deriving instance (Arbitrary a) => Arbitrary (HeadsTail a)
deriving instance (Arbitrary a) => Arbitrary (AlphaOmega a)
deriving instance (Arbitrary a) => Arbitrary (AlphaNOmegaK n k a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortFront m 0 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortFront m 1 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortFront m 2 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortFront m 5 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortRear m 0 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortRear m 1 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortRear m 2 a)
deriving instance (Arbitrary (m a)) => Arbitrary (ShortRear m 5 a)

assocTests :: Int
assocTests = 250

testMonad :: forall m. (Monad m, Eq (m Int), Arbitrary (m Int),
                        Arbitrary (m (m (m Int))),
                        Show (m Int), Show (m (m (m Int))))
          => String -> Proxy m -> SpecWith ()
testMonad name _ =
  describe (name ++ " is a monad") $ do
    it "left unit:" $ property $
      \xs -> join (fmap return xs) == (xs :: m Int)
    it "right unit:" $ property $
      \xs -> join (return xs)      == (xs :: m Int)
    modifyMaxSuccess (const assocTests) $ it "associativity:" $ property $
      \xsss -> join (join xsss)    == (join (fmap join xsss) :: m Int)

spec :: Spec
spec = do

  testMonad "DualNonEmptyMonad Keeper"  (Proxy :: Proxy (DualNonEmptyMonad Keeper))
  testMonad "DualNonEmptyMonad DiscreteHybridNE"  (Proxy :: Proxy (DualNonEmptyMonad DiscreteHybridNE))
  testMonad "IdXList MazeWalk"  (Proxy :: Proxy (IdXList MazeWalk))
  testMonad "Keeper"  (Proxy :: Proxy HeadTails)
  describe  "Keeper is XY" $ it "(x <> y) <> z  ==  x <> y" $ property $
       \(x :: Keeper Int) y z -> (x <> y) <> z  ==  x <> y
  testMonad "DiscreteHybridNE"  (Proxy :: Proxy HeadTails)
  describe  "DiscreteHybridNE is YZ" $ it "(x <> y) <> z  ==  y <> z" $ property $
       \(x :: DiscreteHybridNE Int) y z -> (x <> y) <> z  ==  y <> z
  testMonad "OpDiscreteHybridNE" (Proxy :: Proxy OpDiscreteHybridNE)
  describe  "OpDiscreteHybridNE is XZ" $ it "(x <> y) <> z  ==  x <> z" $ property $
       \(x :: OpDiscreteHybridNE Int) y z -> (x <> y) <> z  ==  x <> z
  testMonad "MazeWalkNE" (Proxy :: Proxy MazeWalkNE)
  describe  "MazeWalkNE is PalindromeMagma" $ it "(x <> y) <> z  ==  x <> (y <> (x <> z))" $ property $
                    \(x :: MazeWalkNE Int) y z -> (x <> y) <> z  ==  x <> (y <> (x <> z))
  testMonad "StutterNE 0" (Proxy :: Proxy (StutterNE 0))
  describe  "StutterNE 0 is StutterMagma 0" $ it "(x <> y) <> z  ==  foldr1 (<>) (replicate (0 + 2) x)" $ property $
                   \(x :: StutterNE 0 Int) y z -> (x <> y) <> z  ==  foldr1 (<>) (replicate (0 + 2) x)
  testMonad "StutterNE 1" (Proxy :: Proxy (StutterNE 1))
  describe  "StutterNE 1 is StutterMagma 1" $ it "(x <> y) <> z  ==  foldr1 (<>) (replicate (1 + 2) x)" $ property $
                   \(x :: StutterNE 1 Int) y z -> (x <> y) <> z  ==  foldr1 (<>) (replicate (1 + 2) x)
  testMonad "StutterNE 2" (Proxy :: Proxy (StutterNE 2))
  describe  "StutterNE 2 is StutterMagma 2" $ it "(x <> y) <> z  ==  foldr1 (<>) (replicate (2 + 2) x)" $ property $
                    \(x :: StutterNE 2 Int) y z -> (x <> y) <> z  ==  foldr1 (<>) (replicate (2 + 2) x)
  testMonad "StutterNE 5" (Proxy :: Proxy (StutterNE 5))
  describe  "StutterNE 5 is StutterMagma 5" $ it "(x <> y) <> z  ==  foldr1 (<>) (replicate (5 + 2) x)" $ property $
                   \(x :: StutterNE 5 Int) y z -> (x <> y) <> z  ==  foldr1 (<>) (replicate (5 + 2) x)

  testMonad "HeadTails"  (Proxy :: Proxy HeadTails)
  describe  "HeadTails is HeadTailTail" $ do
    it "equaitons:"
      $ property $ \(x :: HeadTails Int) y z v w ->
            x                         ==  htt x x (hd x)
         && hd (hd x)                 ==  hd x
         && hd (htt x y z)            ==  hd x
         && htt x y (hd z)            ==  htt x y (hd y)
         && htt x y (htt z v w)       ==  htt x y (htt y v w)
         && htt x (hd y) (hd z)       ==  hd x
         && htt x (hd y) (htt z v w)  ==  htt x v w
         && htt x (htt y z v) w       ==  htt x z (htt z v w)
         && htt (hd x) y z            ==  htt x y z
         && htt (htt x y z) v w       ==  htt x v w
  testMonad "HeadsTail"  (Proxy :: Proxy HeadsTail)
  describe  "HeadsTail is HeadHeadTail" $ do
    it "equations:"
      $ property $ \(x :: HeadsTail Int) y z v w ->
            x                    ==  ht x x
         && hd' (hd' x)          ==  hd' x
         && hd' (ht x y)         ==  hd' x
         && hd' (hht x y z)      ==  hd' x
         && ht x (hd' y)         ==  hd' x
         && ht x (ht y z)        ==  ht x z
         && ht x (hht y z v)     ==  hht x z v
         && ht (hd' x) y         ==  ht x y
         && ht (ht x y) z        ==  ht x z
         && ht (hht x y z) v     ==  ht x v
         && hht x y (hd' z)      ==  hd' x
         && hht x y (ht z v)     ==  hht x y v
         && hht x y (hht z v w)  ==  hht x y (hht y v w)
         && hht x (hd' y) z      ==  hht x y z
         && hht x (ht y z) v     ==  hht x y v
         && hht x (hht y z v) w  ==  hht x y w
         && hht (hd' x) y z      ==  hht x y z
         && hht (ht x y) z v     ==  hht x z v
         && hht (hht x y z) v w  ==  hht x v w

  testMonad "AlphaOmega" (Proxy :: Proxy AlphaOmega)

  testMonad "AlphaNOmegaK 1 1" (Proxy :: Proxy (AlphaNOmegaK 1 1))
  testMonad "AlphaNOmegaK 2 0" (Proxy :: Proxy (AlphaNOmegaK 2 0))
  testMonad "AlphaNOmegaK 0 2" (Proxy :: Proxy (AlphaNOmegaK 0 2))
  testMonad "AlphaNOmegaK 2 1" (Proxy :: Proxy (AlphaNOmegaK 2 1))
  testMonad "AlphaNOmegaK 1 2" (Proxy :: Proxy (AlphaNOmegaK 1 2))
  testMonad "AlphaNOmegaK 2 2" (Proxy :: Proxy (AlphaNOmegaK 2 2))
  testMonad "AlphaNOmegaK 3 1" (Proxy :: Proxy (AlphaNOmegaK 3 1))
  testMonad "AlphaNOmegaK 1 3" (Proxy :: Proxy (AlphaNOmegaK 1 3))
  testMonad "AlphaNOmegaK 3 2" (Proxy :: Proxy (AlphaNOmegaK 3 2))
  testMonad "AlphaNOmegaK 2 3" (Proxy :: Proxy (AlphaNOmegaK 2 3))
  testMonad "AlphaNOmegaK 3 3" (Proxy :: Proxy (AlphaNOmegaK 3 3))
  testMonad "AlphaNOmegaK 6 8" (Proxy :: Proxy (AlphaNOmegaK 6 8))
  testMonad "AlphaNOmegaK 9 3" (Proxy :: Proxy (AlphaNOmegaK 9 3))

  testMonad "ShortFront NonEmpty 0" (Proxy :: Proxy (ShortFront NonEmpty 0))
  testMonad "ShortFront NonEmpty 1" (Proxy :: Proxy (ShortFront NonEmpty 1))
  testMonad "ShortFront NonEmpty 2" (Proxy :: Proxy (ShortFront NonEmpty 2))
  testMonad "ShortFront NonEmpty 5" (Proxy :: Proxy (ShortFront NonEmpty 5))

  testMonad "ShortFront Keeper 0" (Proxy :: Proxy (ShortFront Keeper 0))
  testMonad "ShortFront Keeper 1" (Proxy :: Proxy (ShortFront Keeper 1))
  testMonad "ShortFront Keeper 2" (Proxy :: Proxy (ShortFront Keeper 2))
  testMonad "ShortFront Keeper 5" (Proxy :: Proxy (ShortFront Keeper 5))

  testMonad "ShortFront OpDiscreteHybridNE 0" (Proxy :: Proxy (ShortFront OpDiscreteHybridNE 0))
  testMonad "ShortFront OpDiscreteHybridNE 1" (Proxy :: Proxy (ShortFront OpDiscreteHybridNE 1))
  testMonad "ShortFront OpDiscreteHybridNE 2" (Proxy :: Proxy (ShortFront OpDiscreteHybridNE 2))
  testMonad "ShortFront OpDiscreteHybridNE 5" (Proxy :: Proxy (ShortFront OpDiscreteHybridNE 5))

  testMonad "ShortFront MazeWalkNE 0" (Proxy :: Proxy (ShortFront MazeWalkNE 0))
  testMonad "ShortFront MazeWalkNE 1" (Proxy :: Proxy (ShortFront MazeWalkNE 1))
  testMonad "ShortFront MazeWalkNE 2" (Proxy :: Proxy (ShortFront MazeWalkNE 2))
  testMonad "ShortFront MazeWalkNE 5" (Proxy :: Proxy (ShortFront MazeWalkNE 5))

  testMonad "ShortFront (StutterNE 0) 0" (Proxy :: Proxy (ShortFront (StutterNE 0) 0))
  testMonad "ShortFront (StutterNE 0) 1" (Proxy :: Proxy (ShortFront (StutterNE 0) 1))
  testMonad "ShortFront (StutterNE 0) 2" (Proxy :: Proxy (ShortFront (StutterNE 0) 2))
  testMonad "ShortFront (StutterNE 0) 5" (Proxy :: Proxy (ShortFront (StutterNE 0) 5))

  testMonad "ShortFront (StutterNE 1) 0" (Proxy :: Proxy (ShortFront (StutterNE 1) 0))
  testMonad "ShortFront (StutterNE 1) 1" (Proxy :: Proxy (ShortFront (StutterNE 1) 1))
  testMonad "ShortFront (StutterNE 1) 2" (Proxy :: Proxy (ShortFront (StutterNE 1) 2))
  testMonad "ShortFront (StutterNE 1) 5" (Proxy :: Proxy (ShortFront (StutterNE 1) 5))

  testMonad "ShortFront (StutterNE 2) 0" (Proxy :: Proxy (ShortFront (StutterNE 2) 0))
  testMonad "ShortFront (StutterNE 2) 1" (Proxy :: Proxy (ShortFront (StutterNE 2) 1))
  testMonad "ShortFront (StutterNE 2) 2" (Proxy :: Proxy (ShortFront (StutterNE 2) 2))
  testMonad "ShortFront (StutterNE 2) 5" (Proxy :: Proxy (ShortFront (StutterNE 2) 5))

  testMonad "ShortFront (StutterNE 5) 0" (Proxy :: Proxy (ShortFront (StutterNE 5) 0))
  testMonad "ShortFront (StutterNE 5) 1" (Proxy :: Proxy (ShortFront (StutterNE 5) 1))
  testMonad "ShortFront (StutterNE 5) 2" (Proxy :: Proxy (ShortFront (StutterNE 5) 2))
  testMonad "ShortFront (StutterNE 5) 5" (Proxy :: Proxy (ShortFront (StutterNE 5) 5))

  testMonad "ShortFront AlphaOmega 0" (Proxy :: Proxy (ShortFront AlphaOmega 0))
  testMonad "ShortFront AlphaOmega 1" (Proxy :: Proxy (ShortFront AlphaOmega 1))
  testMonad "ShortFront AlphaOmega 2" (Proxy :: Proxy (ShortFront AlphaOmega 2))
  testMonad "ShortFront AlphaOmega 5" (Proxy :: Proxy (ShortFront AlphaOmega 5))

  testMonad "ShortFront (AlphaNOmegaK 1 1) 0" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 1 1) 0))
  testMonad "ShortFront (AlphaNOmegaK 1 1) 1" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 1 1) 1))
  testMonad "ShortFront (AlphaNOmegaK 1 1) 2" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 1 1) 2))
  testMonad "ShortFront (AlphaNOmegaK 1 1) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 1 1) 5))
  testMonad "ShortFront (AlphaNOmegaK 2 0) 0" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 0) 0))
  testMonad "ShortFront (AlphaNOmegaK 2 0) 1" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 0) 1))
  testMonad "ShortFront (AlphaNOmegaK 2 0) 2" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 0) 2))
  testMonad "ShortFront (AlphaNOmegaK 2 0) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 0) 5))
  testMonad "ShortFront (AlphaNOmegaK 0 2) 0" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 0 2) 0))
  testMonad "ShortFront (AlphaNOmegaK 0 2) 0" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 0 2) 0))
  testMonad "ShortFront (AlphaNOmegaK 0 2) 1" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 0 2) 1))
  testMonad "ShortFront (AlphaNOmegaK 0 2) 2" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 0 2) 2))
  testMonad "ShortFront (AlphaNOmegaK 2 3) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 3) 5))
  testMonad "ShortFront (AlphaNOmegaK 2 3) 1" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 3) 1))
  testMonad "ShortFront (AlphaNOmegaK 2 3) 2" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 3) 2))
  testMonad "ShortFront (AlphaNOmegaK 2 3) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 2 3) 5))
  testMonad "ShortFront (AlphaNOmegaK 12 3) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 12 3) 5))
  testMonad "ShortFront (AlphaNOmegaK 12 3) 1" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 12 3) 1))
  testMonad "ShortFront (AlphaNOmegaK 12 3) 2" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 12 3) 2))
  testMonad "ShortFront (AlphaNOmegaK 12 3) 5" (Proxy :: Proxy (ShortFront (AlphaNOmegaK 12 3) 5))

  testMonad "ShortFront (DualNonEmptyMonad DiscreteHybridNE) 0" (Proxy :: Proxy (ShortFront (DualNonEmptyMonad DiscreteHybridNE) 0))
  testMonad "ShortFront (DualNonEmptyMonad DiscreteHybridNE) 1" (Proxy :: Proxy (ShortFront (DualNonEmptyMonad DiscreteHybridNE) 1))
  testMonad "ShortFront (DualNonEmptyMonad DiscreteHybridNE) 2" (Proxy :: Proxy (ShortFront (DualNonEmptyMonad DiscreteHybridNE) 2))
  testMonad "ShortFront (DualNonEmptyMonad DiscreteHybridNE) 5" (Proxy :: Proxy (ShortFront (DualNonEmptyMonad DiscreteHybridNE) 5))

  testMonad "ShortRear NonEmpty 0" (Proxy :: Proxy (ShortRear NonEmpty 0))
  testMonad "ShortRear NonEmpty 1" (Proxy :: Proxy (ShortRear NonEmpty 1))
  testMonad "ShortRear NonEmpty 2" (Proxy :: Proxy (ShortRear NonEmpty 2))
  testMonad "ShortRear NonEmpty 5" (Proxy :: Proxy (ShortRear NonEmpty 5))

  testMonad "ShortRear DiscreteHybridNE 0" (Proxy :: Proxy (ShortRear DiscreteHybridNE 0))
  testMonad "ShortRear DiscreteHybridNE 1" (Proxy :: Proxy (ShortRear DiscreteHybridNE 1))
  testMonad "ShortRear DiscreteHybridNE 2" (Proxy :: Proxy (ShortRear DiscreteHybridNE 2))
  testMonad "ShortRear DiscreteHybridNE 5" (Proxy :: Proxy (ShortRear DiscreteHybridNE 5))

  testMonad "ShortRear AlphaOmega 0" (Proxy :: Proxy (ShortRear AlphaOmega 0))
  testMonad "ShortRear AlphaOmega 1" (Proxy :: Proxy (ShortRear AlphaOmega 1))
  testMonad "ShortRear AlphaOmega 2" (Proxy :: Proxy (ShortRear AlphaOmega 2))
  testMonad "ShortRear AlphaOmega 5" (Proxy :: Proxy (ShortRear AlphaOmega 5))

  testMonad "ShortRear (AlphaNOmegaK 1 1) 0" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 1 1) 0))
  testMonad "ShortRear (AlphaNOmegaK 1 1) 1" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 1 1) 1))
  testMonad "ShortRear (AlphaNOmegaK 1 1) 2" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 1 1) 2))
  testMonad "ShortRear (AlphaNOmegaK 1 1) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 1 1) 5))
  testMonad "ShortRear (AlphaNOmegaK 2 0) 0" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 0) 0))
  testMonad "ShortRear (AlphaNOmegaK 2 0) 1" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 0) 1))
  testMonad "ShortRear (AlphaNOmegaK 2 0) 2" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 0) 2))
  testMonad "ShortRear (AlphaNOmegaK 2 0) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 0) 5))
  testMonad "ShortRear (AlphaNOmegaK 0 2) 0" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 0 2) 0))
  testMonad "ShortRear (AlphaNOmegaK 0 2) 0" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 0 2) 0))
  testMonad "ShortRear (AlphaNOmegaK 0 2) 1" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 0 2) 1))
  testMonad "ShortRear (AlphaNOmegaK 0 2) 2" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 0 2) 2))
  testMonad "ShortRear (AlphaNOmegaK 2 3) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 3) 5))
  testMonad "ShortRear (AlphaNOmegaK 2 3) 1" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 3) 1))
  testMonad "ShortRear (AlphaNOmegaK 2 3) 2" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 3) 2))
  testMonad "ShortRear (AlphaNOmegaK 2 3) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 2 3) 5))
  testMonad "ShortRear (AlphaNOmegaK 12 3) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 12 3) 5))
  testMonad "ShortRear (AlphaNOmegaK 12 3) 1" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 12 3) 1))
  testMonad "ShortRear (AlphaNOmegaK 12 3) 2" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 12 3) 2))
  testMonad "ShortRear (AlphaNOmegaK 12 3) 5" (Proxy :: Proxy (ShortRear (AlphaNOmegaK 12 3) 5))

  testMonad "ShortRear (DualNonEmptyMonad Keeper) 0" (Proxy :: Proxy (ShortRear (DualNonEmptyMonad Keeper) 0))
  testMonad "ShortRear (DualNonEmptyMonad Keeper) 1" (Proxy :: Proxy (ShortRear (DualNonEmptyMonad Keeper) 1))
  testMonad "ShortRear (DualNonEmptyMonad Keeper) 2" (Proxy :: Proxy (ShortRear (DualNonEmptyMonad Keeper) 2))
  testMonad "ShortRear (DualNonEmptyMonad Keeper) 5" (Proxy :: Proxy (ShortRear (DualNonEmptyMonad Keeper) 5))
