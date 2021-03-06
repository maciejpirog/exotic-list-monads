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

module Control.Monad.List.ExoticSpec (spec) where

import Prelude hiding ((<>))
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Control.Monad.List.Exotic
import Control.Monad (join)
import Data.Proxy
import GHC.Exts (IsList(..))

deriving instance (Arbitrary a) => Arbitrary (GlobalFailure a)
deriving instance (Arbitrary a) => Arbitrary (MazeWalk a)
deriving instance (Arbitrary a) => Arbitrary (DiscreteHybrid a)
deriving instance (Arbitrary a) => Arbitrary (ListUnfold a)
deriving instance (Arbitrary a) => Arbitrary (Stutter 0 a)
deriving instance (Arbitrary a) => Arbitrary (Stutter 1 a)
deriving instance (Arbitrary a) => Arbitrary (Stutter 5 a)
deriving instance (Arbitrary a) => Arbitrary (StutterKeeper 0 a)
deriving instance (Arbitrary a) => Arbitrary (StutterKeeper 1 a)
deriving instance (Arbitrary a) => Arbitrary (StutterKeeper 5 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 0 0 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 0 1 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 1 0 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 1 1 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 5 3 a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter 3 5 a)
deriving instance (Arbitrary a) => Arbitrary (Mini a)
deriving instance (Arbitrary a) => Arbitrary (Odd a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 0 0 a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 0 1 a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 1 0 a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 1 1 a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 5 3 a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper 3 5 a)

testMonad :: forall m. (Eq (Item (m Int)), ListMonad m, Arbitrary (m Int),
                        Arbitrary (m (m (m Int))),
                        IsList (m Int),
                        Show (m Int), Show (m (m (m Int))))
          => String -> Proxy m -> SpecWith ()
testMonad name _ =
  describe (name ++ " is a monad") $ do
    it "left unit:" $ property $
      \xs -> toList (join (fmap return xs)) == toList ((xs :: m Int)) 
    it "right unit:" $ property $
      \xs -> toList (join (return xs))      == toList ((xs :: m Int))
    modifyMaxSuccess (const 150) $ it "associativity:" $ property $
      \xsss -> toList (join (join xsss))    == toList (join (fmap join xsss) :: m Int)
      
spec :: Spec
spec = do
  describe "palindromize" $ do
    it "palindromizes a non-empty list" $
      palindromize "abcd" `shouldBe` "abcdcba"
    it "palindromizes an empty list" $
      palindromize "" `shouldBe` ""
      
  describe "isSingle" $ do
    it "knows that empty is not a singleton" $
      isSingle "" `shouldBe` False
    it "knows that a singleton is a singleton" $
      isSingle "a" `shouldBe` True
    it "knows that a long list is not a singleton" $
      isSingle "ab" `shouldBe` False

  describe "safeLast" $ do
    it "knows that last of empty is empty" $
      safeLast "" `shouldBe` ""
    it "knows that last of non-empty is non-empty" $
      safeLast "Roy" `shouldBe` "y"

  testMonad  "GlobalFailure"      (Proxy :: Proxy GlobalFailure)
  describe  "GlobalFailure is ZeroSemigroup" $ do
    it                                             "x <> eps       ==  eps"
      $ property $ \(x :: GlobalFailure Int)     -> x <> eps       ==  eps
    it                                             "eps <> x       ==  eps"
      $ property $ \(x :: GlobalFailure Int)     -> eps <> x       ==  eps
    it                                             "(x <> y) <> z  ==  x <> (y <> z)"
      $ property $ \(x :: GlobalFailure Int) y z -> (x <> y) <> z  ==  x <> (y <> z)
  testMonad  "MazeWalk"           (Proxy :: Proxy MazeWalk)
  describe  "MazeWalk is PalindromeAlgebra" $ do
    it                                        "x <> eps       ==  eps"
      $ property $ \(x :: MazeWalk Int)     -> x <> eps       ==  eps
    it                                        "eps <> x       ==  eps"
      $ property $ \(x :: MazeWalk Int)     -> eps <> x       ==  eps
    it                                        "(x <> y) <> z  ==  x <> (y <> (x <> z))"
      $ property $ \(x :: MazeWalk Int) y z -> (x <> y) <> z  ==  x <> (y <> (x <> z))
  testMonad  "DiscreteHybrid"     (Proxy :: Proxy DiscreteHybrid)
  describe  "DiscreteHybrid is LeaningAlgebra" $ do
    it                                              "x <> eps       ==  eps"
      $ property $ \(x :: DiscreteHybrid Int)     -> x <> eps       ==  eps
    it                                              "eps <> x       ==  x"
      $ property $ \(x :: DiscreteHybrid Int)     -> eps <> x       ==  x
    it                                              "(x <> y) <> z  ==  y <> z"
      $ property $ \(x :: DiscreteHybrid Int) y z -> (x <> y) <> z  ==  y <> z
  testMonad  "ListUnfold"         (Proxy :: Proxy ListUnfold)
  describe  "ListUnfold is SkewedAlgebra" $ do
    it                                          "x <> eps       ==  eps"
      $ property $ \(x :: ListUnfold Int)     -> x <> eps       ==  eps
    it                                          "eps <> x       ==  eps"
      $ property $ \(x :: ListUnfold Int)     -> eps <> x       ==  eps
    it                                          "(x <> y) <> z  ==  eps"
      $ property $ \(x :: ListUnfold Int) y z -> (x <> y) <> z  ==  eps
  testMonad  "Stutter 1"          (Proxy :: Proxy (Stutter 0))
  testMonad  "Stutter 2"          (Proxy :: Proxy (Stutter 1))
  testMonad  "Stutter 5"          (Proxy :: Proxy (Stutter 5))
  testMonad  "StutterKeeper 0"    (Proxy :: Proxy (StutterKeeper 0))
  testMonad  "StutterKeeper 1"    (Proxy :: Proxy (StutterKeeper 1))
  testMonad  "StutterKeeper 5"    (Proxy :: Proxy (StutterKeeper 5))
  testMonad  "StutterStutter 0 0" (Proxy :: Proxy (StutterStutter 0 0))
  testMonad  "StutterStutter 0 1" (Proxy :: Proxy (StutterStutter 0 1))
  testMonad  "StutterStutter 1 0" (Proxy :: Proxy (StutterStutter 1 0))
  testMonad  "StutterStutter 1 1" (Proxy :: Proxy (StutterStutter 1 1))
  testMonad  "StutterStutter 5 3" (Proxy :: Proxy (StutterStutter 5 3))
  testMonad  "StutterStutter 3 5" (Proxy :: Proxy (StutterStutter 3 5))
  testMonad  "Mini"               (Proxy :: Proxy Mini)
  testMonad  "Odd"                (Proxy :: Proxy Odd)
  testMonad  "ShortStutterKeeper 0 0" (Proxy :: Proxy (ShortStutterKeeper 0 0))
  testMonad  "ShortStutterKeeper 0 1" (Proxy :: Proxy (ShortStutterKeeper 0 1))
  testMonad  "ShortStutterKeeper 0 1" (Proxy :: Proxy (ShortStutterKeeper 1 0))
  testMonad  "ShortStutterKeeper 1 1" (Proxy :: Proxy (ShortStutterKeeper 1 1))
  testMonad  "ShortStutterKeeper 5 3" (Proxy :: Proxy (ShortStutterKeeper 5 3))
  testMonad  "ShortStutterKeeper 3 5" (Proxy :: Proxy (ShortStutterKeeper 3 5))
