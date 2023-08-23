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
deriving instance (Arbitrary a) => Arbitrary (Stutter m a)
deriving instance (Arbitrary a) => Arbitrary (StutterKeeper m a)
deriving instance (Arbitrary a) => Arbitrary (StutterStutter m n a)
deriving instance (Arbitrary a) => Arbitrary (Mini a)
deriving instance (Arbitrary a) => Arbitrary (Odd a)
deriving instance (Arbitrary a) => Arbitrary (AtLeast n a)
deriving instance (Arbitrary a) => Arbitrary (NumericalMonoidMonad xs a)
deriving instance (Arbitrary a) => Arbitrary (ContinuumOfMonads s a)
deriving instance (Arbitrary a) => Arbitrary (ShortStutterKeeper m n a)

assocTests :: Int
assocTests = 250

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
    modifyMaxSuccess (const assocTests) $ it "associativity:" $ property $
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
  testMonad  "StutterKeeper 2"    (Proxy :: Proxy (StutterKeeper 2))
  testMonad  "StutterKeeper 3"    (Proxy :: Proxy (StutterKeeper 3))
  testMonad  "StutterKeeper 4"    (Proxy :: Proxy (StutterKeeper 4))
  testMonad  "StutterKeeper 5"    (Proxy :: Proxy (StutterKeeper 5))
  testMonad  "StutterKeeper 10"   (Proxy :: Proxy (StutterKeeper 10))
  
  testMonad  "StutterStutter 0 0" (Proxy :: Proxy (StutterStutter 0 0))
  testMonad  "StutterStutter 0 1" (Proxy :: Proxy (StutterStutter 0 1))
  testMonad  "StutterStutter 1 0" (Proxy :: Proxy (StutterStutter 1 0))
  testMonad  "StutterStutter 1 1" (Proxy :: Proxy (StutterStutter 1 1))
  testMonad  "StutterStutter 5 3" (Proxy :: Proxy (StutterStutter 5 3))
  testMonad  "StutterStutter 3 5" (Proxy :: Proxy (StutterStutter 3 5))
  
  testMonad  "Mini"               (Proxy :: Proxy Mini)
  testMonad  "Odd"                (Proxy :: Proxy Odd)
  
  testMonad  "AtLeast 10"         (Proxy :: Proxy (AtLeast 10))
  testMonad  "AtLeast 4"          (Proxy :: Proxy (AtLeast 4))
  testMonad  "AtLeast 3"          (Proxy :: Proxy (AtLeast 3))
  testMonad  "AtLeast 2"          (Proxy :: Proxy (AtLeast 2))
  testMonad  "AtLeast 1"          (Proxy :: Proxy (AtLeast 1))
  testMonad  "AtLeast 0"          (Proxy :: Proxy (AtLeast 0))

  testMonad  "NumericalMonoidMonad []" (Proxy :: Proxy (NumericalMonoidMonad '[]))
  testMonad  "NumericalMonoidMonad [0]" (Proxy :: Proxy (NumericalMonoidMonad '[0]))
  testMonad  "NumericalMonoidMonad [1]" (Proxy :: Proxy (NumericalMonoidMonad '[1]))
  testMonad  "NumericalMonoidMonad [0,1]" (Proxy :: Proxy (NumericalMonoidMonad '[0,1]))
  testMonad  "NumericalMonoidMonad [2,7,20,22]" (Proxy :: Proxy (NumericalMonoidMonad '[2,7,20,22]))
  testMonad  "NumericalMonoidMonad [2]" (Proxy :: Proxy (NumericalMonoidMonad '[2]))
  testMonad  "NumericalMonoidMonad [3,4,5]" (Proxy :: Proxy (NumericalMonoidMonad '[3,4,5]))
  testMonad  "NumericalMonoidMonad [3,7]" (Proxy :: Proxy (NumericalMonoidMonad '[3,7]))
  testMonad  "NumericalMonoidMonad [2,4,11]" (Proxy :: Proxy (NumericalMonoidMonad '[2,4,11]))

  testMonad  "ContinuumOfMonads Primes" (Proxy :: Proxy (ContinuumOfMonads "Primes"))
  testMonad  "ContinuumOfMonads Fib" (Proxy :: Proxy (ContinuumOfMonads "Fib"))

  testMonad  "ShortStutterKeeper 0 0" (Proxy :: Proxy (ShortStutterKeeper 0 0))
  testMonad  "ShortStutterKeeper 0 1" (Proxy :: Proxy (ShortStutterKeeper 0 1))
  testMonad  "ShortStutterKeeper 0 1" (Proxy :: Proxy (ShortStutterKeeper 1 0))
  testMonad  "ShortStutterKeeper 1 1" (Proxy :: Proxy (ShortStutterKeeper 1 1))
  testMonad  "ShortStutterKeeper 5 3" (Proxy :: Proxy (ShortStutterKeeper 5 3))
  testMonad  "ShortStutterKeeper 3 5" (Proxy :: Proxy (ShortStutterKeeper 3 5))
