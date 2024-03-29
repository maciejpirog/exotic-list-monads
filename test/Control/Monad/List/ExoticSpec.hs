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
{-# LANGUAGE RankNTypes #-}

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

deriving instance (Arbitrary (m a)) => Arbitrary (DualListMonad m a)
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
deriving instance (Arbitrary a) => Arbitrary (AtMost n a)
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

testMonadIsomorphism :: forall m n. (Eq (Item (m Int)), ListMonad m, Arbitrary (m Int),
                        Arbitrary (m (m Int)),
                        IsList (m Int),
                        Show (m Int), Show (m (m Int)),
                        Eq (Item (n Int)), ListMonad n, Arbitrary (n Int),
                        Arbitrary (n (n Int)),
                        IsList (n Int),
                        Show (n Int), Show (n (n Int)))
          => String -> String -> Proxy m -> Proxy n -> (forall a. m a -> n a) -> (forall a. n a -> m a) -> SpecWith ()
testMonadIsomorphism name name' _ _ f g =
  describe (name ++ " and " ++ name' ++ " are isomorphic as monads") $ do
    it "inverse:" $ property $
      \xs -> toList (xs :: m Int) == toList (g (f xs))
    it "other inverse:" $ property $
      \xs -> toList (xs :: n Int) == toList (f (g xs))
    it "homomorphism:" $ property $
      \xs -> toList (join (xs :: m (m (Int)))) == toList (g (join (f (fmap f xs))))
    it "other homomorphism:" $ property $
      \xs -> toList (join (xs :: n (n (Int)))) == toList (f (join (g (fmap g xs))))

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

  testMonad  "GlobalFailure"  (Proxy :: Proxy GlobalFailure)
  testMonad  "DualListMonad GlobalFailure" (Proxy :: Proxy (DualListMonad GlobalFailure))
  describe  "GlobalFailure is ZeroSemigroup" $ do
    it                                             "x <> eps       ==  eps"
      $ property $ \(x :: GlobalFailure Int)     -> x <> eps       ==  eps
    it                                             "eps <> x       ==  eps"
      $ property $ \(x :: GlobalFailure Int)     -> eps <> x       ==  eps
    it                                             "(x <> y) <> z  ==  x <> (y <> z)"
      $ property $ \(x :: GlobalFailure Int) y z -> (x <> y) <> z  ==  x <> (y <> z)
      
  testMonad  "MazeWalk" (Proxy :: Proxy MazeWalk)
  testMonad  "DualListMonad MazeWalk" (Proxy :: Proxy (DualListMonad MazeWalk))
  describe  "MazeWalk is PalindromeAlgebra" $ do
    it                                        "x <> eps       ==  eps"
      $ property $ \(x :: MazeWalk Int)     -> x <> eps       ==  eps
    it                                        "eps <> x       ==  eps"
      $ property $ \(x :: MazeWalk Int)     -> eps <> x       ==  eps
    it                                        "(x <> y) <> z  ==  x <> (y <> (x <> z))"
      $ property $ \(x :: MazeWalk Int) y z -> (x <> y) <> z  ==  x <> (y <> (x <> z))
      
  testMonad  "DiscreteHybrid" (Proxy :: Proxy DiscreteHybrid)
  testMonad  "DualListMonad DiscreteHybrid" (Proxy :: Proxy (DualListMonad DiscreteHybrid))
  describe  "DiscreteHybrid is LeaningAlgebra" $ do
    it                                              "x <> eps       ==  eps"
      $ property $ \(x :: DiscreteHybrid Int)     -> x <> eps       ==  eps
    it                                              "eps <> x       ==  x"
      $ property $ \(x :: DiscreteHybrid Int)     -> eps <> x       ==  x
    it                                              "(x <> y) <> z  ==  y <> z"
      $ property $ \(x :: DiscreteHybrid Int) y z -> (x <> y) <> z  ==  y <> z
  
  testMonad  "ListUnfold" (Proxy :: Proxy ListUnfold)
  testMonad  "DualListMonad ListUnfold" (Proxy :: Proxy (DualListMonad ListUnfold))
  describe  "ListUnfold is SkewedAlgebra" $ do
    it                                          "x <> eps       ==  eps"
      $ property $ \(x :: ListUnfold Int)     -> x <> eps       ==  eps
    it                                          "eps <> x       ==  eps"
      $ property $ \(x :: ListUnfold Int)     -> eps <> x       ==  eps
    it                                          "(x <> y) <> z  ==  eps"
      $ property $ \(x :: ListUnfold Int) y z -> (x <> y) <> z  ==  eps
      
  testMonad  "Stutter 1"          (Proxy :: Proxy (Stutter 1))
  testMonad  "Stutter 2"          (Proxy :: Proxy (Stutter 2))
  testMonad  "Stutter 5"          (Proxy :: Proxy (Stutter 5))

  testMonad  "DualListMonad (Stutter 0)" (Proxy :: Proxy (DualListMonad (Stutter 0)))
  testMonad  "DualListMonad (Stutter 1)" (Proxy :: Proxy (DualListMonad (Stutter 1)))
  testMonad  "DualListMonad (Stutter 2)" (Proxy :: Proxy (DualListMonad (Stutter 2)))
  testMonad  "DualListMonad (Stutter 5)" (Proxy :: Proxy (DualListMonad (Stutter 5)))

  testMonad  "StutterKeeper 0"    (Proxy :: Proxy (StutterKeeper 0))
  testMonad  "StutterKeeper 1"    (Proxy :: Proxy (StutterKeeper 1))
  testMonad  "StutterKeeper 2"    (Proxy :: Proxy (StutterKeeper 2))
  testMonad  "StutterKeeper 3"    (Proxy :: Proxy (StutterKeeper 3))
  testMonad  "StutterKeeper 4"    (Proxy :: Proxy (StutterKeeper 4))
  testMonad  "StutterKeeper 5"    (Proxy :: Proxy (StutterKeeper 5))
  testMonad  "StutterKeeper 10"   (Proxy :: Proxy (StutterKeeper 10))

  testMonad  "DualListMonad (StutterKeeper 0)" (Proxy :: Proxy (DualListMonad (StutterKeeper 0)))
  testMonad  "DualListMonad (StutterKeeper 1)" (Proxy :: Proxy (DualListMonad (StutterKeeper 1)))
  testMonad  "DualListMonad (StutterKeeper 2)" (Proxy :: Proxy (DualListMonad (StutterKeeper 2)))
  testMonad  "DualListMonad (StutterKeeper 5)" (Proxy :: Proxy (DualListMonad (StutterKeeper 5)))
  
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

  testMonadIsomorphism "AtLeast 1" "GlobalFailure" (Proxy :: Proxy (AtLeast 1)) (Proxy :: Proxy GlobalFailure) (GlobalFailure . unAtLeast) (AtLeast . unGlobalFailure)

  testMonad  "NumericalMonoidMonad []" (Proxy :: Proxy (NumericalMonoidMonad '[]))
  testMonad  "NumericalMonoidMonad [0]" (Proxy :: Proxy (NumericalMonoidMonad '[0]))
  testMonad  "NumericalMonoidMonad [1]" (Proxy :: Proxy (NumericalMonoidMonad '[1]))
  testMonad  "NumericalMonoidMonad [0,1]" (Proxy :: Proxy (NumericalMonoidMonad '[0,1]))
  testMonad  "NumericalMonoidMonad [2,7,20,22]" (Proxy :: Proxy (NumericalMonoidMonad '[2,7,20,22]))
  testMonad  "NumericalMonoidMonad [2]" (Proxy :: Proxy (NumericalMonoidMonad '[2]))
  testMonad  "NumericalMonoidMonad [3,4,5]" (Proxy :: Proxy (NumericalMonoidMonad '[3,4,5]))
  testMonad  "NumericalMonoidMonad [3,7]" (Proxy :: Proxy (NumericalMonoidMonad '[3,7]))
  testMonad  "NumericalMonoidMonad [2,4,11]" (Proxy :: Proxy (NumericalMonoidMonad '[2,4,11]))

  testMonadIsomorphism "Mini" "NumericalMonoidMonad '[]" (Proxy :: Proxy Mini) (Proxy :: Proxy (NumericalMonoidMonad '[])) (NumericalMonoidMonad . unMini) (Mini . unNumericalMonoidMonad)
  testMonadIsomorphism "Odd" "NumericalMonoidMonad '[2]" (Proxy :: Proxy Odd) (Proxy :: Proxy (NumericalMonoidMonad '[2])) (NumericalMonoidMonad . unOdd) (Odd . unNumericalMonoidMonad)
  testMonadIsomorphism "AtLeast 1" "NumericalMonoidMonad '[1]" (Proxy :: Proxy (AtLeast 3)) (Proxy :: Proxy (NumericalMonoidMonad '[2,3])) (NumericalMonoidMonad . unAtLeast) (AtLeast . unNumericalMonoidMonad)
  testMonadIsomorphism "AtLeast 3" "NumericalMonoidMonad '[2,3]" (Proxy :: Proxy (AtLeast 3)) (Proxy :: Proxy (NumericalMonoidMonad '[2,3])) (NumericalMonoidMonad . unAtLeast) (AtLeast . unNumericalMonoidMonad)
  testMonadIsomorphism "AtLeast 4" "NumericalMonoidMonad '[3,4,5]" (Proxy :: Proxy (AtLeast 4)) (Proxy :: Proxy (NumericalMonoidMonad '[3,4,5])) (NumericalMonoidMonad . unAtLeast) (AtLeast . unNumericalMonoidMonad)
  testMonadIsomorphism "AtLeast 5" "NumericalMonoidMonad '[4,5,6,7]" (Proxy :: Proxy (AtLeast 5)) (Proxy :: Proxy (NumericalMonoidMonad '[4,5,6,7])) (NumericalMonoidMonad . unAtLeast) (AtLeast . unNumericalMonoidMonad)

  testMonad  "AtMost 6"           (Proxy :: Proxy (AtMost 6))
  testMonad  "AtMost 5"           (Proxy :: Proxy (AtMost 5))
  testMonad  "AtMost 4"           (Proxy :: Proxy (AtMost 4))
  testMonad  "AtMost 3"           (Proxy :: Proxy (AtMost 3))
  testMonad  "AtMost 2"           (Proxy :: Proxy (AtMost 2))
  testMonad  "AtMost 1"           (Proxy :: Proxy (AtMost 1))
  testMonad  "AtMost 0"           (Proxy :: Proxy (AtMost 0))
  
  testMonad  "ContinuumOfMonads Primes" (Proxy :: Proxy (ContinuumOfMonads "Primes"))
  testMonad  "ContinuumOfMonads Fib" (Proxy :: Proxy (ContinuumOfMonads "Fib"))

  testMonad  "ShortStutterKeeper 0 0" (Proxy :: Proxy (ShortStutterKeeper 0 0))
  testMonad  "ShortStutterKeeper 0 1" (Proxy :: Proxy (ShortStutterKeeper 0 1))
  testMonad  "ShortStutterKeeper 1 0" (Proxy :: Proxy (ShortStutterKeeper 1 0))
  testMonad  "ShortStutterKeeper 1 1" (Proxy :: Proxy (ShortStutterKeeper 1 1))
  testMonad  "ShortStutterKeeper 5 3" (Proxy :: Proxy (ShortStutterKeeper 5 3))
  testMonad  "ShortStutterKeeper 3 5" (Proxy :: Proxy (ShortStutterKeeper 3 5))

  testMonad  "DualListMonad (ShortStutterKeeper 0 0)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 0 0)))
  testMonad  "DualListMonad (ShortStutterKeeper 0 1)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 0 1)))
  testMonad  "DualListMonad (ShortStutterKeeper 1 0)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 1 0)))
  testMonad  "DualListMonad (ShortStutterKeeper 1 1)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 1 1)))
  testMonad  "DualListMonad (ShortStutterKeeper 5 3)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 5 3)))
  testMonad  "DualListMonad (ShortStutterKeeper 3 5)" (Proxy :: Proxy (DualListMonad (ShortStutterKeeper 3 5)))


