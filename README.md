# exotic-list-monads

The usual [list monad](https://hackage.haskell.org/package/base-4.14.0.0/docs/src/GHC.Base.html#line-1133) is only one of infinitely many ways to turn the list functor into a monad. The same applies to the usual [non-empty list monad](https://hackage.haskell.org/package/base-4.14.0.0/docs/src/GHC.Base.html#line-1105) and the non-empty list functor. This library collects such non-standard "list" and "non-empty list" monads.

Most of the constructions implemented in this library have been first introduced in the paper [Degrading lists](degrading-lists.pdf) by Dylan McDermott, Maciej Piróg, and Tarmo Uustalu (PPDP 2020), but there are some new specimens as well.

It is quite possible that there exist "list" and "non-empty list" monads that we are not aware of, so pull requests are appreciated. Moreover, not every monad in this library has been formally verified to be a monad (it is not a trivial task because of combinatorial explosions of the number of cases to be considered in some proofs of associativity), so if you're currently playing around with tools like Coq and have a spare afternoon...
