# exotic-list-monad changelog

## v1.2.1

- Add `UndecidableInstances` extension to `Control.Monad.List.NonEmpty.Exotic` to
  deal with the `2 <= n + k` constraint in the `AlphaNOmegaK` monad on newer GHCs

- Turn off the `x-partial` warning

## v1.2.0

- Add the `AlphaNOmegaK` monad

## v1.1.1

- Refactor to avoid the `noncanonical-monad-instances` and `star-is-type` warnings

- Add `Eq` and `Show` instances to `DualListMonad`

- Fixes in documentation

## v1.1.0

- Add the `AtMost` monad

- Add the `NumericalMonoidMonad` monad

- Fixed the documentation to make `Mini` and `Odd` instances of `NumericalMonoidMonad`

- Add `AtLeast` as another instance of `NumericalMonoidMonad`

- Add the `ContinuumOfMonads` construction

## v1.0.1

- Fixes in documentation

## v1.0.0

- Initial version
