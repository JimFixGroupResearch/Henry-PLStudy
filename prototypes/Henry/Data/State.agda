module Henry.Data.State where

open import Function
open import Level
open import Data.Product

open import Henry.Data.Monad

private
  variable
    ℓ ℓ′ : Level
    S : Set ℓ
    A : Set ℓ′

State : Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
State S A = S → (S × A)

MonadState : Monad (State S)
MonadState = {!!}
