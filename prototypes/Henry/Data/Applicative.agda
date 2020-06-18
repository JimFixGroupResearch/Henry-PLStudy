module Henry.Data.Applicative where

open import Henry.Data.Functor using (Functor)
open import Level

private
  variable
    ℓ ℓ′ : Level

record Applicative (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  infixl 4 _⊛_

  field
    functor : Functor F
    pure    : ∀ {A   : Set ℓ} → F A
    _⊛_     : ∀ {A B : Set ℓ} → F (A → B) → F A → F B
