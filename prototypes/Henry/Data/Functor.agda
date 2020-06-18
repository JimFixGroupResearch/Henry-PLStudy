module Henry.Data.Functor where

open import Level

private
  variable
    ℓ ℓ′ : Level

record Functor (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  infixl 4 _<$>_

  field
    _<$>_ : ∀ {A B : Set ℓ} → (A → B) → F A → F B
    
