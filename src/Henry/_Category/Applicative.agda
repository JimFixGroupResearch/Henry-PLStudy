module Henry.Category.Applicative where

open import Henry.Category.Functor using (Functor)
open import Level

private
  variable
    ℓ ℓ′ : Level

record Applicative (F : Set ℓ → Set ℓ′) {{_ : Functor F}} : Set (suc ℓ ⊔ ℓ′) where
  infixl 4 _⊛_
  field
    pure    : ∀ {A   : Set ℓ} → A → F A
    _⊛_     : ∀ {A B : Set ℓ} → F (A → B) → F A → F B


open Applicative {{...}} public
