module Henry.Category.Monad where

open import Henry.Category.Functor using (Functor)
open import Henry.Category.Applicative using (Applicative)

open import Function
open import Level

private
  variable
    ℓ ℓ′ : Level

open Applicative

record Monad (M : Set ℓ → Set ℓ′) {{_ : Functor M}} {{Applicative-M : Applicative M}} : Set (suc ℓ ⊔ ℓ′) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    _>>=_ : ∀ {A B : Set ℓ} → M A → (A → M B) → M B

  return : ∀ {A : Set ℓ} → A → M A
  return = pure Applicative-M

  _>>_ : ∀ {A B : Set ℓ} → M A → M B → M B
  m >> m′ = m >>= λ a → m′

  _>=>_ : ∀ {A B C : Set ℓ} → (A → M B) → (B → M C) → (A → M C)
  f >=> g = λ { a →  f a >>= g }

  _=<<_ : ∀ {A B : Set ℓ} → (A → M B) → M A → M B
  f =<< m = m >>= f

  _<=<_ : ∀ {A B C : Set ℓ} → (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

open Monad {{...}} public
