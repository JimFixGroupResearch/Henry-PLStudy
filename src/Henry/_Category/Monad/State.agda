module Henry.Category.Monad.State where

open import Function
open import Level
open import Data.Product

open import Henry.Category.Functor
open import Henry.Category.Applicative
open import Henry.Category.Monad

private
  variable
    ℓ ℓ′ : Level

State : Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
State S A = S → (S × A)

instance
  Functor-State : ∀ {S : Set ℓ} → Functor {ℓ′} {ℓ ⊔ ℓ′} (State S)
  _<$>_ {{Functor-State}} f sa = λ s → let (s′ , a) = sa s in s′ , f a


instance 
  Applicative-State : ∀ {S : Set ℓ} → Applicative {ℓ′} {ℓ ⊔ ℓ′} (State S)
  pure {{Applicative-State}} a = λ s → s , a
  _⊛_ {{Applicative-State}} sf sa = λ s →
    let (s′  , f) = sf s  in
    let (s′′ , a) = sa s′ in
    s′′ , f a

instance
  Monad-State : ∀ {S : Set ℓ} → Monad {ℓ′} {ℓ ⊔ ℓ′} (State S)
  _>>=_ {{Monad-State}} sa f = λ s → let (s′ , a) = sa s in (f a) s′
