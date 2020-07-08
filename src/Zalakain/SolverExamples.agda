module Zalakain.SolverExamples {A : Set} where

open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Unit as Unit using (⊤; tt)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Nat as Nat using (ℕ)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.List as List using (List; _++_; [])
import Data.List.Properties as ListProperties
open import Data.Product as Product

open import Zalakain.Solver {A = List A} _++_ [] ListProperties.++-isMonoid as Solver

_ : ∀ xs →
  [] ++ xs ≡ xs ++ []
_ = λ xs → solve {1} eq (xs ∷ []) where
  eq = ((ε′ ∙′ var′ zero) ≡′ (var′ zero ∙′ ε′))


_ : ∀(xs ys zs : List A) →
  ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
_ = λ(xs ys zs : List A) → solve {3} eq (xs ∷ ys ∷ zs ∷ []) where
  a : Expression 3
  a = var′ zero
  b : Expression 3
  b = var′ (suc zero)
  c : Expression 3
  c =  var′ (suc (suc zero))
  eq = ((a ∙′ b) ∙′ c) ≡′ (a ∙′ (b ∙′ c))



Builder-Params : ℕ → ℕ → Set
Builder-Params m Nat.zero = Expression m
Builder-Params m (Nat.suc n) = Expression m → Builder-Params m n
  
Builder : ℕ → Set
Builder Nat.zero = ⊤
Builder m@(Nat.suc n) = (Builder-Params m n → Equation m) → Equation m where


build : ∀ n → Builder n
build Nat.zero = tt
build (Nat.suc n) = λ f → f (build-params n n) where 
  build-params : ∀ m n → Builder-Params (Nat.suc m) n
  build-params m Nat.zero = var′ zero
  build-params m (Nat.suc n) = λ v → build-params m n

-- ((Solver.Expression 2 →
--   Solver.Expression 2) →
--  Zalakain.Solver.Equation _++_ [] ListProperties.++-isMonoid 1) →
-- Zalakain.Solver.Equation _++_ [] ListProperties.++-isMonoid 1

-- Builder-Params : {ℕ} → ℕ → Set
-- Builder-Params {m} Nat.zero = Expression m
-- Builder-Params {m} (Nat.suc n) = Expression m → Builder-Params {m} n

-- Builder : {ℕ} → ℕ → Set
-- Builder {m} Nat.zero = ⊤
-- Builder {m} (Nat.suc n) = Builder-Params {m} n → Equation m where

-- builder : {m : ℕ} (n : ℕ) → Builder {m} n
-- builder {m} Nat.zero = tt
-- builder {m} (Nat.suc Nat.zero) = {!!}
-- builder {m} (Nat.suc (Nat.suc n)) = {!!}


  -- helper : ∀ n → (Expression m → Builder-Params n) → Equation m
  -- helper Nat.zero f = {!var′ zero!}
  -- helper (Nat.suc n) f = {!!}


-- Builder 2 = (Expression 2 → Expression 2 → Equation 2) → Equation 2
