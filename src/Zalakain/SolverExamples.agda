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

_ : (xs : List A)
  → [] ++ xs ≡ xs ++ []
_ = λ xs → solve {1} (((ε′ ∙′ var′ zero) ≡′ (var′ zero ∙′ ε′))) (xs ∷ [])


_ : (xs ys zs : List A) →
    xs ++ ys ++ zs ≡ xs ++ ys ++ zs
_ = λ xs ys zs →
  solve {3}
    ((a ∙′ b) ∙′ c) ≡′ (a ∙′ (b ∙′ c))
    (xs ∷ ys ∷ zs ∷ [])
  where
    a : Expression 3
    a = var′ (Fin.raise 2 (Fin.fromℕ 0))
    b : Expression 3
    b = var′ (Fin.raise 1 (Fin.fromℕ 1))
    c : Expression 3
    c = var′ (Fin.raise 0 (Fin.fromℕ 2))
