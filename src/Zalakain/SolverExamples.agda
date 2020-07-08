module Zalakain.SolverExamples {A : Set} where

open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Unit as Unit using (⊤; tt)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Properties as NatProperties
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.List as List using (List; _++_; [])
import Data.List.Properties as ListProperties
open import Data.Product as Product

open import Zalakain.Solver {A = List A} _++_ [] ListProperties.++-isMonoid as Solver


--
-- examples
--


_ : ∀(a : List A)                      → [] ++ a ≡ a ++ []
_ = λ(a : List A) → solve (build 1 λ a → ε′ ∙′ a ≡′ a ∙′ ε′) (a ∷ [])

_ : ∀(a b : List A)                        → a ++ [] ++ b ≡  a ++ b
_ = λ(a b : List A) → solve (build 2 λ a b → a ∙′ ε′ ∙′ b ≡′ a ∙′ b) (a ∷ b ∷ [])

_ : ∀(a b c : List A)                          → (a ++ b) ++ c ≡  a ++ (b ++ c)
_ = λ(a b c : List A) → solve (build 3 λ a b c → (a ∙′ b) ∙′ c ≡′ a ∙′ (b ∙′ c)) (a ∷ b ∷ c ∷ [])
