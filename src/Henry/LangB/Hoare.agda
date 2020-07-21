module Henry.LangB.Hoare where


--
-- Imports
--


open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Data.Maybe

open import Henry.LangB.Grammar as Grammar


--
--
--


record Hoare-Triple : Set where
  constructor
    hoare-triple
  field
    pre  : Symbolic
    body : Statement
    post : Symbolic

open Hoare-Triple

--
--
--


postulate
  weakest-precondition : Statement → Symbolic

postulate
  strongest-postcondition : Statement → Symbolic

infer-hoare-triple : Statement → Hoare-Triple
infer-hoare-triple s = hoare-triple H₀ s H₁
  where
    H₀ = weakest-precondition s
    H₁ = strongest-postcondition s


--
-- Inference
--

infix 5 Judgement _⊬_

syntax Judgement H₀ H₁ = H₀ ⊢ H₁

data Judgement : Symbolic → Symbolic → Set where

  -- pure

  intro-trueₚ : ∀ Π Σ â
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₚ trueₚ ₚ∧ₛ Σ

  from-falseₚ : ∀ Σ â
    → ∃ₗ[ â ] falseₚ ₚ∧ₛ Σ ⊢ contradiction

  intro-equal : ∀ T₁ T₂ Π Σ â
    → T₁ ≡ T₂
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₚ T₁ =ₜ T₂ ₚ∧ₛ Σ

  intro-unequal : ∀ T₁ T₂ Π Σ â
    → ¬ T₁ ≡ T₂
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₚ T₁ ≠ₜ T₂ ₚ∧ₛ Σ

  -- TODO: not sure if this is right
  intro-and : ∀ Π₁ Π₂ Σ H â
    → H ⊢ ∃ₗ[ â ] Π₁ ₚ∧ₛ Σ
    → H ⊢ ∃ₗ[ â ] Π₂ ₚ∧ₛ Σ
    → H ⊢ ∃ₗ[ â ] Π₁ ₚ∧ₚ Π₂ ₚ∧ₛ Σ

  elim-and₁ : ∀ Π₁ Π₂ Σ â
    → ∃ₗ[ â ] Π₁ ₚ∧ₚ Π₂ ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π₁ ₚ∧ₛ Σ

  elim-and₂ : ∀ Π₁ Π₂ Σ â
    → ∃ₗ[ â ] Π₁ ₚ∧ₚ Π₂ ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π₂ ₚ∧ₛ Σ

  -- spacial

  intro-trueₛ : ∀ Δ â
    → ∃ₗ[ â ] Δ ⊢ ∃ₗ[ â ] Δ ∧ₛ trueₛ

  from-falseₛ : ∀ Π â
    → ∃ₗ[ â ] Π ₚ∧ₛ falseₛ ⊢ contradiction

  -- TODO: not sure if this is right
  intro-sep : ∀ Π Σ₁ Σ₂ H â
    → H ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₁
    → H ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₂
    → H ⊢ ∃ₗ[ â ] Π ₚ∧ₛ (Σ₁ ₛ⋆ₛ Σ₂)

  elim-sep₁ : ∀ Π Σ₁ Σ₂ â
    → ∃ₗ[ â ] Π ₚ∧ₛ (Σ₁ ₛ⋆ₛ Σ₂) ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₁

  elim-sep₂ : ∀ Π Σ₁ Σ₂ â
    → ∃ₗ[ â ] Π ₚ∧ₛ (Σ₁ ₛ⋆ₛ Σ₂) ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₂

  -- concrete

  and-comm : ∀ Δ₁ Δ₂ â
    → ∃ₗ[ â ] Δ₁ ∧ Δ₂ ⊢ ∃ₗ[ â ] Δ₂ ∧ Δ₁

  -- symbolic

  sep-comm : ∀ H₁ H₂
    → H₁ ⋆ H₂ ⊢ H₂ ⋆ H₁

  elim-false : ∀ H
    → contradiction ⊢ H

_⊬_ : Symbolic → Symbolic → Set
H₀ ⊬ H₁ = ¬ (H₀ ⊢ H₁)


--
-- Inference solving
--

postulate
  infer : ∀ H₁ H₂ → Maybe (H₁ ⊢ H₂)

{- OLD
postulate
  -- given H₁ H₂ evaluates to
  --   ⊤       , if H₁ ⊬ H₂ is inhabited
  --   H₁ ⊢ H₂ , if H₁ ⊢ H₂ is inhabited
  Inference : Symbolic → Symbolic → Set

  -- given H₁ H₂ evaluates to
  --   tt : ⊤       , if H₁ ⊬ H₂ is inhabited
  --   pf : H₁ ⊢ H₂ , if H₁ ⊢ H₂ is inhabited
  infer : ∀ H₁ H₂ → Inference H₁ H₂
-}

Valid : Hoare-Triple → Set 
Valid ht = pre ht ⊢ post ht
