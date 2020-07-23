module Henry.LangB.Abduction where


--
-- Imports
--


open import Function
import Level

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Unit as Unit
open import Data.Empty as Empty
open import Data.List as List hiding ([_])
open import Data.String as String hiding (_++_)
open import Data.Sum as Sum
open import Data.Product as Product hiding (Σ)

open import Category.Functor as Functor
open import Category.Monad as Monad

open import Data.Maybe as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MaybeCategorical

open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar
open import Henry.LangB.Inference as Inference

open Monad.RawMonad (MaybeCategorical.monad {Level.zero})


--
-- Abductive Inference
--


infix 4 Abductive-Judgement
syntax Abductive-Judgement Δ M H = Δ ⋆⟦ M ⟧▹ H

data Abductive-Judgement : Concrete → Symbolic → Symbolic → Set where

  remove : ∀ Π Π′ Σ Σ′ â M H
    → (Π ₚ∧ₛ Σ) ⋆⟦ M ⟧▹ H
    → ∃ₗ[] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π′ ₚ∧ₛ trueₛ
    → ∃ₗ[] Π ₚ∧ₚ Π′ ₚ∧ₛ empty ⊢ ∃ₗ[] trueₚ ₚ∧ₛ Σ′
    ----------------------------------------------
    → Π ₚ∧ₛ Σ ⋆⟦ M ⟧▹ H ⋆ (∃ₗ[ â ] (Π′ ₚ∧ₛ Σ′))

  match : ∀ T T₀ T₁ Δ Δ′ â b̂ M
    → (T₀ =ₚ T₁ ₚ∧ₛ trueₛ) ∧ Δ ⋆⟦ M ⟧▹ ∃ₗ[ b̂ ] Δ′
    ---------------------------------------------------------------------------------------------
    → (Δ ⋆ₛ T ↦ₛ T₀) ⋆⟦ (∃ₗ[ â ] T₀ =ₚ T₁ ₚ∧ₛ trueₛ) ⋆ M ⟧▹ ∃ₗ[ â ++ b̂ ] Δ′ ∧ trueₚ ₚ∧ₛ T ↦ₛ T₁
    -- additionally: where b̂ ∩ FreeLVar(T₁) = ∅

  lseg-right : ∀ T₀ T₁ T B Δ Δ′ â b̂ M
    → Δ ⋆⟦ M ⟧▹ ∃ₗ[ â ] Δ′ ∧ trueₚ ₚ∧ₛ lseg T₀ T₁
    --------------------------------------------------------------------------
    → Δ ∧ trueₚ ₚ∧ₛ pred₂ B T T₀ ⋆⟦ M ⟧▹ ∃ₗ[ â ++ b̂ ] Δ′ ∧ trueₚ ₚ∧ₛ T ↦ₛ T₁

  base-empty : ∀ Π Π′ â
    ---------------------------------------------------------------
    → Π ₚ∧ₛ empty ⋆⟦ ∃ₗ[ â ] Π′ ₚ∧ₛ empty ⟧▹ ∃ₗ[ â ] Π′ ₚ∧ₛ empty

  base-true : ∀ Π Δ â 
    ------------------------------------------------
    → Δ ⋆⟦ ∃ₗ[ â ] Π ₚ∧ₛ empty ⟧▹ ∃ₗ[] Π ₚ∧ₛ empty

  missing : ∀ B T E′ Δ Δ′ â M
    → Δ ⋆⟦ M ⟧▹ ∃ₗ[] Δ′
    → ((∃ₗ[] Δ) ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′)) ⊬ contradiction
    ---------------------------------------------------------------------------------------------
    → Δ ⋆⟦ M ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′) ⟧▹ (∃ₗ[] Δ′) ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′)


postulate
  from-Abductive-Entails : ∀ Δ M H
    → Δ ⋆⟦ M ⟧▹ H
    --------------------
    → (∃ₗ[] Δ) ⋆ M ⊢ H


--
-- Abduction
--


{-
  abduce(Δ, H) = M such that Δ ⋆ M ⊢ H, or fails
-}

postulate
  abduce : ∀ Δ H → Maybe (∃[ M ] ((∃ₗ[] Δ) ⋆ M ⊢ H))
