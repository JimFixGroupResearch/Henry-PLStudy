module Henry.LangB.BiAbduction where


--
-- Imports
--


open import Function
import Level

open import Relation.Nullary

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
open import Henry.LangB.Hoare as Hoare

open Monad.RawMonad (MaybeCategorical.monad {Level.zero})


--
-- Abductive Inference
--


infix 4 Abductive-Judgement
syntax Abductive-Judgement Δ M H = Δ ⋆⟦ M ⟧▹ H

data Abductive-Judgement : Concrete → Symbolic → Symbolic → Set where

  remove : ∀ (Π Π′ : Pure) (Σ Σ′ : Spacial) (â : List LVar) (M H : Symbolic)
    → (Π ₚ∧ₛ Σ) ⋆⟦ M ⟧▹ H
    → ∃ₗ[] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π′ ₚ∧ₛ trueₛ
    → ∃ₗ[] Π ₚ∧ₚ Π′ ₚ∧ₛ empty ⊢ ∃ₗ[] trueₚ ₚ∧ₛ Σ′
    ----------------------------------------------
    → Π ₚ∧ₛ Σ ⋆⟦ M ⟧▹ H ⋆ (∃ₗ[ â ] (Π′ ₚ∧ₛ Σ′))

  match : ∀ (T T₀ T₁ : Term) (Δ Δ′ : Concrete) (â b̂ : List LVar) (M : Symbolic)
    → (T₀ =ₜ T₁ ₚ∧ₛ trueₛ) ∧ Δ ⋆⟦ M ⟧▹ ∃ₗ[ b̂ ] Δ′
    -------------------------------------------------------------------------------------------
    → (Δ ⋆ₛ T ↦ₛ T₀) ⋆⟦ (∃ₗ[ â ] T₀ =ₜ T₁ ₚ∧ₛ trueₛ) ⋆ M ⟧▹ ∃ₗ[ â ++ b̂ ] Δ′ ∧ trueₚ ₚ∧ₛ T ↦ₛ T₁
    -- additionally: where b̂ ∩ FreeLVar(T₁) = ∅

  lseg-right : ∀ (T₀ T₁ T : Term) (B : Spacial-Predicate-Binary)
                 (Δ Δ′ : Concrete) (â b̂ : List LVar) (M : Symbolic)
    → Δ ⋆⟦ M ⟧▹ ∃ₗ[ â ] Δ′ ∧ trueₚ ₚ∧ₛ lseg T₀ T₁
    ------------------------------------------------------------------------
    → Δ ∧ trueₚ ₚ∧ₛ pred₂ B T T₀ ⋆⟦ M ⟧▹ ∃ₗ[ â ++ b̂ ] Δ′ ∧ trueₚ ₚ∧ₛ T ↦ₛ T₁

  base-empty : ∀ (Π Π′ : Pure) (â : List LVar) →
    -------------------------------------------------------------
    Π ₚ∧ₛ empty ⋆⟦ ∃ₗ[ â ] Π′ ₚ∧ₛ empty ⟧▹ ∃ₗ[ â ] Π′ ₚ∧ₛ empty

  base-true : ∀ (Π : Pure) (Δ : Concrete) (â : List LVar)
    ------------------------------------------------
    → Δ ⋆⟦ ∃ₗ[ â ] Π ₚ∧ₛ empty ⟧▹ ∃ₗ[] Π ₚ∧ₛ empty

  missing : ∀ (B : Spacial-Predicate-Binary) (T E′ : Term)
              (Δ Δ′ : Concrete) (â : List LVar) (M : Symbolic)
    → Δ ⋆⟦ M ⟧▹ ∃ₗ[] Δ′
    → ((∃ₗ[] Δ) ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′)) ⊬ contradiction
    -------------------------------------------------------------------------------------------
    → Δ ⋆⟦ M ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′) ⟧▹ (∃ₗ[] Δ′) ⋆ (∃ₗ[ â ] trueₚ ₚ∧ₛ pred₂ B T E′)


postulate
  from-Abductive-Entails : ∀ (Δ : Concrete) (M : Symbolic) (H : Symbolic)
    → Δ ⋆⟦ M ⟧▹ H
    --------------------
    → (∃ₗ[] Δ) ⋆ M ⊢ H


--
-- Frame
--


{-
  frame(H₀, H₁) = L such that H₀ ⊢ H₁ ⋆ L, or fails
-}

postulate
  frame : (H₀ H₁ : Symbolic)
    → Maybe (Σ[ L ∈ Symbolic ] H₀ ⊢ H₁ ⋆ L)
  

--
-- Abduction (get anti-frame)
--


{-
  abduce(Δ, H) = M such that Δ ⋆ M ⊢ H, or fails
-}

postulate
  abduce : (Δ : Concrete) (H : Symbolic)
    → Maybe (Σ[ M ∈ Symbolic ] (∃ₗ[] Δ) ⋆ M ⊢ M)


--
-- BiAbduction
--


{-
  biabduce(Δ, H) = M , L
    where
      M = Abduce(Δ, H ⋆ true)
      L = Frame(Δ ⋆ M, H),
    or fails
-}

biabduce : (Δ : Concrete) (H : Symbolic)
  → Maybe (Σ[ (M , L) ∈ Symbolic × Symbolic ] (∃ₗ[] Δ) ⋆ M ⊢ H ⋆ L)
biabduce Δ H = do
  M , pM ← abduce Δ (H ⋆ (∃ₗ[] true))
  L , pL ← frame ((∃ₗ[] Δ) ⋆ M) H
  return ((M , L) , pL)
