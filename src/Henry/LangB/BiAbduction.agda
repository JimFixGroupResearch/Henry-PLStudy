module Henry.LangB.BiAbduction where


--
-- Imports
--

open import Function
import Level

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


syntax Abductive-Judgement Δ M H = Δ ⋆[ M ]▹ H

data Abductive-Judgement : Concrete → Symbolic → Symbolic → Set where

  remove : ∀ (Π Π′ : Pure) (Σ Σ′ : Spacial) (â : List LVar) (M H : Symbolic)
    → (Π ₚ∧ₛ Σ) ⋆[ M ]▹ H
    → ([] , Π ₚ∧ₛ Σ) ⊢ (â , Π′ , true)
    → ([] , Π ₚ∧ₚ Π′ , empty) ⊢ ([] , true , Σ′)
    ----------------------------------------------
    → (Π ₚ∧ₛ Σ) ⋆[ M ]▹ (H ∧⋆ (â , Π′ , Σ′))

  match : ∀ (E E₀ E₁ : Term) (Δ Δ′ : Concrete) (â b̂ : List LVar) (M : Symbolic)
    → ((E₀ =ₜ E₁ , true) ∧ Δ) ⋆[ M ]▹ (b̂ , Δ′)
    ---
    → (Δ ⋆ₛ predₛ[ E ↦ₛ E₀ ]) ⋆[ (â , (E₀ =ₜ E₁) , true) ∧⋆ M ]▹
      (â ++ b̂ , Δ′ ⋆ (true , predₛ[ E ↦ₛ E₁ ]))


postulate
  from-Abductive-Entails :
    ∀ (Δ@(Δₚ , Δₛ) : Concrete) (M@(Mₗ , Mₚ , Mₛ) : Symbolic) (H : Symbolic)
    → Δ ⋆[ M ]▹ H
    --------------------------------
    → ([] , Δ) ∧⋆ M ⊢ H

--
-- Frame
--


{-
  frame(H₀, H₁) = L such that H₀ ⊢ H₁ ⋆ L
-}

postulate
  frame : (H₀ H₁ : Symbolic)
    → Maybe (Σ[ L ∈ Symbolic ] H₀ ⊢ H₁ ∧⋆ L)
  

--
-- Abduction (get anti-frame)
--


{-
  abduce(Δ, H) = M such that Δ ⋆ M ⊢ H
-}

postulate
  abduce : (Δ : Concrete) (H : Symbolic)
    → Maybe (Σ[ M ∈ Symbolic ] ([] , Δ) ∧⋆ M ⊢ M)


--
-- BiAbduction
--


{-
  biabduce(Δ, H) = M , L
    where
      M = Abduce(Δ, H ⋆ true)
      L = Frame(Δ ⋆ M, H)
-}

biabduce : Concrete → Symbolic → Maybe (Symbolic × Symbolic)
biabduce Δ H = do
  M ← proj₁ <$> abduce Δ (H ∧⋆ ([] , true , true))
  L ← proj₁ <$> frame (([] , Δ) ∧⋆ M) H
  return (M , L)
