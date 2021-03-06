module Henry.LangB.BiAbduction where


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
open import Henry.LangB.Framing as Framing
open import Henry.LangB.Abduction as Abduction

open Monad.RawMonad (MaybeCategorical.monad {Level.zero})


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
