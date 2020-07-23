module Henry.LangB.Framing where


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
open import Data.Product as Product

open import Category.Functor as Functor
open import Category.Monad as Monad

open import Data.Maybe as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MaybeCategorical

open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar
open import Henry.LangB.Inference as Inference

open Monad.RawMonad (MaybeCategorical.monad {Level.zero})


--
-- Frame
--


{-
  frame(H₀, H₁) = L such that H₀ ⊢ H₁ ⋆ L, or fails
-}

postulate
  frame : ∀ H₀ H₁ → Maybe (∃[ L ] (H₀ ⊢ H₁ ⋆ L))
