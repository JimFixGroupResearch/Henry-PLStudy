module Henry.LangB.BiAbduction where


--
-- Imports
--

open import Function

open import Data.Unit as Unit
open import Data.Empty as Empty
open import Data.List as List hiding ([_])
open import Data.Bool as Bool
open import Data.String as String
open import Data.Sum as Sum
open import Data.Product as Product

import Category.Functor as Functor
import Category.Monad as Monad
import Category.Monad.State as State

open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Categorical renaming (monad to maybeMonad)

open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar
open import Henry.LangB.Hoare as Haore


--
-- Abductive Inference
--


data Judgement : Set where
  judgement : Formula.Concrete → Formula.Symbolic → Formula.Symbolic → Judgement

_⋆[_]▹_ : Formula.Concrete → Formula.Symbolic → Formula.Symbolic → Judgement
_⋆[_]▹_ = judgement


--
-- Frame
--

{-
  Frame(H₀, H₁) = L such that H₀ ⊢ H₁ ⋆ L
-}



--
-- Abduction (get anti-frame)
--

{-
  Abduce(Δ, H) = M such that Δ ⋆ M ⊢ H
-}


--
-- BiAbduction
--

{-
  BiAbduce(Δ, H) = M , L
    where
      M = Abduce(Δ, H ⋆ true)
      L = Frame(Δ ⋆ M, H)
-}
