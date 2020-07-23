module Henry.LangB.Verification where


--
-- Imports
--

open import Function

open import Data.Unit as Unit
open import Data.Empty as Empty
open import Data.List as List hiding ([_])
-- open import Data.Bool as Bool
open import Data.String as String
open import Data.Sum as Sum
open import Data.Product as Product

import Category.Functor as Functor
import Category.Monad as Monad
import Category.Monad.State as State

open import Data.Maybe as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MaybeCategorical

open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar
open import Henry.LangB.Inference as Inference
open import Henry.LangB.BiAbduction as BiAbduction
open import Henry.LangB.Hoare as Hoare


--
-- Verification
--

{-

Example:

We are given two statements, and want to find
the Hoare triple corresponding to their sequence.

  x ≔ 1
  assert x =ₚ 1

To do this, first infer the Hoare triples for
each statement individually.
The pre- and post-conditions are Concretes.

  { H₀ }

  { trueₚ ₚ∧ₛ empty := Δ₁ }
    x ≔ 1
  { x =ₚ 1 ₚ∧ₛ empty =: Δ₂ }

  { x =ₚ 1 ₚ∧ₛ empty =: Δ₃ } 
    assert x =ₚ 1
  { x =ₚ 1 ₚ∧ₛ empty := Δ₄ }

  { H₅ }

We shall work from the bottom up.

1. compute H₄ := biabduce Δ₄ H₅ such that Δ₄ ⋆ H₄ ⊢ H₅.
2. compute H₃ := biabduce Δ₃ H₄ such that Δ₃ ⋆ H₃ ⊢ H₄
3. compute H₂ := biabduce Δ₂ H₃ such that Δ₂ ⋆ H₂ ⊢ H₃
4. compute H₁ := biabduce Δ₁ H₂ such that Δ₁ ⋆ H₁ ⊢ H₂

Then to check that the program is valid,
(satisfies the given pre-symbolic-condition and post-symbolic-condition)
compute infer H₀ H₁

-}




{- TODO: this is proper way of setting it up, but needs more thought
Verification : Program → Set
Verification = ?


verify : ∀ p → Verification p
verify p = ?
-}
