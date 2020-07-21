module Henry.LangB.BiAbductionExamples where


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
open import Henry.LangB.BiAbduction as BiAbduction


--
-- Examples (from biabduction paper)
--

-- example 1
_ : let x = ` "x" in
    let y = ` "y" in
    let a = ` "a" in
    let v0 = ` "v0" in
  true ₚ∧ₛ x ↦ₛ y ⋆⟦ ∃ₗ[] y =ₜ a ₚ∧ₛ lseg a v0 ⟧▹ ∃ₗ[] true ₚ∧ₛ (x ↦ₛ a ₛ⋆ₛ lseg a v0)
_ = {!!}
