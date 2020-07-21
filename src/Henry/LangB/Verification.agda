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
open import Henry.LangB.Hoare as Hoare
open import Henry.LangB.BiAbduction as BiAbduction


--
-- Verification
--

Verification : Program → Set
Verification (program s) = Maybe (Valid (infer-hoare-triple s))

verify : (p : Program) → Verification p
verify p = {!!}
