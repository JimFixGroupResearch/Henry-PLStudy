module Henry.LangB.Grammar.Properties where

--
-- Imports
--

open import Function
open import Level
open import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Negation as Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropositionalEquality
open import Relation.Binary.Definitions

open import Data.Empty
open import Data.String as String using (String)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)

import Henry.LangB.Grammar.Base as Grammar


--
--
--


module Type where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Type} _≡_
