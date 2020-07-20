module Henry.LangB.Grammar.Substitution where

--
-- Imports
--


open import Relation.Nullary as Nullary

open import Data.Product as Product
open import Data.String as String
open import Data.Bool as Bool

open import Henry.LangB.Grammar.Base


--
-- Substitution
--

Substitution : Set → Set
Substitution A = (Var × Term) → A → A

postulate
  substitute-var-in-term : Substitution Term
  substitute-var-in-formula : Substitution Symbolic
  substitute-var-in-statement : Substitution Statement
