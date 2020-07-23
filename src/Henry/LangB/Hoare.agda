module Henry.LangB.Hoare where


--
-- Imports
--


open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Data.Maybe

open import Henry.LangB.Grammar as Grammar


--
--
--


record Hoare-Triple : Set where
  constructor
    hoare-triple
  field
    pre  : Symbolic
    body : Statement
    post : Symbolic

open Hoare-Triple


--
-- Hoare Inference
--


-- TODO
postulate
  weakest-precondition : Statement → Symbolic
  strongest-postcondition : Statement → Symbolic

infer-hoare-triple : Statement → Hoare-Triple
infer-hoare-triple s = hoare-triple H₀ s H₁
  where
    H₀ = weakest-precondition s
    H₁ = strongest-postcondition s
