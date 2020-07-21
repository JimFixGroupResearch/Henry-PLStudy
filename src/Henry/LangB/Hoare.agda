module Henry.LangB.Hoare where


--
-- Imports
--


open import Relation.Nullary

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


--
--
--


postulate
  weakest-precondition : Statement → Symbolic

postulate
  strongest-postcondition : Statement → Symbolic

infer-hoare-triple : Statement → Hoare-Triple
infer-hoare-triple s = hoare-triple φ s ψ
  where
    φ = weakest-precondition s
    ψ = strongest-postcondition s


--
--
--

data Judgement : Symbolic → Symbolic → Set where

infix 5 Judgement _⊬_
syntax Judgement H₀ H₁ = H₀ ⊢ H₁

_⊬_ : Symbolic → Symbolic → Set
H₀ ⊬ H₁ = ¬ (H₀ ⊢ H₁)
