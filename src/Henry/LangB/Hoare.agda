module Henry.LangB.Hoare where


--
-- Imports
--


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
