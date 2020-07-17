module Henry.LangB.Grammar.Base where


--
-- Imports
--


open import Data.List hiding (and; or)
open import Data.String
open import Data.Product
open import Data.Nat


--
-- Type
--


data Type : Set where
  natural  : Type
  list     : Type
  function : List Type → Type → Type
  

--
-- Term
--


Var : Set
Var = String

data Term : Set where
  var : Var → Term
  nat : ℕ → Term
  nil : Term
  app : Term → Term → Term

infixr 5 app

syntax var x = ` x
-- syntax nat n = ...
pattern `[] = nil
syntax app h t = h `∷ t


--
-- Pointer
--


data Pointer : Set where
  pointer : String → Pointer

syntax pointer p = `* p


--
-- Formula
--


module Formula where

  -- logic variable
  LVar : Set
  LVar = String

  data Pure : Set where
    equal : Term → Term → Pure
    unequal : Term → Term → Pure
    true : Pure
    and : Pure → Pure → Pure

  data Spacial-Predicate : Set where
    points : Term → Term → Spacial-Predicate
    list-segment : Term → Term → Spacial-Predicate

  data Spacial : Set where
    predicate : Spacial-Predicate → Spacial
    true : Spacial
    empty : Spacial
    seperately : Spacial → Spacial → Spacial

  Concrete : Set
  Concrete = Pure × Spacial

  Symbolic : Set
  Symbolic = List LVar → Concrete

  Formula : Set
  Formula = Symbolic

open Formula using (Formula) public


--
-- Statement
--


data Statement : Set where
  pass     : Statement
  sequence : List Statement → Statement
  assert   : Formula → Statement
  -- control structures
  branch   : Term → Statement → Statement → Statement
  loop     : Term → Formula → Statement → Statement
  -- variables
  declare  : Var → Type → Term → Statement
  assign   : Var → Term → Statement
  -- pointers
  allocate : Pointer → Type → Term → Statement
  write    : Pointer → Term → Statement
  read     : Var → Pointer → Statement
  -- functions
  function : Term → List (Var × Type) → Formula → Formula → Statement → Statement
  apply    : Var → Var → List Term → Statement

syntax branch a s₁ s₂ = `if a `then s₁ `else s₂
syntax loop a φᵢ s = `while a `invariant φᵢ `do s
syntax declare x α a = `declare x `: α `≔ a
syntax assign x a = x `≔ a
syntax allocate p α a = `allocate p `: α `↦ a
syntax write p a = p `↦ a
syntax read x p = x `← p

--
-- Program
--


data Program : Set where
  program : Statement → Program

