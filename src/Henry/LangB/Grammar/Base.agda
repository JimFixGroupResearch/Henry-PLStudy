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
  natural : Type
  list : Type
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
  app : Term


--
-- Pointer
--


data Pointer : Set where
  pointer : String → Pointer


--
-- Formula
--


data Formula : Set where
  -- terms
  check : Term → Formula
  equal : Term → Term → Formula
  unequal : Term → Term → Formula
  -- pointers
  allocated : Pointer → Formula
  points : Pointer → Term → Formula
  -- junctions
  not : Formula → Formula
  and : Formula → Formula → Formula
  or : Formula → Formula → Formula
  sep : Formula → Formula → Formula -- seperately and
  

--
-- Statement
--


data Statement : Set where
  pass : Statement
  sequence : List Statement → Statement
  assert : Formula → Statement
  -- control structures
  branch : Term → Statement → Statement → Statement
  loop : Term → Statement → Statement
  -- variables
  declare : Var → Type → Statement
  assign : Var → Term → Statement
  -- pointers
  allocate : Pointer → Type → Statement
  write : Pointer → Term → Statement
  read : Var → Pointer → Statement
  -- functions
  function : Term → List (Var × Type) → Formula → Formula → Statement → Statement
  apply : Term → Term → List Term → Statement


--
-- Program
--


data Program : Set where
  program : Statement → Program

