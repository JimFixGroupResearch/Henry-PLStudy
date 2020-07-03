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
  arrow : List Type → Type → Type
  

--
-- Term
--


data Term : Set where
  var : String → Term
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
  equal : Term → Term → Formula
  points : Pointer → Term → Formula
  allocated : Pointer → Formula
  and : Formula → Formula → Formula
  or : Formula → Formula → Formula
  sep : Formula → Formula → Formula -- seperately and
  

--
-- Statement
--


data Statement : Set where
  pass : Statement
  sequence : List Statement → Statement
  -- control structures
  branch : Term → Statement → Statement → Statement
  loop : Term → Statement → Statement
  -- variables
  declare : String → Type → Statement
  assign : String → Term → Statement
  -- pointers
  allocate : String → Type → Statement
  write : Pointer → Term → Statement
  read : String → Pointer → Statement
  -- functions
  function : Term → List (String × Type) → Statement → Statement
  apply : Term → Term → List Term → Statement


--
-- Program
--


data Program : Set where
  program : Statement → Program

