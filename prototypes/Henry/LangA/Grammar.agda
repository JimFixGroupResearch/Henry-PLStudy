open import Data.List
open import Data.String
open import Data.Nat
open import Data.Bool

module LangA.Grammar where

data Register : Set where
  reg-A : Register
  reg-B : Register

Term-Name : Set
Term-Name = String

data Term : Set where
  -- name
  name : Term-Name → Term
  -- primitive
  natural : ℕ → Term
  boolean : Bool → Term
  -- list
  nil : Term
  app : Term → Term → Term

data Type : Set where
  -- primitive
  natural : Type
  boolean : Type
  -- higher-order
  list : Type → Type

data Formula : Set where
  -- term required to type as boolean
  term : Term → Formula

data Statement : Set where
  pass        : Statement
  declaration : Type → Term-Name → Term → Statement
  assignment  : Term-Name → Term → Statement
  allocation  : Register → Term → Statement
  write       : Register → Term → Statement
  read        : Term-Name → Register → Statement
  assert      : Formula → Statement

Program = List Statement
