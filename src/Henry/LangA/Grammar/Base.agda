module Henry.LangA.Grammar.Base where

---
--- Imports
---


-- Data
open import Data.List using (List; _∷_; [])
open import Data.String
open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.Maybe


--
-- Kind
--


data Kind-Atom : Set where
  mono : Kind-Atom

data Kind : Set where
  atom  : Kind-Atom → Kind
  arrow : Kind → Kind → Kind
  

--
-- Type
--


data Type-Atom : Set where
  unit    : Type-Atom
  boolean : Type-Atom
  natural : Type-Atom
  list    : Type-Atom
  arrow   : Type-Atom

data Type : Set where
  atom        : Type-Atom → Type
  function    : Type-Atom → Kind → Type → Type
  application : Type → Type → Type


data Type-Variable : Set where
  bound       : Type → Type-Variable
  free        : ℕ → Type-Variable
  application : Type-Variable → Type-Variable → Type-Variable
  


--
-- Term
--


data Term-Atom : Set where
  name : String → Term-Atom

data Term : Set where
  atom        : Term-Atom → Term
  function    : Term-Atom → Type → Term → Term
  application : Term → Term → Term


-- 
-- Pointer
--


-- heap has n pointers
data Pointer : Set where
  pointer : ℕ → Type → Pointer

--
-- Formula
--


data Formula : Set where
  assert   : Term → Formula
  equality : Term → Term → Formula
  pointing : Pointer → Maybe Term → Formula
  and      : Formula → Formula → Formula
  or       : Formula → Formula → Formula
  sep      : Formula → Formula → Formula


--
-- Statement
--


data Statement : Set where
  pass        : Statement
  declaration : Term-Atom → Type → Term → Statement
  assignment  : Term-Atom → Term → Statement
  allocation  : Pointer → Type → Statement
  write       : Pointer → Term → Statement
  read        : Pointer → Term-Atom → Statement
  assert      : Formula → Statement

data Program : Set where
  sequence : List (Statement) → Program


--
--
--


test-program-1 : Program
test-program-1 = sequence
  ( declaration (name "x") (atom boolean) (atom (name "true"))
  ∷ assert (equality (atom (name "x")) (atom (name "true")))
  ∷ [])
