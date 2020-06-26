module Henry.LangA.Grammar.Base where

---
--- Imports
---


-- Data
open import Data.List
open import Data.String
open import Data.Nat
open import Data.Bool
open import Data.Fin


--
-- Term
--


data Term-Atom : Set where
  name : String → Term-Atom

data Term : Set where
  atom        : Term-Atom → Term
  function    : Term-Atom → Term → Term
  application : Term → Term → Term


--
-- Type
--


data Type-Atom : Set where
  natural : Type-Atom
  boolean : Type-Atom
  list    : Type-Atom

data Type : Set where
  atom        : Type-Atom → Type
  function    : Type-Atom → Type → Type
  application : Type → Type → Type


--
-- Kind
--


data Kind-Atom : Set where
  mono : Kind-Atom

data Kind : Set where
  atom  : Kind-Atom → Kind
  arrow : Kind → Kind → Kind


-- 
-- Register
--


-- heap has n registers
data Register (n : ℕ) : Set where
  register : Fin n → Register n

--
-- Formula
--


data Formula : Set where
  term : Term → Formula


--
-- Statement
--


data Statement (n : ℕ) : Set where
  pass        : Statement n
  declaration : Type → Term-Atom → Term → Statement n
  assignment  : Term-Atom → Term → Statement n
  allocation  : Register n → Term → Statement n
  write       : Register n → Term → Statement n
  read        : Term-Atom → Register n → Statement n
  assert      : Formula → Statement n


Program = ∀(n : ℕ) → List (Statement n)
