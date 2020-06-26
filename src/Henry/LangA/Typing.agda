module Henry.LangA.Typing where

---
--- Imports
---

open import Level as Level using (Level)
open import Function

-- Monad
open import Category.Monad as Monad
open import Category.Monad.State as State

-- Data
open import Agda.Builtin.Nat as BuiltinNat
open import Agda.Builtin.Bool as BuiltinBool
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.String as String
open import Data.Unit as Unit
open import Data.Nat as Nat
open import Data.Bool as Bool
open import Henry.Data.StringDictionary as StringDictionary

-- Classes
open import Henry.Class.Equalable
open import Henry.Class.Equalable.Instances

-- LangA
open import Henry.LangA.Grammar as Grammar


--
-- Type Variable
--


data Type-Variable : Set where
  bound      : Type → Type-Variable
  bound-poly : (Type → Type) → Type-Variable → Type-Variable
  free       : ℕ → Type-Variable


--
-- Typing Context
--


record Typing-Context : Set where
  constructor make-Γ
  field
    fresh-id : ℕ
    type-variables : StringDictionary Type-Variable

open Typing-Context


--
-- Typing State
--


module Typing-State where

  open Monad.RawMonad (StateMonad Typing-Context) public

  Typing-State : Set → Set
  Typing-State A = State Typing-Context A

  -- Utilities

  find-type-variable : Term-Name → Typing-State (Maybe Type-Variable)
  find-type-variable n Γ = (find n (type-variables Γ)) , Γ

  update-type-variable : Term-Name → Type-Variable → Typing-State ⊤
  update-type-variable n α Γ = tt , record Γ { type-variables = type-variables Γ ⟦ n ⟧∷= α }

  fresh-type-variable : Term-Name → Typing-State Type-Variable
  fresh-type-variable n Γ = α , Γ′ where
    α = free (fresh-id Γ)
    Γ′ = record Γ { fresh-id = suc (fresh-id Γ)
                  ; type-variables = (type-variables Γ) ⟦ n ⇒ α ⟧ }
         
open Typing-State


--
--
--

unify : Type-Variable → Type-Variable → Typing-State Type-Variable
unify (bound a) (bound b) = {!!}
unify (bound a) (bound-poly x₁ β) = {!!}
unify (bound a) (free x₁) = {!!}
unify (bound-poly f α) β = {!!}
unify (free α) β = {!!}


type-name : Term-Name → Typing-State Type-Variable
type-name n = find-type-variable n >>=
  λ { nothing → fresh-type-variable n
    ; (just α) → return α }

type-term : Term → Typing-State Type-Variable
type-term (name n) = type-name n
type-term (natural x) = return (bound natural)
type-term (boolean x) = return (bound boolean)
type-term nil = fresh-type-variable "nil" >>= return ∘ bound-poly list
type-term (app h t) = do
  α ← type-term h
  β ← type-term t
  return =<< unify α β
