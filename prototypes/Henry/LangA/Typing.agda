open import Data.List as List
open import Data.Maybe as Maybe
open import Data.Product as Product
open import Data.String as String
open import Data.Unit as Unit
open import Data.Nat as Nat
open import Data.Bool as Bool

open import Agda.Builtin.Nat as BuiltinNat
open import Agda.Builtin.Bool as BuiltinBool

-- open import Relation

open import LangA.Grammar as Grammar

module LangA.Typing where

data Type-Variable : Set where
  bound : Type → Type-Variable
  free  : String → Type-Variable

record Typing-Context : Set where
  constructor make-Typing-Context
  field
    names : List (Term-Name × Type-Variable)

open Typing-Context

find : ∀ {A : Set} → String → List (String × A) → Maybe A
find k′ [] = nothing
find k′ ((k , v) ∷ ls) = if k′ String.== k then just v else find k′ ls

type-name : Typing-Context → Term-Name → Maybe Type-Variable
type-name Γ n = find n (names Γ)

type-term : Typing-Context → Term → Maybe Type-Variable
type-term Γ (name n) = type-name Γ n
type-term Γ (natural x) = just (bound natural)
type-term Γ (boolean x) = just (bound boolean)
type-term Γ nil = just {!!}
type-term Γ (app t t₁) = {!!}
