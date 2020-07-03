module Henry.LangB.Typing where


open import Function
open import Level as Level using (Level)
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Category.Functor as Functor
open import Category.Monad as Monad
open import Category.Monad.State as State

open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Categorical renaming (monad to maybeMonad)

open import Data.Product as Product
open import Data.Sum as Sum
open import Data.String as String
open import Data.Unit as Unit
open import Data.Bool as Bool
open import Data.List as List
open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar


--
-- Typing Context
--


record Typing-Context : Set where
  constructor make-Γ
  field
    pointer-types : Dictionary String Type
    var-types : Dictionary String Type

open Typing-Context

empty : Typing-Context
empty = make-Γ
  (Dictionary.empty (λ x y → does (x String.≟ y)))
  (Dictionary.empty (λ x y → does (x String.≟ y)))


--
-- Typing-State
--


module Typing-State where

  open Monad.RawMonad (StateTMonad Typing-Context maybeMonad)
    using (return; _>>=_; _=<<_; _>>_; _<$>_) public
  open RawMonadState (StateTMonadState Typing-Context maybeMonad)
    using (monad; get; put) public

  Typing-State : Set → Set
  Typing-State = StateT Typing-Context Maybe

  -- stateful interactions

  get-pointer-type : String → Typing-State Type
  get-pointer-type p Γ = pointer-types Γ ⟦ p ⟧ Maybe.>>= λ ρ → just (ρ , Γ)

  set-pointer-type : String → Type → Typing-State ⊤
  set-pointer-type p ρ Γ = just (tt , Γ′) where
    Γ′ = record Γ { pointer-types = pointer-types Γ ⟦ p ⇒ ρ ⟧ }

  get-var-type : String → Typing-State Type
  get-var-type x Γ = var-types Γ ⟦ x ⟧ Maybe.>>= λ ξ → just (ξ , Γ)

  set-var-type : String → Type → Typing-State ⊤
  set-var-type x ξ Γ = just (tt , Γ′) where
    Γ′ = record Γ { var-types = var-types Γ ⟦ x ⇒ ξ ⟧ }

  -- utilities

  mal-typed : ∀{A} → Typing-State A
  mal-typed = λ _ → nothing

  well-typed : Typing-State ⊤
  well-typed = return tt

open Typing-State


--
-- Term
--


type-term : Term → Typing-State Type
type-term a = {!!}

check-statement : Statement → Typing-State ⊤
check-statement pass = well-typed
check-statement (sequence []) = well-typed
check-statement (sequence (s ∷ ss)) = check-statement s >> check-statement (sequence ss)
check-statement (branch c s₁ s₂) =
  get >>= λ Γ → const
    (check-statement s₁ Γ Maybe.>>= λ _ →
     check-statement s₂ Γ)
check-statement (loop x s) = check-statement s
check-statement (declare x ξ) = set-var-type x ξ
check-statement (assign x a) = do
  ξ ← get-var-type x
  α ← type-term a
  if does (ξ Grammar.Properties.Type.≟ α)
    then well-typed
    else mal-typed
check-statement (allocate p ρ) = {!!}
check-statement (write p a) = {!!}
check-statement (read x p) = {!!}
check-statement (function f xs s) = {!!}
check-statement (apply x f as) = {!!}

check-program : Program → Typing-State ⊤
check-program (program s) = check-statement s
