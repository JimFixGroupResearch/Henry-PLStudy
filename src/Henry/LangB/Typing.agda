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
open import Data.Bool as Bool hiding (not)
open import Data.List as List hiding (and; or)
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

  type-pointer : String → Typing-State Type
  type-pointer p Γ = pointer-types Γ ⟦ p ⟧ Maybe.>>= λ ρ → just (ρ , Γ)

  check-allocated : String → Typing-State ⊤
  check-allocated p = type-pointer p >> return tt

  set-type-pointer : String → Type → Typing-State ⊤
  set-type-pointer p ρ Γ = just (tt , Γ′) where
    Γ′ = record Γ { pointer-types = pointer-types Γ ⟦ p ⇒ ρ ⟧ }

  type-var : String → Typing-State Type
  type-var x Γ = var-types Γ ⟦ x ⟧ Maybe.>>= λ ξ → just (ξ , Γ)

  check-declared : String → Typing-State ⊤
  check-declared x = type-var x >> return tt

  set-type-var : String → Type → Typing-State ⊤
  set-type-var x ξ Γ = just (tt , Γ′) where
    Γ′ = record Γ { var-types = var-types Γ ⟦ x ⇒ ξ ⟧ }

  -- utilities

  mal-typed : ∀{A} → Typing-State A
  mal-typed = λ _ → nothing

  well-typed : Typing-State ⊤
  well-typed = return tt

open Typing-State


--
-- Utilities
--


check-type-equality : Type → Type → Typing-State ⊤
check-type-equality α β with α Grammar.Properties.Type.≟ β
... | yes _ = well-typed
... | no  _ = mal-typed

check-type-equality′ : Typing-State Type → Typing-State Type → Typing-State ⊤
check-type-equality′ get-α get-β = do
  α ← get-α
  β ← get-β
  check-type-equality α β


-- ignores resulting state of stateful computation
substate : ∀{A} → Typing-State A → Typing-State A
substate s =
  (s <$> get) >>= λ
    { (just (a , Γ′)) → return a
    ; nothing         → mal-typed }


--
-- Term
--


type-term : Term → Typing-State Type
type-term (var x) = type-var x
type-term (nat x) = return natural
type-term nil = return list
type-term app = return list


--
-- Formula
--


check-formula : Formula → Typing-State ⊤
check-formula (check a) = well-typed
check-formula (equal a b) = check-type-equality′ (type-term a) (type-term b)
check-formula (unequal a b) = check-type-equality′ (type-term a) (type-term b)
check-formula (allocated (pointer p)) = check-allocated p
check-formula (points (pointer p) a) = check-type-equality′ (type-pointer p) (type-term a)
check-formula (not φ) = check-formula φ
check-formula (and φ ψ) = check-formula φ >> check-formula ψ
check-formula (or φ ψ) = check-formula φ >> check-formula ψ
check-formula (sep φ ψ) = check-formula φ >> check-formula ψ


--
-- Statement
--


check-statement : Statement → Typing-State ⊤
check-statement (sequence []) = well-typed
check-statement (sequence (s ∷ ss)) = check-statement s >> check-statement (sequence ss)
check-statement pass = well-typed
check-statement (assert φ) = check-formula φ
check-statement (branch c s₁ s₂) = substate (check-statement s₁ >> check-statement s₂)
check-statement (loop x s) = check-statement s
check-statement (declare x ξ) = set-type-var x ξ
check-statement (assign x a) = check-type-equality′ (type-var x) (type-term a)
check-statement (allocate (pointer p) ρ) = set-type-pointer p ρ
check-statement (write (pointer p) a) = check-type-equality′ (type-pointer p) (type-term a)
check-statement (read x (pointer p)) = check-type-equality′ (type-var x) (type-pointer p)
-- todo: check equality of function type and list
check-statement (function f xs φ ψ s) = todo where postulate todo : Typing-State ⊤
check-statement (apply x f as) = todo where postulate todo : Typing-State ⊤


--
-- Program
--


check-program : Program → Typing-State ⊤
check-program (program s) = check-statement s
