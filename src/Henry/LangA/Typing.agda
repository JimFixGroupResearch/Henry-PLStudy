open import Data.Nat as Nat

module Henry.LangA.Typing where

---
--- Imports
---

open import Function
open import Level as Level using (Level)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- Category
import Category.Functor as Functor
open import Category.Monad as Monad
open import Category.Monad.State as State
-- open import Category.Monad.Indexed as Indexed

-- Data
open import Agda.Builtin.Nat as BuiltinNat
open import Agda.Builtin.Bool as BuiltinBool
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Categorical renaming (monad to maybeMonad)

open import Data.Product as Product
open import Data.Sum as Sum
open import Data.String as String
open import Data.Unit as Unit
open import Data.Bool as Bool
open import Henry.Data.Dictionary as Dictionary hiding (empty)

-- LangA
open import Henry.LangA.Grammar as Grammar


--
-- Typing Context
--


record Typing-Context : Set where
  constructor make-Γ
  field
    fresh-id        : ℕ
    term-atom-types : Dictionary Term-Atom Type-Variable
    pointer-types   : Dictionary Pointer Type
--    constraits : Dictionary Type-Variable Type-Variable

open Typing-Context

empty : Typing-Context
empty = make-Γ 0
  (Dictionary.empty (λ x y → does (x Grammar.Properties.Term-Atom.≟ y)))
  (Dictionary.empty (λ x y → does (x Grammar.Properties.Pointer.≟ y)))


--
-- Typing State
--

-- TODO: use StateT in order to use Maybe as internal type, for 'mal-typed' result

module Typing-State where

  open Monad.RawMonad (StateTMonad Typing-Context maybeMonad)
    using (return; _>>=_; _=<<_; _>>_; _<$>_) public
  open RawMonadState (StateTMonadState Typing-Context maybeMonad)
    using (monad; get; put) public

  Typing-State : Set → Set
  Typing-State = StateT Typing-Context Maybe

  -- Utilities

  set-type-of-term-atom : Term-Atom → Type-Variable → Typing-State ⊤
  set-type-of-term-atom x ξ Γ = just (tt , Γ′) where
    Γ′ = record Γ { term-atom-types = term-atom-types Γ ⟦ x ⇒ ξ ⟧ }

  get-type-of-term-atom : Term-Atom → Typing-State Type-Variable
  get-type-of-term-atom x Γ = term-atom-types Γ ⟦ x ⟧ Maybe.>>= λ α → just (α , Γ)

  set-type-of-pointer : Pointer → Type → Typing-State ⊤
  set-type-of-pointer r ρ Γ = just (tt , Γ′) where
    Γ′ = record Γ { pointer-types = pointer-types Γ ⟦ r ⇒ ρ ⟧ }

  get-type-of-pointer : Pointer → Typing-State Type
  get-type-of-pointer r Γ = pointer-types Γ ⟦ r ⟧ Maybe.>>= λ α → just (α , Γ)

  fresh-type-variable : Typing-State Type-Variable
  fresh-type-variable Γ = just (free (fresh-id Γ) , Γ′) where
    Γ′ = record Γ { fresh-id = suc (fresh-id Γ) }

  mal-typed : ∀{A : Set} → Typing-State A
  mal-typed = λ _ → nothing

open Typing-State


--
--
--


-- conventions
--   a, b, c, ... are of Term
--   x, y, z, ... are of Term-Atom
--   α, β, γ, ... are of Type-Variables
--   A, B, C, ... are of Type


postulate unify : Type-Variable → Type-Variable → Typing-State Type-Variable


module Type-Primitive-Term where
  succ : Type-Variable
  succ = bound
    (application
      (application (atom arrow) (atom natural))
      (application
        (application (atom arrow) (atom natural))
        (atom natural)))

  nil : Type-Variable → Type-Variable
  nil α = application (bound (atom list)) α

  app : Type-Variable → Type-Variable
  app α =
    (application
      (application (bound (atom arrow)) α)
      (application
        (application (bound (atom arrow)) (application (bound (atom list)) α))
        (application (bound (atom list)) α)))
   

type-term-atom : Term-Atom → Typing-State Type-Variable
type-term-atom (name "unit")  = return (bound (atom unit))
type-term-atom (name "true")  = return (bound (atom boolean))
type-term-atom (name "false") = return (bound (atom (boolean)))
type-term-atom (name "zero")  = return (bound (atom natural))
type-term-atom (name "succ")  = return Type-Primitive-Term.succ
type-term-atom (name "nil")   = Type-Primitive-Term.nil <$> fresh-type-variable
type-term-atom (name "app")   = Type-Primitive-Term.app <$> fresh-type-variable
type-term-atom (name x)       = get-type-of-term-atom (name x)


-- postulate type-term : Term → Typing-State (Maybe Type)
type-term : Term → Typing-State Type-Variable
type-term (atom x) = type-term-atom x
type-term (function x ξ a) =
  set-type-of-term-atom x (bound ξ) >> type-term a <$>
    RawMonadState.get (StateTMonadState Typing-Context maybeMonad)
  >>= λ
    { nothing → mal-typed
    ; (just (α , _)) → return α }
type-term (application a b) = do
  α ← type-term a
  β ← type-term b
  γ ← fresh-type-variable
  unify α (application β γ)


type-pointer : Pointer → Typing-State Type
type-pointer (pointer n π) = return π


type-check-formula : Formula → Typing-State ⊤
type-check-formula (assert a) = do
  α ← type-term a
  if does (α Grammar.Properties.Type-Variable.≟ bound (atom boolean))
    then return tt
    else mal-typed
type-check-formula (equality a b) = do
  α ← type-term a
  β ← type-term b
  if does (α Grammar.Properties.Type-Variable.≟ β)
    then return tt
    else mal-typed
type-check-formula (pointing p ma) = do
  π ← bound <$> type-pointer p
  -- if pointing wildcard, always type-checks
  α ← Maybe.maybe′ type-term (return π) ma
  if does (π Grammar.Properties.Type-Variable.≟ α)
    then return tt
    else mal-typed
type-check-formula (and φ ψ) = type-check-formula φ >> type-check-formula ψ
type-check-formula (or φ ψ) = type-check-formula φ >> type-check-formula ψ
type-check-formula (sep φ ψ) = type-check-formula φ >> type-check-formula ψ


type-check-statement : Statement → Typing-State ⊤
type-check-statement pass = return tt
type-check-statement (declaration x A a) = set-type-of-term-atom x =<< type-term a
type-check-statement (assignment x a) = do
  ξ ← get-type-of-term-atom x -- needs to already have been declared
  α ← type-term a
  unify ξ α
  return tt
type-check-statement (allocation r R) = set-type-of-pointer r R
type-check-statement (write r a) = do
  ρ ← get-type-of-pointer r
  α ← type-term a
  unify (bound ρ) α
  return tt
type-check-statement (read  r x) = get-type-of-pointer r >>= set-type-of-term-atom x ∘ bound
type-check-statement (assert φ) = type-check-formula φ


type-check : Program → Typing-State ⊤
type-check (sequence []) = return tt
type-check (sequence (s ∷ ss)) = type-check-statement s >> type-check (sequence ss)


--
--
--


test-type-check : Maybe (⊤ × Typing-Context)
test-type-check = type-check test-program-1 empty
