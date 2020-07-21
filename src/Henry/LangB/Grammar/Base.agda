module Henry.LangB.Grammar.Base where


--
-- Imports
--


open import Relation.Nullary

open import Data.List as List hiding (and; or)
open import Data.String hiding (_++_)
open import Data.Product
open import Data.Nat


--
-- Type
--


data Type : Set where
  natural  : Type
  list     : Type
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
  app : Term → Term → Term

infixr 5 app

syntax var x = ` x
-- syntax nat n = ...
pattern `[] = nil
syntax app h t = h `∷ t


--
-- Pointer
--


data Pointer : Set where
  pointer : String → Pointer

syntax pointer p = `* p


--
-- Formula
--


-- logic variable
LVar : Set
LVar = String

data Pure : Set where
  equal : Term → Term → Pure
  unequal : Term → Term → Pure
  true : Pure
  false : Pure
  and : Pure → Pure → Pure

data Spacial-Predicate-Binary : Set where
  points : Spacial-Predicate-Binary
  is-list-segment : Spacial-Predicate-Binary

data Spacial : Set where
  pred₂ : Spacial-Predicate-Binary → Term → Term → Spacial
  true : Spacial
  false : Spacial
  empty : Spacial
  seperately : Spacial → Spacial → Spacial

Concrete : Set
Concrete = Pure × Spacial

data Symbolic : Set where
  consistent : List LVar → Concrete → Symbolic
  contradiction : Symbolic

data Judgement : Symbolic → Symbolic → Set where

-- syntax
{-
  Conventions:
  - ∙ₚ and ₚ∙ indicates Pure parameters
  - ∙ₛ and ₛ∙ indicates Spacial parameters
  - ∙         indicates Concrete parameters

  Binding levels: (decreasing tighness)
  - Pure
  - Spacial
  - Concrete
  - Symbolic
-}

infix 10 equal unequal _↦ₛ_ -- pure / spacial predicate
infixl 9 and _ₚ∧_ _∧ₚ_ _ₚ∧ₛ_ _ₛ∧ₚ_ -- pure conjunctions
infixl 8 seperately _ₛ⋆_ _⋆ₛ_ _ₚ⋆ₛ_ _ₛ⋆ₚ_ -- spacial conjunctions
infixl 7 _∧_ -- concrete conjunctions
infixl 6 _⋆_ -- symbolic conjunctions
infix  5 ∃ₗ[_]_ ∃ₗ[]_ -- symbolic constructors
infix  4 Judgement -- judgement constructors

syntax equal t₁ t₂ = t₁ =ₜ t₂
syntax unequal t₁ t₂ = t₁ ≠ₜ t₂
syntax and p₁ p₂ = p₁ ₚ∧ₚ p₂
syntax seperately s₁ s₂ = s₁ ₛ⋆ₛ s₂

_↦ₛ_ : Term → Term → Spacial
_↦ₛ_ = pred₂ points

lseg : Term → Term → Spacial
lseg = pred₂ is-list-segment

_∧ₚ_  : Concrete → Pure     → Concrete ; (p₁ , s)   ∧ₚ  p₂       = (p₁ ₚ∧ₚ p₂ , s)
_ₚ∧_  : Pure     → Concrete → Concrete ; p₁        ₚ∧  (p₂ , s)  = (p₁ ₚ∧ₚ p₂ , s)
_∧ₛ_  : Concrete → Spacial  → Concrete ; (p , s₁)   ∧ₛ  s₂       = (p , s₁ ₛ⋆ₛ s₂)
_ₛ∧_  : Spacial  → Concrete → Concrete ; s₁        ₛ∧  (p , s₂)  = (p , s₁ ₛ⋆ₛ s₂)
_ₚ∧ₛ_ : Pure     → Spacial  → Concrete ; p         ₚ∧ₛ  s        = (p , s)
_ₛ∧ₚ_ : Spacial  → Pure     → Concrete ; s         ₛ∧ₚ  p        = (p , s)

_⋆ₛ_  : Concrete → Spacial  → Concrete ; (p , s₁)   ⋆ₛ  s₂       = (p , s₁ ₛ⋆ₛ s₂)
_ₛ⋆_  : Spacial  → Concrete → Concrete ; s₁        ₛ⋆  (p , s₂)  = (p , s₁ ₛ⋆ₛ s₂)
_ₚ⋆ₛ_ : Pure     → Spacial  → Concrete ; p         ₚ⋆ₛ  s        = (p , s)
_ₛ⋆ₚ_ : Spacial  → Pure     → Concrete ; s         ₛ⋆ₚ  p        = (p , s)

∃ₗ[_]_ : List LVar → Concrete → Symbolic
∃ₗ[ â ] Δ = consistent â Δ

∃ₗ[]_ : Concrete → Symbolic
∃ₗ[] Δ = consistent [] Δ

_∧_ : Concrete → Concrete → Concrete
(p₁ , s₁) ∧ (p₂ , s₂) = (p₁ ₚ∧ₚ p₂ , s₁ ₛ⋆ₛ s₂)

_⋆_ : Symbolic → Symbolic → Symbolic
consistent â₁ Δ₁ ⋆ consistent â₂ Δ₂ = consistent (â₁ ++ â₂) (Δ₁ ∧ Δ₂)
contradiction ⋆ _ = contradiction
_ ⋆ contradiction = contradiction
  
syntax Judgement H₀ H₁ = H₀ ⊢ H₁

_⊬_ : Symbolic → Symbolic → Set
H₀ ⊬ H₁ = ¬ (H₀ ⊢ H₁)


--
-- Statement
--


data Statement : Set where
  pass     : Statement
  sequence : List Statement → Statement
  assert   : Symbolic → Statement
  -- control structures
  branch   : Term → Statement → Statement → Statement
  loop     : Term → Symbolic → Statement → Statement
  -- variables
  declare  : Var → Type → Term → Statement
  assign   : Var → Term → Statement
  -- pointers
  allocate : Pointer → Type → Term → Statement
  write    : Pointer → Term → Statement
  read     : Var → Pointer → Statement
  -- functions
  function : Term → List (Var × Type) → Symbolic → Symbolic → Statement → Statement
  apply    : Var → Var → List Term → Statement

syntax branch a s₁ s₂ = `if a `then s₁ `else s₂
syntax loop a φᵢ s = `while a `invariant φᵢ `do s
syntax declare x α a = `declare x `: α `≔ a
syntax assign x a = x `≔ a
syntax allocate p α a = `allocate p `: α `↦ a
syntax write p a = p `↦ a
syntax read x p = x `← p

--
-- Program
--


data Program : Set where
  program : Statement → Program

