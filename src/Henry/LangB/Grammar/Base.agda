module Henry.LangB.Grammar.Base where


--
-- Imports
--


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
  and : Pure → Pure → Pure

data Spacial-Predicate : Set where
  points : Term → Term → Spacial-Predicate
  list-segment : Term → Term → Spacial-Predicate

data Spacial : Set where
  predicate : Spacial-Predicate → Spacial
  true : Spacial
  empty : Spacial
  seperately : Spacial → Spacial → Spacial

Concrete : Set
Concrete = Pure × Spacial

Symbolic : Set
Symbolic = List LVar × Concrete

data Judgement : Symbolic → Symbolic → Set where

-- syntax
{-
  Conventions:
  - ∙ₚ and ₚ∙ indicates Pure parameters
  - ∙ₛ and ₛ∙ indicates Spacial parameters
  - ∙         indicates Symbolic parameters
-}

infixr 6 and _ₚ∧_ _∧ₚ_ _∧_ _ₚ∧ₛ_ _ₛ∧ₚ_
infixr 5 seperately _ₛ⋆_ _⋆ₛ_ _⋆_ _ₚ⋆ₛ_ _ₛ⋆ₚ_
infix 4 Judgement
infix 7 equal unequal points predicate

syntax equal t₁ t₂ = t₁ =ₜ t₂
syntax unequal t₁ t₂ = t₁ ≠ₜ t₂
syntax and p₁ p₂ = p₁ ₚ∧ₚ p₂

syntax points t₁ t₂ = t₁ ↦ₛ t₂
-- syntax list-segment t₁ t₂ = lseg s to t

syntax predicate p = predₛ[ p ]
syntax seperately s₁ s₂ = s₁ ₛ⋆ₛ s₂
  
syntax Judgement H₀ H₁ = H₀ ⊢ H₁

_∧ₚ_  : Concrete → Pure     → Concrete ; (p₁ , s)   ∧ₚ p₂       = (p₁ ₚ∧ₚ p₂ , s)
_ₚ∧_  : Pure     → Concrete → Concrete ; p₁        ₚ∧ (p₂ , s)  = (p₁ ₚ∧ₚ p₂ , s)
_∧ₛ_  : Concrete → Spacial  → Concrete ; (p , s₁)   ∧ₛ s₂       = (p , s₁ ₛ⋆ₛ s₂)
_ₛ∧_  : Spacial  → Concrete → Concrete ; s₁        ₛ∧ (p , s₂)  = (p , s₁ ₛ⋆ₛ s₂)
_ₚ∧ₛ_ : Pure     → Spacial  → Concrete ; p         ₚ∧ₛ s        = (p , s)
_ₛ∧ₚ_ : Spacial  → Pure     → Concrete ; s         ₛ∧ₚ p        = (p , s)
_∧_   : Concrete → Concrete → Concrete ; (p₁ , s₁)  ∧ (p₂ , s₂) = (p₁ ₚ∧ₚ p₂ , s₁ ₛ⋆ₛ s₂)

_⋆ₛ_  : Concrete → Spacial  → Concrete ; (p , s₁) ⋆ₛ s₂             = (p , s₁ ₛ⋆ₛ s₂)
_ₛ⋆_  : Spacial  → Concrete → Concrete ; s₁             ₛ⋆ (p , s₂)   = (p , s₁ ₛ⋆ₛ s₂)
_ₚ⋆ₛ_ : Pure → Spacial → Concrete ; p ₚ⋆ₛ s = (p , s)
_ₛ⋆ₚ_ : Spacial → Pure → Concrete ; s ₛ⋆ₚ p = (p , s)
_⋆_   : Concrete → Concrete → Concrete ; (p₁ , s₁) ⋆  (p₂ , s₂) = (p₁ ₚ∧ₚ p₂ , s₁ ₛ⋆ₛ s₂)
_∧⋆_ : Symbolic → Symbolic → Symbolic ; (l₁ , p₁ , s₁) ∧⋆ (l₂ , p₂ , s₂) = (l₁ ++ l₂ , p₁ ₚ∧ₚ p₂ , s₁ ₛ⋆ₛ s₂)


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

