module Henry.LangB.Grammar.Base where


--
-- Imports
--


import Level

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary
open import Data.List as List hiding (and; or)
open import Data.String as String hiding (_++_)
open import Data.Product
open import Data.Nat
open import Data.Bool using (Bool)


--
-- Type
--


data Type : Set where
  natural  : Type
  list     : Type
  function : List Type → Type → Type

syntax function ps t = ps `→ t
  

--
-- Term
--


Var : Set
Var = String

LVar : Set
LVar = String

LVars : Set
LVars = List LVar


data Term : Set where
  var : Var → Term
  lvar : LVar → Term
  nat : ℕ → Term
  nil : Term
  app : Term → Term → Term

syntax var x = ` x
pattern `[] = nil
syntax app h t = h `∷ t


free-lvars-term : Term → LVars
free-lvars-term (var x) = []
free-lvars-term (lvar x) = [ x ]
free-lvars-term (nat x) = []
free-lvars-term `[] = []
free-lvars-term (app h t) = free-lvars-term h ++ free-lvars-term t 


--
-- Pointer
--


data Pointer : Set where
  pointer : String → Pointer

syntax pointer p = `* p


--
-- Formula
--

-- â is a subset of b̂
-- postulate sub-lvars : Rel LVars Level.zero

sub-lvars : Rel LVars Level.zero
sub-lvars â b̂ = all (λ a → any (λ b → does (a String.≟ b)) b̂) â ≡ Bool.true

-- sub-lvars : LVars → LVars → Bool
-- sub-lvars â b̂ = all (λ a → any (λ b → does (a String.≟ b)) b̂) â

syntax sub-lvars â b̂ = â ⊂ b̂

data Pure : Set where
  equal   : Term → Term → Pure
  unequal : Term → Term → Pure
  trueₚ   : Pure
  falseₚ  : Pure
  and     : Pure → Pure → Pure

data Spacial-Predicate-Binary : Set where
  points          : Spacial-Predicate-Binary
  is-list-segment : Spacial-Predicate-Binary

data Spacial : Set where
  pred₂  : Spacial-Predicate-Binary → Term → Term → Spacial
  trueₛ  : Spacial
  falseₛ : Spacial
  empty  : Spacial
  sep    : Spacial → Spacial → Spacial

-- lvars that are free in Σ
free-lvars : Spacial → LVars
free-lvars (pred₂ B t₁ t₂) = free-lvars-term t₁ ++ free-lvars-term t₂
free-lvars trueₛ = []
free-lvars falseₛ = []
free-lvars empty = []
free-lvars (sep Σ₁ Σ₂) = free-lvars Σ₁ ++ free-lvars Σ₂

Concrete : Set
Concrete = Pure × Spacial

data Symbolic : Set where
  consistent    : LVars → Concrete → Symbolic
  contradiction : Symbolic

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

syntax equal t₁ t₂   = t₁ =ₚ t₂
syntax unequal t₁ t₂ = t₁ ≠ₚ t₂
syntax and p₁ p₂     = p₁ ₚ∧ₚ p₂
syntax sep s₁ s₂     = s₁ ₛ⋆ₛ s₂

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

true : Concrete
true = trueₚ ₚ∧ₛ trueₛ

-- pattern ∃ₗ[_]_ = consistent
-- pattern ∃ₗ[]_ = consistent []

∃ₗ[_]_ : LVars → Concrete → Symbolic
∃ₗ[_]_ = consistent

∃ₗ[]_ : Concrete → Symbolic
∃ₗ[]_ = consistent []

_∧_ : Concrete → Concrete → Concrete
(p₁ , s₁) ∧ (p₂ , s₂) = (p₁ ₚ∧ₚ p₂ , s₁ ₛ⋆ₛ s₂)

_⋆_ : Symbolic → Symbolic → Symbolic
consistent â₁ Δ₁ ⋆ consistent â₂ Δ₂ = consistent (â₁ ++ â₂) (Δ₁ ∧ Δ₂)
contradiction ⋆ _ = contradiction
{-# CATCHALL #-}
_ ⋆ contradiction = contradiction


--
-- Statement
--

{- TODO:

remove Sequence statement, for the sake of inferring Hoare triples?
Then need to have explicit way, outside of individual Statements,
to consider sequenced Statement for the sake of inferring what transfers
between Hoare triples.

e.g. the program "x ≔ 1 ; x ≔ 2"
should ignore the inference in the postcondition of "x ≔ 1" when going on to "x ≔ 2"

-}



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
syntax loop a φᵢ s    = `while a `invariant φᵢ `do s
syntax declare x α a  = `declare x `: α `≔ a
syntax assign x a     = x `≔ a
syntax allocate p α a = `allocate p `: α `↦ a
syntax write p a      = p `↦ a
syntax read x p       = x `← p

--
-- Program
--


data Program : Set where
  program : Statement → Program


--
-- Infix
--


-- term/type/pointer constructor
infix  13 var function pointer 
-- term conjunction
infixr 12 app
-- pure/spacial predicate
infix  11 equal unequal _↦ₛ_
-- pure conjunction
infixl 10 and _ₚ∧_ _∧ₚ_ _ₚ∧ₛ_ _ₛ∧ₚ_
-- spacial conjunction
infixl 9  sep _ₛ⋆_ _⋆ₛ_ _ₚ⋆ₛ_ _ₛ⋆ₚ_
-- concrete conjunction
infixl 8  _∧_
-- symbolic conjunction
infixl 7  _⋆_
-- symbolic constructors
infix  6  ∃ₗ[_]_ ∃ₗ[]_ 
