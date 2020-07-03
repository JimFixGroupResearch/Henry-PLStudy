module Henry.LangA.Grammar.Properties where

--
-- Imports
--

open import Function
-- open import Function.Bijection
open import Level
open import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Negation as Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions

open import Data.Empty
open import Data.String as String using (String)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)

import Henry.LangA.Grammar.Base as Grammar


--
--
--


module Kind-Atom where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Kind-Atom} _≡_

module Kind where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Kind} _≡_


module Type-Atom where
  infix 4 _≟_
  _≟_ : Decidable {A = Grammar.Type-Atom} _≡_
  Grammar.unit ≟ Grammar.unit = true because ofʸ refl
  Grammar.unit ≟ Grammar.boolean = false because ofⁿ (λ ())
  Grammar.unit ≟ Grammar.natural = false because ofⁿ (λ ())
  Grammar.unit ≟ Grammar.list = false because ofⁿ (λ ())
  Grammar.unit ≟ Grammar.arrow = false because ofⁿ (λ ())
  Grammar.boolean ≟ Grammar.unit = false because ofⁿ (λ ())
  Grammar.boolean ≟ Grammar.boolean = true because ofʸ refl
  Grammar.boolean ≟ Grammar.natural = false because ofⁿ (λ ())
  Grammar.boolean ≟ Grammar.list = false because ofⁿ (λ ())
  Grammar.boolean ≟ Grammar.arrow = false because ofⁿ (λ ())
  Grammar.natural ≟ Grammar.unit = false because ofⁿ (λ ())
  Grammar.natural ≟ Grammar.boolean = false because ofⁿ (λ ())
  Grammar.natural ≟ Grammar.natural = true because ofʸ refl
  Grammar.natural ≟ Grammar.list = false because ofⁿ (λ ())
  Grammar.natural ≟ Grammar.arrow = false because ofⁿ (λ ())
  Grammar.list ≟ Grammar.unit = false because ofⁿ (λ ())
  Grammar.list ≟ Grammar.boolean = false because ofⁿ (λ ())
  Grammar.list ≟ Grammar.natural = false because ofⁿ (λ ())
  Grammar.list ≟ Grammar.list = true because ofʸ refl
  Grammar.list ≟ Grammar.arrow = false because ofⁿ (λ ())
  Grammar.arrow ≟ Grammar.unit = false because ofⁿ (λ ())
  Grammar.arrow ≟ Grammar.boolean = false because ofⁿ (λ ())
  Grammar.arrow ≟ Grammar.natural = false because ofⁿ (λ ())
  Grammar.arrow ≟ Grammar.list = false because ofⁿ (λ ())
  Grammar.arrow ≟ Grammar.arrow = true because ofʸ refl

module Type where
  ≡→atom≡ : ∀{x y} → x ≡ y → Grammar.Type.atom x ≡ Grammar.Type.atom y
  ≡→atom≡ refl = refl
  ≡atom→≡ : ∀{x y} → Grammar.Type.atom x ≡ Grammar.Type.atom y → x ≡ y
  ≡atom→≡ refl = refl

  

  infix 4 _≟_
  -- postulate _≟_ : Decidable {A = Grammar.Type} _≡_
  _≟_ : Decidable {A = Grammar.Type} {B = Grammar.Type} _≡_
  Grammar.atom a ≟ Grammar.atom b with a Type-Atom.≟ b
  ... | no ¬p = false because ofⁿ (contraposition ≡atom→≡ ¬p)
  ... | yes p = true because ofʸ (≡→atom≡ p)
  Grammar.atom a ≟ Grammar.function x k y = false because ofⁿ λ()
  Grammar.atom a ≟ Grammar.application x y = false because ofⁿ λ()
  Grammar.function x k y ≟ Grammar.atom a = false because ofⁿ λ()
  Grammar.function x k y ≟ Grammar.function z l w with x Type-Atom.≟ z
  ... | no ¬x≡z with k Kind.≟ l
  ...           | no ¬k≡l with y ≟ w
  ...                     | no ¬y≡w = {!!}
  ...                     | yes y≡w = {!!}
  ...           | yes k≡l with y ≟ w
  ...                     | no ¬y≡w = {!!}
  ...                     | yes y≡w = {!!}
  ... | yes x≡z = {!!} -- with k Kind.≟ l
  -- ...           | no ¬k≡l with y ≟ w
  -- ...                     | no ¬y≡w = ?
  -- ...                     | yes y≡w = ?
  -- ...           | yes k≡l with y ≟ w
  -- ...                     | no ¬y≡w = ?
  -- ...                     | yes y≡w = ?
  Grammar.function x k y ≟ Grammar.application z w = {!!}
  Grammar.application x y ≟ Grammar.atom z = {!!}
  Grammar.application x y ≟ Grammar.function z k w = {!!}
  Grammar.application x y ≟ Grammar.application z z₁ = {!!}

module Type-Variable where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Type-Variable} _≡_


module Term-Atom where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Term-Atom} _≡_
  -- name a ≟ name b = (does (a String.≟ b)) because (reason (a String.≟ b)) where
  --   reason : Dec (a ≡ b) → Reflects (name a ≡ name b) (does (a String.≟ b))
  --   reason (no ¬p) = {!!}
  --   reason (yes p) = {!!}

module Term where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Term} _≡_


module Pointer where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Pointer} _≡_

module Formula where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Formula} _≡_


module Statement where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Statement} _≡_
