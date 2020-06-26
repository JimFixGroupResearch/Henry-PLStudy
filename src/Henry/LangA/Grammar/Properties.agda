module Henry.LangA.Grammar.Properties where

--
-- Imports
--


open import Level
open import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions

open import Data.Empty
open import Data.String as String using (String)
open import Data.Bool as Bool using (Bool)
open import Data.Nat using (ℕ)

import Henry.LangA.Grammar.Base as Grammar


--
--
--


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


module Type-Atom where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Type-Atom} _≡_

module Type where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Type} _≡_


module Kind-Atom where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Kind-Atom} _≡_

module Kind where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Kind} _≡_


module Register where
  infix 4 _≟_
  postulate _≟_ : ∀{n : ℕ} → Decidable {A = Grammar.Register n} _≡_

module Formula where
  infix 4 _≟_
  postulate _≟_ : Decidable {A = Grammar.Formula} _≡_


module Statement where
  infix 4 _≟_
  postulate _≟_ : ∀{n : ℕ} → Decidable {A = Grammar.Statement n} _≡_
