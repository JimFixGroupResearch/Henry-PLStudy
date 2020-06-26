module Henry.Class.Equalable where

open import Data.Bool
open import Level

private
  variable
    ℓ : Level

record Equalable (A : Set ℓ) : Set (suc ℓ) where
  infix 5 _==_
  field
    _==_ : A → A → Bool

open Equalable {{...}} public


