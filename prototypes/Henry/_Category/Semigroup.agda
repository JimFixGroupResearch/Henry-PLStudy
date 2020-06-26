module Henry.Category.Semigroup where


open import Level


private
  variable
    ℓ : Level


--
-- Semigroup
--


record Semigroup (M : Set ℓ) : Set (suc ℓ) where
  field
    _
