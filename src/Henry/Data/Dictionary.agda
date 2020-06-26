module Henry.Data.Dictionary where

open import Data.Unit as Unit
open import Data.Empty as Empty
open import Data.Bool as Bool
open import Data.List as List
open import Data.Maybe as Maybe
open import Data.Product as Product
open import Data.Sum as Sum

open import Relation.Binary.Core using (Rel)

open import Algebra
open IsMagma ⦃ ... ⦄
open IsSemigroup ⦃ ... ⦄
open IsMonoid ⦃ ... ⦄

open import Henry.Class.Equalable
open import Henry.Class.Equalable.Instances

open import Level


private
  variable
    ℓ ℓ′ : Level
    K : Set ℓ
    V : Set ℓ′


--
-- Dictionary
--


data Dictionary (K : Set ℓ) (V : Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  from-list : ⦃ Equalable K ⦄ → List (K × V) → Dictionary K V


--
-- utilities
--

-- find the value of a key, if it exists
find : K → Dictionary K V → Maybe V
find k′ (from-list []) = nothing
find k′ (from-list ((k , v) ∷ kvs)) =
  if k′ == k
    then just v
    else find k′ (from-list kvs)

infix 5 _⟦_⟧
_⟦_⟧ : Dictionary K V → K → Maybe V
d ⟦ k ⟧ = find k d


-- raw append to dictionary items
_∷D_ : (K × V) → Dictionary K V → Dictionary K V
kv ∷D (from-list kvs) = from-list (kv ∷ kvs)


-- insert a value-key pair if it does not exist
-- otherwise update the existing key
insert : K → V → Dictionary K V → Dictionary K V
insert k′ v′ (from-list []) = from-list List.[ k′ , v′ ]
insert k′ v′ (from-list ((k , v) ∷ kvs)) =
  if k′ == k
    then from-list ((k′ , v′) ∷ kvs)
    else (k , v) ∷D (insert k′ v′ (from-list kvs))

infix 5 _⟦_⇒_⟧
_⟦_⇒_⟧ : Dictionary K V → K → V → Dictionary K V
d ⟦ k ⇒ v ⟧ = insert k v d


-- update the value of a key
update : K → V → Dictionary K V → Dictionary K V
update k′ v′ (from-list []) = from-list []
update k′ v′ (from-list ((k , v) ∷ kvs)) =
  if k′ == k
    then from-list ((k′ , v′) ∷ kvs)
    else ((k , v) ∷D (update k′ v′ (from-list kvs)))

infix 5 _⟦_⟧∷=_
_⟦_⟧∷=_ : Dictionary K V → K → V → Dictionary K V
d ⟦ k ⟧∷= v = update k v d

merge : Dictionary K V → Dictionary K V → Dictionary K V
merge (from-list []) d₂ = d₂
merge (from-list ((k , v) ∷ kvs)) d₂ = merge (from-list kvs) (insert k v d₂)

--
-- Instances
--

-- instance
--   Equalable-List-Product : ⦃ Equalable K ⦄ → ⦃ Equalable V ⦄ → Equalable (List (K × V))
--   _==_ ⦃ Equalable-List-Product ⦄ [] [] = true
--   _==_ ⦃ Equalable-List-Product ⦄ [] (_ ∷ _) = false
--   _==_ ⦃ Equalable-List-Product ⦄ (_ ∷ _) [] = false
--   _==_ ⦃ Equalable-List-Product ⦄ (x ∷ l) (x′ ∷ l′) = x == x′

instance
  Equalable-Dictionary : ⦃ Equalable V ⦄ → Equalable (Dictionary K V)
  _==_ ⦃ Equalable-Dictionary ⦄ (from-list ⦃ Equalable-K ⦄ l) (from-list l′) =
    (all (λ (k , v) → (just v) == ((from-list ⦃ Equalable-K ⦄ l′) ⟦ k ⟧)) l ) ∧
    (all (λ (k , v) → (just v) == ((from-list ⦃ Equalable-K ⦄ l ) ⟦ k ⟧)) l′)


-- _≈_ : Relation.Binary.Core.Rel A ℓ

-- Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
-- Rel A ℓ = REL A A ℓ

-- REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
-- REL A B ℓ = A → B → Set ℓ

Bool→Set : Bool → Set
Bool→Set true = ⊤
Bool→Set false = ⊥

_≈_ : ⦃ Equalable V ⦄ → Rel (Dictionary K V) zero
d₁ ≈ d₂ = Bool→Set (d₁ == d₂)

-- IsMagma-Dictionary : ⦃ Equalable V ⦄ → IsMagma {suc ℓ ⊔ ℓ′} {zero} _≈_ merge
-- IsMagma-Dictionary = record
--   { isEquivalence = record
--     { refl = {!!}
--     ; sym = {!!}
--     ; trans = {!!} }
--   ; ∙-cong = {!!} }

-- {a ℓ : Level} {A : Set a} (_≈_ : Relation.Binary.Core.Rel A ℓ)
-- (∙ : Op₂ A) →
-- Set (a ⊔ ℓ)

-- instance
--  IsMagma-Dictionary : IsMagma merge
--  isEquivalence ⦃ IsMagma-Dictionary ⦄ = ?
--  ∙-cong ⦃ IsMagma-Dictionary ⦄ = ?
