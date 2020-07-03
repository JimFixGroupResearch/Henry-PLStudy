module Henry.Data.Dictionary where

open import Level
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Data.Product as Product
open import Data.Sum as Sum
open import Data.List as List
open import Data.Maybe as Maybe
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)


private
  variable
    ℓₖ ℓᵥ : Level
    K : Set ℓₖ
    V : Set ℓᵥ


--
-- Dictionary
--


record Dictionary (K : Set ℓₖ) (V : Set ℓᵥ) : Set (ℓₖ ⊔ ℓᵥ) where
  constructor dictionary
  infix 4 _==_
  field
    _==_ : K → K → Bool
    items : List (K × V)
  
open Dictionary


empty : (K → K → Bool) → Dictionary K V
empty _==_ = dictionary _==_ [] 


infix 4 _==⟨_⟩_
_==⟨_⟩_ : K → Dictionary K V → K → Bool
k ==⟨ d ⟩ k′ = _==_ d k k′


--
-- utilities
--

-- get key's value, if key is in dictionary
find : K → Dictionary K V → Maybe V
find k′ (dictionary _==_ []) = nothing
find k′ (dictionary _==_ ((k , v) ∷ items)) =
  if k′ == k
    then just v
    else find k′ (dictionary _==_ items) 

infix 5 _⟦_⟧
_⟦_⟧ : Dictionary K V → K → Maybe V
d ⟦ k ⟧ = find k d



private
  -- raw append to dictionary items
  infix 5 _∷D_
  _∷D_ : (K × V) → Dictionary K V → Dictionary K V
  kv ∷D dictionary _==_ items = dictionary _==_ (kv ∷ items)
  

-- insert a value-key pair if it does not exist
-- otherwise update the existing key
insert : K → V → Dictionary K V → Dictionary K V
insert k′ v′ (dictionary _==_ []) = dictionary _==_ List.[ (k′ , v′) ]
insert k′ v′ (dictionary _==_ ((k , v) ∷ items)) =
  if k′ == k
    then dictionary _==_ ((k′ , v′) ∷ items)
    else (k , v) ∷D insert k′ v′ (dictionary _==_ items) 

infix 5 _⟦_⇒_⟧
_⟦_⇒_⟧ : Dictionary K V → K → V → Dictionary K V
d ⟦ k ⇒ v ⟧ = insert k v d


-- update the value of a key
update : K → V → Dictionary K V → Dictionary K V
update k′ v′ (dictionary _==_ []) = dictionary _==_ []
update k′ v′ (dictionary _==_ ((k , v) ∷ items)) =
  if k′ == k
    then dictionary _==_ ((k′ , v′) ∷ items)
    else (k , v) ∷D update k′ v′ (dictionary _==_ items)


infix 5 _⟦_⟧∷=_
_⟦_⟧∷=_ : Dictionary K V → K → V → Dictionary K V
d ⟦ k ⟧∷= v = update k v d


merge : Dictionary K V → Dictionary K V → Dictionary K V
merge d (dictionary _==_ []) = d
merge d (dictionary _==_ ((k , v) ∷ items)) = merge (insert k v d) (dictionary _==_ items)
