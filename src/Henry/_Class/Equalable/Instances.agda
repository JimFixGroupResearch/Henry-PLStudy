module Henry.Class.Equalable.Instances where

open import Data.Bool as Bool
open import Data.Nat as Nat
open import Data.String as String hiding (_==_)
open import Data.List as List
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Maybe as Maybe

open import Level

open import Henry.Class.Equalable

private
  variable
    ℓ ℓ′ : Level
    A : Set ℓ
    B : Set ℓ′

instance
  Equalable-Bool : Equalable Bool
  _==_ {{Equalable-Bool}} = λ
    { true true   → true
    ; true false  → false
    ; false true  → false
    ; false false → true }

instance
  Equalable-ℕ : Equalable ℕ
  _==_ {{Equalable-ℕ}} = λ
    { zero    zero    → true
    ; zero    (suc _) → false
    ; (suc _) zero    → false
    ; (suc m) (suc n) → _==_ {{Equalable-ℕ}} m n }

instance
  Equalable-String : Equalable String
  _==_ {{Equalable-String}} s s′ = s String.== s′

instance
  Equalable-List : {{Equalable A}} → Equalable (List A)
  _==_ {{Equalable-List}} = λ
    { []      []        → true
    ; []      (_ ∷ _)   → false
    ; (_ ∷ _) []        → false
    ; (h ∷ t) (h′ ∷ t′) → (h == h′) ∧ (_==_ {{Equalable-List}} t t′) }

instance
  Equalable-Product : {{Equalable A}} → {{Equalable B}} → Equalable (A × B)
  _==_ {{Equalable-Product}} = λ (a , b) (a′ , b′) → (a == a′) ∧ (b == b′)

instance
  Equalable-Maybe : {{Equalable A}} → Equalable (Maybe A)
  _==_ {{Equalable-Maybe}} = λ
    { nothing  nothing   → true
    ; nothing  (just _)  → false
    ; (just _) nothing   → false
    ; (just a) (just a′) → a == a′ }
