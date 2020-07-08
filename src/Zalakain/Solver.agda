open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropositionalEquality
open import Relation.Nullary
open import Algebra


module Zalakain.Solver
  {A : Set}
  (_∙_ : A → A → A) (ε : A) (isMonoid : IsMonoid _≡_ _∙_ ε)
  where

open import Data.Unit as Unit using (⊤; tt)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Nat as Nat using (ℕ)
open import Data.Vec as Vec using (Vec; lookup)
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as ListProperties
open import Data.Product as Product -- using (_×_; _,_; proj₁; proj₂)



--
-- Expression
--

infixr 5 _∙′_

data Expression (n : ℕ) : Set where
  ε′ : Expression n
  var′ : Fin n → Expression n
  _∙′_ : Expression n → Expression n → Expression n

infix 4 _≡′_

data Equation (n : ℕ) : Set where
  _≡′_ : Expression n → Expression n → Equation n

--
-- Normal Form
--


NormalForm : ℕ → Set
NormalForm n = List (Fin n)

_≟_ : ∀{n} → DecidableEquality (NormalForm n)
_≟_ = ListProperties.≡-dec Fin._≟_

normalize : ∀{n} → Expression n → NormalForm n
normalize ε′ = List.[]
normalize (var′ i) = i ∷ List.[]
normalize (e₁ ∙′ e₂) = normalize e₁ List.++ normalize e₂


--
-- Environment
--


Environment : ℕ → Set
Environment n = Vec A n


⟦_⟧ : ∀{n} → Expression n → Environment n → A
⟦ ε′ ⟧ ρ = ε
⟦ var′ i ⟧ ρ = lookup ρ i
⟦ e₁ ∙′ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ

⟦_⇓⟧ : ∀{n} → NormalForm n → Environment n → A
⟦ [] ⇓⟧ ρ = ε
⟦ (i ∷ e) ⇓⟧ ρ = (lookup ρ i) ∙ ⟦ e ⇓⟧ ρ


--
-- Solution
--


Solution : ∀{n} → Equation n → Set
Solution {n} (e₁ ≡′ e₂) with (normalize e₁) ≟ (normalize e₂)
... | no _ = ⊤
... | yes _ = ∀(ρ : Environment n) → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ


∙-identityˡ : ∀ a → ε ∙ a ≡ a
∙-identityˡ = proj₁ (IsMonoid.identity isMonoid)

∙-identityʳ : ∀ a → a ∙ ε ≡ a
∙-identityʳ = proj₂ (IsMonoid.identity isMonoid)

∙-assoc : ∀ a b c → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
∙-assoc a b c = IsMonoid.assoc isMonoid a b c


++-homo : ∀ {n} (e₁ e₂ : NormalForm n) (ρ : Environment n)
  → ⟦ e₁ ⇓⟧ ρ ∙ ⟦ e₂ ⇓⟧ ρ ≡ ⟦ e₁ ++ e₂ ⇓⟧ ρ
++-homo [] e₂ ρ = ∙-identityˡ (⟦ e₂ ⇓⟧ ρ)
++-homo (i ∷ e₁) e₂ ρ =
  begin
    ((lookup ρ i) ∙ ⟦ e₁ ⇓⟧ ρ) ∙ ⟦ e₂ ⇓⟧ ρ
  ≡⟨ ∙-assoc _ _ _ ⟩
    (lookup ρ i) ∙ (⟦ e₁ ⇓⟧ ρ ∙ ⟦ e₂ ⇓⟧ ρ)
  ≡⟨ cong (λ ● → lookup ρ i ∙ ●) (++-homo e₁ e₂ ρ) ⟩
    (lookup ρ i) ∙ ⟦ e₁ ++ e₂ ⇓⟧ ρ
  ∎
  where open ≡-Reasoning


correct : ∀ {n} (e : Expression n) (ρ : Environment n)
  → ⟦ e ⟧ ρ ≡ ⟦ normalize e ⇓⟧ ρ
correct ε′ ρ = refl
correct (var′ i) ρ rewrite ∙-identityʳ (⟦ var′ i ⟧ ρ) = refl
correct (e₁ ∙′ e₂) ρ =
  begin
    ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ
  ≡⟨ cong (λ ● → ● ∙ _) (correct e₁ ρ) ⟩
    ⟦ normalize e₁ ⇓⟧ ρ ∙ ⟦ e₂ ⟧ ρ
  ≡⟨ cong (λ ● → _ ∙ ●) (correct e₂ ρ) ⟩
    ⟦ normalize e₁ ⇓⟧ ρ ∙ ⟦ normalize e₂ ⇓⟧ ρ
  ≡⟨ ++-homo (normalize e₁) (normalize e₂) ρ ⟩
    ⟦ normalize e₁ ++ normalize e₂ ⇓⟧ ρ
  ∎
  where open ≡-Reasoning


solve : ∀ {n} (eq : Equation n) → Solution eq
solve (e₁ ≡′ e₂) with (normalize e₁) ≟ (normalize e₂)
... | no _ = tt
... | yes eq = λ ρ →
  begin
    ⟦ e₁ ⟧ ρ
  ≡⟨ correct e₁ ρ ⟩
    ⟦ normalize e₁ ⇓⟧ ρ
  ≡⟨ cong (λ e → ⟦ e ⇓⟧ ρ) eq ⟩
    ⟦ normalize e₂ ⇓⟧ ρ
  ≡⟨ sym (correct e₂ ρ) ⟩
    ⟦ e₂ ⟧ ρ
  ∎
  where open ≡-Reasoning


--
-- automated generation of equations
--


-- builder

{-# TERMINATING #-}
Builder : ∀ n → Fin (Nat.suc n) → Set
Builder n Fin.zero = Equation n
Builder n (Fin.suc i) = Expression n → Builder n (Fin.inject₁ i)

-- NOTE: this reverses the order of the variables, not sure how to fix that
--       other that just making a solve′ that reverses its given environment
{-# TERMINATING #-}
build : ∀ n → Builder n (Fin.fromℕ n) → Equation n
build Nat.zero = id
build n@(Nat.suc n′) = helper (Fin.fromℕ n)
  where
    _Fin∸_ : ∀{n} → Fin n → Fin n → Fin n
    i Fin∸ Fin.zero = i
    Fin.zero Fin∸ Fin.suc j = Fin.zero
    Fin.suc i Fin∸ Fin.suc j = Fin.inject₁ i Fin∸ Fin.inject₁ j

    helper : ∀ i → Builder n i → Equation n
    helper Fin.zero = id
    helper (Fin.suc i) f = helper (Fin.inject₁ i) (f (var′ (Fin.fromℕ n′ Fin∸ i)))
    -- the following reverses the order of variables
    -- helper (Fin.suc i) f = helper (Fin.inject₁ i) (f (var′ i))


