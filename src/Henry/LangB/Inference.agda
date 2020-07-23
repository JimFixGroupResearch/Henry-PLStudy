module Henry.LangB.Inference where


--
-- Imports
--

import Level

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropositionalEquality using (_≡_)

open import Data.List using (List; _++_)
open import Data.Unit
open import Data.Maybe
open import Data.Product

open import Henry.LangB.Grammar as Grammar


{- Judgement

A Judgement of the form H ⊢ L is the type of proofs that
L can be obtained by some sequence of applications of
the inference rules below.

-}

infix 5 Judgement _⊬_

syntax Judgement H L = H ⊢ L

data Judgement : Rel Symbolic Level.zero where

  -- pure

  intro-trueₚ : ∀ {Π Σ â}
    → (∃ₗ[ â ] (Π ₚ∧ₛ Σ)) ⊢ ∃ₗ[ â ] Π ₚ∧ₚ trueₚ ₚ∧ₛ Σ

  elim-trueₚ : ∀ {Π Σ â}
    → ∃ₗ[ â ] Π ₚ∧ₚ trueₚ ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ

  from-falseₚ : ∀ {Σ â}
    → ∃ₗ[ â ] falseₚ ₚ∧ₛ Σ ⊢ contradiction

  intro-equal : ∀ {T₁ T₂ Π Σ â}
    → T₁ ≡ T₂
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₚ T₁ =ₚ T₂ ₚ∧ₛ Σ

  intro-unequal : ∀ {T₁ T₂ Π Σ â}
    → ¬ T₁ ≡ T₂
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₚ T₁ ≠ₚ T₂ ₚ∧ₛ Σ

  elim-and₁ : ∀ {Π₁ Π₂ Σ â}
    → ∃ₗ[ â ] Π₁ ₚ∧ₚ Π₂ ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π₁ ₚ∧ₛ Σ

  elim-and₂ : ∀ {Π₁ Π₂ Σ â}
    → ∃ₗ[ â ] Π₁ ₚ∧ₚ Π₂ ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π₂ ₚ∧ₛ Σ

  -- spacial

  intro-trueₛ : ∀ {Π Σ â}
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â ] Π ₚ∧ₛ (Σ ₛ⋆ₛ trueₛ)

  elim-trueₛ : ∀ {Π Σ â}
    → ∃ₗ[ â ] Π ₚ∧ₛ (Σ ₛ⋆ₛ trueₛ) ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ

  from-falseₛ : ∀ {Π â}
    → ∃ₗ[ â ] Π ₚ∧ₛ falseₛ ⊢ contradiction

  elim-sep₁ : ∀ {Π Σ₁ Σ₂ â}
    → ∃ₗ[ â ] Π ₚ∧ₛ (Σ₁ ₛ⋆ₛ Σ₂) ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₁

  elim-sep₂ : ∀ {Π Σ₁ Σ₂ â}
    → ∃ₗ[ â ] Π ₚ∧ₛ (Σ₁ ₛ⋆ₛ Σ₂) ⊢ ∃ₗ[ â ] Π ₚ∧ₛ Σ₂

  -- concrete

  and-comm : ∀ {Δ₁ Δ₂ â}
    → ∃ₗ[ â ] Δ₁ ∧ Δ₂ ⊢ ∃ₗ[ â ] Δ₂ ∧ Δ₁

  -- symbolic

  sep-comm : ∀ {H L}
    → H ⋆ L ⊢ L ⋆ H

  elim-extra-lvars : ∀ {Π Σ â â′}
    → free-lvars Σ ⊂ â′ → â′ ⊂ â
    → ∃ₗ[ â ] Π ₚ∧ₛ Σ ⊢ ∃ₗ[ â′ ] Π ₚ∧ₛ Σ

  elim-false : ∀ {H}
    → contradiction ⊢ H


--
-- Properties
--


postulate trans : Transitive Judgement -- H ⊢ L → L ⊢ M → H ⊢ M
postulate refl : Reflexive Judgement -- H ⊢ H
min : Minimum Judgement contradiction -- contradiction entails anything
max : Maximum Judgement (∃ₗ[] true) -- true is entailed by anything


module ⊢-Reasoning where

  infix  3 _∎
  infixr 2 _⊢⟨⟩_ step-⊢
  infix  1 begin_

  begin_ : ∀ {H L} → H ⊢ L → H ⊢ L
  begin_ H⊢L = H⊢L

  _⊢⟨⟩_ : ∀ H {L} → H ⊢ L → H ⊢ L
  _ ⊢⟨⟩ H⊢L = H⊢L

  step-⊢ : ∀ H {L} {M} → H ⊢ L → L ⊢ M → H ⊢ M
  step-⊢ _ H⊢L L⊢M = trans H⊢L L⊢M

  _∎ : ∀ H → H ⊢ H
  H ∎ = refl

  syntax step-⊢ H H⊢L L⊢M = H ⊢⟨ H⊢L ⟩ L⊢M


min H = elim-false {H}

max (consistent â (Π , Σ)) =
  begin
    ∃ₗ[ â ] Π ₚ∧ₛ Σ
  ⊢⟨ intro-trueₚ ⟩
    ∃ₗ[ â ] (Π ₚ∧ₚ trueₚ) ₚ∧ₛ Σ
  ⊢⟨ elim-and₂ ⟩
    ∃ₗ[ â ] trueₚ ₚ∧ₛ Σ
  ⊢⟨ intro-trueₛ ⟩
    ∃ₗ[ â ] trueₚ ₚ∧ₛ (Σ ₛ⋆ₛ trueₛ)
  ⊢⟨ elim-sep₂ ⟩
    ∃ₗ[ â ] true
  ⊢⟨ elim-extra-lvars PropositionalEquality.refl PropositionalEquality.refl ⟩
    ∃ₗ[] true
  ∎
  where open ⊢-Reasoning
max contradiction = elim-false


_⊬_ : Symbolic → Symbolic → Set
H ⊬ L = ¬ H ⊢ L


{- Infer

Given H L, tries to infer the Judgement L ⊢ M.

-}

--
-- Infer (solving for entailment proof)
--


postulate
  infer : ∀ L M → Maybe (L ⊢ M)
