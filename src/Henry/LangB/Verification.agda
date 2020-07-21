module Henry.LangB.Verification where


--
-- Imports
--

open import Function

open import Data.Unit as Unit
open import Data.Empty as Empty
open import Data.List as List hiding ([_])
open import Data.Bool as Bool
open import Data.String as String
open import Data.Sum as Sum
open import Data.Product as Product

import Category.Functor as Functor
import Category.Monad as Monad
import Category.Monad.State as State

open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Categorical renaming (monad to maybeMonad)

open import Henry.Data.Dictionary as Dictionary hiding (empty)

open import Henry.LangB.Grammar as Grammar
open import Henry.LangB.Hoare as Haore


--
-- Verification Context
--


module Verification-Context where
  open Monad
  open State

  Function-Interface = List (Var × Type) × Symbolic × Symbolic

  record Verification-Context : Set where
    constructor verification-context
    field
      function-interfaces : Dictionary String Function-Interface

  open Verification-Context

  S : Set
  S = Verification-Context

  M : Set → Set
  M = StateT S Maybe

  open Monad.RawMonad (StateTMonad S maybeMonad)
    using (return; _>>=_; _=<<_; _>>_; _<$>_) public
  open RawMonadState (StateTMonadState S maybeMonad)
    using (monad; get; put) public

  get-function-interface : String → M Function-Interface
  get-function-interface x s = function-interfaces s ⟦ x ⟧ Maybe.>>= flip return s

  set-function-interface : String → Function-Interface → M ⊤
  set-function-interface x i = do
    s ← get
    put record s { function-interfaces = function-interfaces s ⟦ x ⇒ i ⟧ }
    return tt

open Verification-Context


--
-- Verification
--

{-


postulate
  _implies_ : Symbolic → Symbolic → Verification-Context.M Bool


weakest-precondition : Statement → Verification-Context.M Symbolic
-- account for mutation of stack
weakest-precondition (sequence (s ∷ ss)) =
  TODO where postulate TODO : Verification-Context.M Symbolic
weakest-precondition (assert φ) = return φ
weakest-precondition (`if a `then s₁ `else s₂) = do
  φ₁ ← weakest-precondition s₁
  φ₂ ← weakest-precondition s₂
  return 
  return $ ([ a `?] `⇒ φ₁) `∨ (`¬ [ a `?] `⇒ φ₂)
weakest-precondition (`while a `invariant φᵢ `do s) = do
  φ ← weakest-precondition s
  return $ φᵢ `∧ ([ a `?] `⇒ φ)
weakest-precondition (p `↦ a) = return $ [ p `↦●]
weakest-precondition (x `← p) = return $ [ p `↦●]
weakest-precondition (apply x f as) = do
  (ps , φ , ψ) ← get-function-interface f
  return $ foldl _|>_ φ (zipWith (curry substitute-var-in-formula) (List.map proj₁ ps) as)
{-# CATCHALL #-}
weakest-precondition _ = return true


strongest-postcondition : Statement → Verification-Context.M Symbolic
-- account for mutation of stack
strongest-postcondition (sequence ss) =
  TODO where postulate TODO : Verification-Context.M Symbolic
strongest-postcondition (assert φ) = return φ
strongest-postcondition (`if a `then s₁ `else s₂) = do
  ψ₁ ← strongest-postcondition s₁
  ψ₂ ← strongest-postcondition s₂
  return $ [ a `?] `∧ ψ₁ `∨ (`¬ [ a `?]) `∧ ψ₂
strongest-postcondition (`while a `invariant φᵢ `do s) = do
  ψ ← strongest-postcondition s
  return $ (`¬ [ a `?]) `∧ φᵢ
strongest-postcondition (`declare x `: α `≔ a) = return [ ` x `= a ]
strongest-postcondition (x `≔ a) = return [ ` x `= a ]
strongest-postcondition (`allocate p `: α `↦ a) = return [ p `↦ a ]
strongest-postcondition (p `↦ a) = return [ p `↦ a ]
strongest-postcondition (x `← p) = return true -- TODO: how to access value stored by pointer?
-- a special variable ` "result" is a synonym for the variable ` x,
-- which recieves the return value of the function
strongest-postcondition (apply x f as) = do
  (ps , φ , ψ) ← get-function-interface f
  return $ foldl _|>_ ψ (zipWith (curry substitute-var-in-formula)
    ("result" ∷ List.map proj₁ ps)
    (` x ∷ as))
{-# CATCHALL #-}
strongest-postcondition _ = return true


_is-valid : Hoare-Triple → Verification-Context.M Bool
(hoare-triple φ s ψ) is-valid = do
  φ′ ← weakest-precondition s
  b₁ ← φ implies φ′
  b₂ ← φ implies ψ
  return b₁

-}
