module Test where

open import Data.String

open import Category.Monad as Monad
open RawMonad
-- open import Category.Monad.Indexed
-- open RawIMonad
open import Category.Monad.State as State
-- open RawIMonadState
-- open RawMonadState

open import Data.Nat as Nat
open import Data.Maybe as Maybe

x : State ℕ ℕ
x = return (StateMonad ℕ) 1

f : String → String
f "hello" = "a"
f "world" = "b"
f _ = "c"
