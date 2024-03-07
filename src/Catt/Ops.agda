module Catt.Ops where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Pasting
open import Catt.Support

Op : Set₁
Op = ∀ {n} (Γ : Ctx n) → VarSet n → VarSet n → Set
