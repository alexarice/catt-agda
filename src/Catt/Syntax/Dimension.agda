{-# OPTIONS --safe --without-K #-}

module Catt.Syntax.Dimension where

open import Catt.Syntax
open import Data.Nat

private
  variable
    n dim : ℕ

ty-dim : Ty n dim → ℕ
ty-dim {dim = dim} A = dim

ctx-dim : Ctx n → ℕ
ctx-dim ∅ = 0
ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A
