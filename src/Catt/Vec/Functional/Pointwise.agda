{-# OPTIONS --safe --without-K #-}

module Catt.Vec.Functional.Pointwise where

open import Relation.Binary
open import Level
open import Catt.Vec.Functional
open import Catt.Fin
open import Data.Nat

private
  variable
    n : ℕ
    a b ℓ : Level
    A : ℕ → Set a
    B : ℕ → Set b

Pointwise : (∀ {m} → REL (A m) (B m) ℓ) → ∀ {n} → VectorD A n → VectorD B n → Set ℓ
Pointwise R xs ys = ∀ i → R (get xs i) (get ys i)
