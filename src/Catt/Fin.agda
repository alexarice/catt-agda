{-# OPTIONS --without-K --safe #-}

module Catt.Fin where

open import Data.Nat
open import Data.Bool

private
  variable
    n : ℕ

data Fin : ℕ → Set where
  fromℕ : (n : ℕ) → Fin (suc n)
  inject : Fin n → Fin (suc n)

toℕ : Fin n → ℕ
toℕ (fromℕ n) = n
toℕ (inject f) = toℕ f

sameF : Fin n → Fin n → Bool
sameF (fromℕ n) (fromℕ .n) = true
sameF (fromℕ n) (inject g) = false
sameF (inject f) (fromℕ _) = false
sameF (inject f) (inject g) = sameF f g
