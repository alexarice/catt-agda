{-# OPTIONS --safe --without-K #-}

module Catt.Nat where

open import Data.Nat public

_+′_ : ℕ → ℕ → ℕ
zero +′ m = m
suc n +′ m = n +′ suc m
