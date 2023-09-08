module Catt.Haskell where

open import Catt.Prelude

data Test : @0 ℕ → Set where
  Zero : Test 0
  Succ : ∀ {@0 n : ℕ} → Test n → Test (suc n)

unwrap : ∀ {@0 n} → Test (suc n) → Test n
unwrap (Succ x) = x

{-# COMPILE AGDA2HS Test #-}
{-# COMPILE AGDA2HS unwrap #-}
