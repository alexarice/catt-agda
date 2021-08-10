{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.SplitForm where

open import Data.Nat.Properties
open import Catt.Base

private
  variable
    n dim : ℕ

data SplitForm : ℕ → ℕ → Set where
  Base : Term n → Ty n dim → SplitForm n dim
  Comp : SplitForm n (suc dim) → SplitForm n (suc dim) → SplitForm n (suc dim)
  WhiskerL : ∀ dim′ → SplitForm n (suc dim′) →
                      SplitForm n (suc dim + suc dim′) →
                      SplitForm n (suc dim + suc dim′)
  WhiskerR : ∀ dim′ → SplitForm n (suc dim + suc dim′) →
                      SplitForm n (suc dim′) →
                      SplitForm n (suc dim + suc dim′)
