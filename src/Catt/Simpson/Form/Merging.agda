{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.Form.Merging where

open import Catt.Simpson.Form
open import Data.Nat

private
  variable
    n dim dim′ : ℕ

merge : (dim′ ≤′ dim) → Form n (suc dim) dim′ → TopForm n dim → TopForm n dim
merge p (Base x x₁) tf = tf
merge p (Com x f x₁) tf = {!!}

mergeForms : (dim′ ≤ dim) → Form n (suc dim) dim′ → Form n dim dim′ → Form n dim dim′
mergeForms = {!!}
