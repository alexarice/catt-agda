------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations applied pointwise to vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core

module Data.Vec.Algebra.Pointwise {l} {A : Set l} (_∙_ : Op₂ A) where

open import Data.Vec
open import Data.Nat
open import Algebra.Definitions

module _ {n : ℕ} where

  infixl 6 _∙v_
  _∙v_ : Op₂ (Vec A n)
  _∙v_ = zipWith _∙_

  ∙v-assoc : Associative ? ? → Associative ? _∙v_
  ∙v-assoc a xs ys zs = ?
