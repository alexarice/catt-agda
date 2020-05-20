{-# OPTIONS --without-K --safe --exact-split #-}

open import Category.Monad

module Catt.TypeChecking.Monad {F : Set → Set} (M : RawMonad F) where

open import Data.Sum.Base
open import Data.String
open import Function
open import Level using (0ℓ)

open import Data.Sum.Categorical.Left String 0ℓ as S using (Sumₗ)

TCM : Set → Set
TCM = F ∘′ S.Sumₗ


monad : RawMonad TCM
monad = S.monadT M

module _ {A : Set} where

  open RawMonad M

  tc-ok : A → TCM A
  tc-ok x = return (inj₂ x)
  tc-fail : String → TCM A
  tc-fail s = return (inj₁ s)

  add-stack : String → TCM A → TCM A
  add-stack s m = m >>= λ where
    (inj₁ s′) → tc-fail $ s ++ "\n" ++ s′
    (inj₂ x) → tc-ok x

open RawMonad monad public
