{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.TypeChecking.Monad where

open import Data.Sum.Categorical.Left as S using (Sumₗ)
open import Data.Sum.Base
open import Category.Monad
open import Data.String
open import Level using (0ℓ)

TCM : Set → Set
TCM = S.Sumₗ String 0ℓ

monad : RawMonad TCM
monad = S.monad String Level.zero

pattern tc-ok x = inj₂ x
pattern tc-fail x = inj₁ x

add-stack : {A : Set} → String → TCM A → TCM A
add-stack s (tc-fail x) = tc-fail (x ++ "\n" ++ s)
add-stack s (tc-ok y) = tc-ok y

open RawMonad monad public
