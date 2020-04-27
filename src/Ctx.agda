{-# OPTIONS --safe --without-K #-}

module Ctx where

open import Data.Nat
open import Data.Fin

record Ctx : Set where
  coinductive
  field
    size : ℕ
    arr : (x y : Fin size) → Ctx

open Ctx public

data PureTy (c : Ctx) : ℕ → Set

retrieve-size : {c : Ctx} → {n : ℕ} → (t : PureTy c n) → ℕ

data PureTy c where
  ⋆P : PureTy c 0
  _⟶P_ : ∀ {n} {t : PureTy c n} → (x y : Fin (retrieve-size t)) → PureTy c (suc n)

retrieve-ctx : {c : Ctx} → {n : ℕ} → (t : PureTy c n) → Ctx

retrieve-size t = size (retrieve-ctx t)

retrieve-ctx {c} ⋆P = c
retrieve-ctx (_⟶P_ {t = t} x y) = arr (retrieve-ctx t) x y
