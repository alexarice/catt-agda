{-# OPTIONS --safe --without-K #-}

module Types where

open import Ctx
open import Data.Nat
open import Data.Fin
open import Data.Product

private
  variable
    c : Ctx
    n : ℕ

data PD (c : Ctx) : Set

data Ty (c : Ctx) : ℕ → Set

data Term (c : Ctx) : {n : ℕ} → Ty c n → Set

data Ty c where
  ⋆ : Ty c 0
  _⟶_ : ∀ {n} {t : Ty c n} → (x y : Term c t) → Ty c (suc n)

purety-to-ty : PureTy c n → Ty c n

pd-n : PD c → ℕ

get-nth-tgt-ty : (f : Fin (suc n)) →
                 {ty : Ty c n} →
                 Term c ty →
                 Ty c (n ℕ-ℕ f)
get-nth-tgt-ty zero {ty} tm = ty
get-nth-tgt-ty (suc f) {x ⟶ y} tm = get-nth-tgt-ty f y

get-nth-tgt-tm : (f : Fin (suc n)) →
                 {ty : Ty c n}
                 (tm : Term c ty) →
                 Term c (get-nth-tgt-ty f tm)
get-nth-tgt-tm zero tm = tm
get-nth-tgt-tm (suc f) {x ⟶ y} tm = get-nth-tgt-tm f y

get-nth-tgt-pd-ty : (pd : PD c) →
                    (f : Fin (suc (pd-n pd))) →
                    Ty c ((pd-n pd) ℕ-ℕ f)
get-nth-tgt-pd-tm : (pd : PD c) →
                    (f : Fin (suc (pd-n pd))) →
                    Term c (get-nth-tgt-pd-ty pd f)

data PD c where
  Base : Term c ⋆ → PD c
  Attach : (pd : PD c) →
           (f : Fin (suc (pd-n pd))) →
           (tgt : Term c (get-nth-tgt-pd-ty pd f)) →
           (fill : Term c (get-nth-tgt-pd-tm pd f ⟶ tgt)) →
           PD c

pd-n (Base x) = 0
pd-n (Attach pd f tgt fill) = suc ((pd-n pd) ℕ-ℕ f)

get-nth-tgt-pd-ty (Base x) zero = ⋆
get-nth-tgt-pd-ty (Attach pd f tgt fill) i = get-nth-tgt-ty i fill

get-nth-tgt-pd-tm (Base x) zero = x
get-nth-tgt-pd-tm (Attach pd f tgt fill) i = get-nth-tgt-tm i fill

data Term c where
  Var : ∀ {n} → (ty : PureTy c n) → Fin (retrieve-size ty) → Term c (purety-to-ty ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y
