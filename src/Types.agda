{-# OPTIONS --safe --without-K #-}

module Types where

open import Data.Nat
open import Data.Fin
open import Data.Product using (∃; _,_)

record Ctx : Set where
  coinductive
  field
    size : ℕ
    arr : (x y : Fin size) → Ctx

open Ctx

data PureTy (c : Ctx) : ℕ → Set

retrieve-size : {c : Ctx} → {n : ℕ} → (t : PureTy c n) → ℕ

data PureTy c where
  ⋆P : PureTy c 0
  _⟶P_ : ∀ {n} {t : PureTy c n} → (x y : Fin (retrieve-size t)) → PureTy c (suc n)

retrieve-ctx : {c : Ctx} → {n : ℕ} → (t : PureTy c n) → Ctx

retrieve-size t = size (retrieve-ctx t)

retrieve-ctx {c} ⋆P = c
retrieve-ctx (_⟶P_ {t = t} x y) = arr (retrieve-ctx t) x y

-- data PD : ℕ → Set where
--   Base : PD 0
--   Attach : ∀ {n} → PD n → (f : Fin (suc n)) → PD (suc (n ℕ-ℕ f))

data PD (c : Ctx) : ℕ → Set

data Ty (c : Ctx) : ℕ → Set

data Term (c : Ctx) : {n : ℕ} → Ty c n → Set

data Ty c where
  ⋆ : Ty c 0
  _⟶_ : ∀ {n} {t : Ty c n} → (x y : Term c t) → Ty c (suc n)

get-ty-of-term : ∀ {c} {n} {ty : Ty c n} → Term c ty → Ty c n
get-ty-of-term {ty = ty} _ = ty

purety-to-ty : {c : Ctx} → {n : ℕ} → (PureTy c n) → (Ty c n)

get-nth-tgt-pd-ty : ∀ {n} {c} → (PD c n) → (f : Fin (suc n)) → Ty c (n ℕ-ℕ f)
get-nth-tgt-pd-tm : ∀ {n} {c} → (pd : PD c n) → (f : Fin (suc n)) → Term c (get-nth-tgt-pd-ty pd f)

data PD c where
  Base : Term c ⋆ → PD c 0
  Attach : ∀ {n} →
           (pd : PD c n) →
           (f : Fin (suc n)) →
           (tgt : Term c (get-nth-tgt-pd-ty pd f)) →
           (fill : Term c (get-nth-tgt-pd-tm pd f ⟶ tgt)) →
           PD c (suc (n ℕ-ℕ f))

get-nth-tgt-ty : ∀ {n} {c} →
                 (f : Fin (suc n)) →
                 {ty : Ty c n} →
                 Term c ty →
                 Ty c (n ℕ-ℕ f)
get-nth-tgt-ty zero {ty} tm = ty
get-nth-tgt-ty (suc f) {x ⟶ y} tm = get-nth-tgt-ty f y

get-nth-tgt-tm : ∀ {n} {c} →
                 (f : Fin (suc n)) →
                 {ty : Ty c n}
                 (tm : Term c ty) →
                 Term c (get-nth-tgt-ty f tm)
get-nth-tgt-tm zero tm = tm
get-nth-tgt-tm (suc f) {x ⟶ y} tm = get-nth-tgt-tm f y

get-nth-tgt-pd-ty (Base x) zero = ⋆
get-nth-tgt-pd-ty (Attach pd f tgt fill) i = get-nth-tgt-ty i fill

get-nth-tgt-pd-tm (Base x) zero = x
get-nth-tgt-pd-tm (Attach pd f tgt fill) i = get-nth-tgt-tm i fill

data Term c where
  Var : ∀ {n} → (ty : PureTy c n) → Fin (retrieve-size ty) → Term c (purety-to-ty ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y
