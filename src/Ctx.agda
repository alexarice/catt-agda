{-# OPTIONS --safe --without-K #-}

module Ctx where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Product

record Ctx : Set where
  inductive
  constructor ⟨_,_⟩
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

empty-ctx : Ctx
empty-ctx .size = 0
empty-ctx .arr ()

NECtx : Set
NECtx = Σ[ c ∈ Ctx ] c .size ≥ 1

singleton-ctx : Ctx
singleton-ctx .size = 1
singleton-ctx .arr x y = empty-ctx

singleton-ctx-ne : NECtx
singleton-ctx-ne = singleton-ctx , ≤-refl

attach-ctx : (c : NECtx) → Ctx → Ctx
attach-ctx (c , _) a .size = suc (c .size)
attach-ctx (⟨ .(suc _) , f ⟩ , (s≤s p)) a .arr zero y = empty-ctx
attach-ctx (⟨ .(suc _) , f ⟩ , (s≤s p)) a .arr (suc zero) zero = a
attach-ctx (⟨ .(suc _) , f ⟩ , (s≤s p)) a .arr (suc zero) (suc y) = f zero y
attach-ctx (⟨ .(suc _) , f ⟩ , (s≤s p)) a .arr (suc (suc x)) zero = empty-ctx
attach-ctx (⟨ .(suc _) , f ⟩ , (s≤s p)) a .arr (suc (suc x)) (suc y) = f (suc x) y

attach-ctx-ne : (c : NECtx) → Ctx → NECtx
attach-ctx-ne nec@(⟨ .(suc _) , _ ⟩ , s≤s p) a = (attach-ctx nec a) , s≤s z≤n
