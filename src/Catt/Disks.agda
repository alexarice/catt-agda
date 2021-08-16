{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Disks where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Data.Nat

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size zero = 0
sphere-size (suc n) = suc (disc-size n)

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (Sphere n) (suc n)

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V
