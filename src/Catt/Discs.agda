{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Suspension
open import Data.Nat
open import Catt.Tree

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size zero = 0
sphere-size (suc n) = suc (disc-size n)

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (sphere-size n) n

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V

sub-from-disc : (Γ : Ctx n) → (t : Tm n) → Sub (disc-size (get-tm-height Γ t)) n
sub-from-sphere : Ty n d → Sub (sphere-size d) n

sub-from-disc Γ t = ⟨ (sub-from-sphere (tm-to-ty Γ t)) , t ⟩

sub-from-sphere ⋆ = ⟨⟩
sub-from-sphere (s ─⟨ A ⟩⟶ t) = ⟨ ⟨ sub-from-sphere A , s ⟩ , t ⟩
