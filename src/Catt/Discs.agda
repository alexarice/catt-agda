module Catt.Discs where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Globular

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size zero = 0
sphere-size (suc n) = suc (disc-size n)

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (sphere-size n)

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V

sub-from-disc : (d : ℕ) → (A : Ty n) → .(ty-dim A ≡ d) → (t : Tm n) → Sub (disc-size d) n ⋆
sub-from-sphere : (d : ℕ) → (A : Ty n) → .(ty-dim A ≡ d) → Sub (sphere-size d) n ⋆

sub-from-disc d A p t = ⟨ sub-from-sphere d A p , t ⟩

sub-from-sphere zero ⋆ p = ⟨⟩
sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = ⟨ ⟨ (sub-from-sphere d A (cong pred p)) , s ⟩ , t ⟩
