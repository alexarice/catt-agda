module Catt.Discs where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Globular

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size n = double n

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (sphere-size n)

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , lift-ty (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ lift-ty (lift-ty (sphere-type n)) ⟩⟶ 0V

sub-from-disc : (d : ℕ) → (A : Ty n) → .(ty-dim A ≡ d) → (t : Tm n) → Sub (disc-size d) n ⋆
sub-from-sphere : (d : ℕ) → (A : Ty n) → .(ty-dim A ≡ d) → Sub (sphere-size d) n ⋆

sub-from-disc d A p t = ⟨ sub-from-sphere d A p , t ⟩

sub-from-sphere zero ⋆ p = ⟨ ⋆ ⟩′
sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = ⟨ ⟨ (sub-from-sphere d A (cong pred p)) , s ⟩ , t ⟩

identity : (n : ℕ) → Sub (disc-size n) m ⋆ → Tm m
identity n σ = Coh (Disc n) (0V ─⟨ lift-ty (sphere-type n) ⟩⟶ 0V) σ

identity-term : (A : Ty n) → (t : Tm n) → Tm n
identity-term A t = identity (ty-dim A) (sub-from-disc (ty-dim A) A refl t)

disc-term : (n : ℕ) → Sub (disc-size n) m ⋆ → Tm m
disc-term n σ = Coh (Disc n) (lift-ty (sphere-type n)) σ

sub-from-disc-term : Sub (disc-size d) n A → Tm n
sub-from-disc-term σ = sub-proj₂ σ

sub-from-sphere-type : Sub (sphere-size d) n A → Ty n
sub-from-sphere-type {d = zero} {A = A} σ = A
sub-from-sphere-type {d = suc d} ⟨ ⟨ σ , s ⟩ , t ⟩ = s ─⟨ sub-from-sphere-type σ ⟩⟶ t

sub-from-disc-type : Sub (disc-size d) n A → Ty n
sub-from-disc-type σ = sub-from-sphere-type (sub-proj₁ σ)
