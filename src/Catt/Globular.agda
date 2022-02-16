module Catt.Globular where

open import Catt.Prelude
open import Catt.Syntax

ty-dim : Ty n → ℕ
ty-dim ⋆ = 0
ty-dim (s ─⟨ A ⟩⟶ t) = suc (ty-dim A)

ctx-dim : Ctx n → ℕ
ctx-dim ∅ = 0
ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A

lookupHeight : (Γ : Ctx n) → (i : Fin n) → ℕ
lookupHeight (Γ , A) zero = ty-dim A
lookupHeight (Γ , A) (suc i) = lookupHeight Γ i

tm-to-ty : (Γ : Ctx n) → (t : Tm n) → Ty n
tm-to-ty Γ (Var i) = Γ ‼ i
tm-to-ty Γ (Coh Δ A σ) = A [ σ ]ty

tm-height : Ctx n → Tm n → ℕ
tm-height Γ t = ty-dim (tm-to-ty Γ t)

ty-src : (A : Ty n) → .⦃ NonZero (ty-dim A) ⦄ → Tm n
ty-src (s ─⟨ A ⟩⟶ t) = s

ty-tgt : (A : Ty n) → .⦃ NonZero (ty-dim A) ⦄ → Tm n
ty-tgt (s ─⟨ A ⟩⟶ t) = t

ty-base : Ty n → Ty n
ty-base ⋆ = ⋆
ty-base (s ─⟨ A ⟩⟶ t) = A

ty-src′ : Ty (suc n) → Tm (suc n)
ty-src′ ⋆ = 0V
ty-src′ (s ─⟨ A ⟩⟶ t) = s

ty-tgt′ : Ty (suc n) → Tm (suc n)
ty-tgt′ ⋆ = 0V
ty-tgt′ (s ─⟨ A ⟩⟶ t) = t

truncate′ : ℕ → Ty n → Ty n
truncate′ zero A = A
truncate′ (suc d) A = truncate′ d (ty-base A)

truncate : ℕ → Ty n → Ty n
truncate d A = truncate′ (ty-dim A ∸ d) A
