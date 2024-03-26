module Catt.Dyck where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular

data Dyck : ℕ → ℕ → Set

data Dyck where
  ⊝ : Dyck 0 0
  ⇑ : Dyck n d → Dyck (suc n) (suc d)
  ⇓ : (dy : Dyck n (suc d)) → Dyck n d

variable
  dy ey fy : Dyck n d

⌊_⌋d : Dyck n d → Ctx (suc (double n))
dyck-pre-type : Dyck n d → Ty (double n)
dyck-type : Dyck n d → Ty (suc (double n))
dyck-term : Dyck n d → Tm (suc (double n))

⌊ ⊝ ⌋d = ∅ , ⋆
⌊ ⇑ d ⌋d = ⌊ d ⌋d , dyck-type d , dyck-pre-type (⇑ d)
⌊ ⇓ d ⌋d = ⌊ d ⌋d

dyck-pre-type ⊝ = ⋆
dyck-pre-type (⇑ d) = (wk-tm (dyck-term d)) ─⟨ (wk-ty (dyck-type d)) ⟩⟶ 0V
dyck-pre-type (⇓ d) = ty-base (dyck-pre-type d)

dyck-type dy = wk-ty (dyck-pre-type dy)

dyck-term ⊝ = 0V
dyck-term (⇑ d) = 0V
dyck-term (⇓ d) = ty-tgt′ (dyck-type d)

data Peak : ∀ {n} → Dyck n d → Set where
  ⇕pk : (dy : Dyck n d) → Peak (⇓ (⇑ dy))
  ⇑pk : {dy : Dyck (suc n) d} → (p : Peak dy) → Peak (⇑ dy)
  ⇓pk : (p : Peak dy) → Peak (⇓ dy)

peak-height : {dy : Dyck n d} → Peak dy → ℕ
peak-height (⇕pk {d = d} dy) = d
peak-height (⇑pk pk) = peak-height pk
peak-height (⇓pk pk) = peak-height pk

peak-term : {dy : Dyck n d} → Peak dy → Tm (suc (double n))
peak-term (⇕pk dy) = 0V
peak-term (⇑pk p) = wk-tm (wk-tm (peak-term p))
peak-term (⇓pk p) = peak-term p

susp-dyck : Dyck n d → Dyck (suc n) (suc d)
susp-dyck ⊝ = ⇑ ⊝
susp-dyck (⇑ d) = ⇑ (susp-dyck d)
susp-dyck (⇓ d) = ⇓ (susp-dyck d)

susp-peak : {dy : Dyck n d} → Peak dy → Peak (susp-dyck dy)
susp-peak (⇕pk dy) = ⇕pk (susp-dyck dy)
susp-peak (⇑pk p) = ⇑pk (susp-peak p)
susp-peak (⇓pk p) = ⇓pk (susp-peak p)

wedge-dyck : (dy : Dyck n 0) → Dyck m d → Dyck (m + n) d
wedge-dyck d ⊝ = d
wedge-dyck d (⇑ e) = ⇑ (wedge-dyck d e)
wedge-dyck d (⇓ e) = ⇓ (wedge-dyck d e)

dyck-dim : (dy : Dyck n d) → ℕ
dyck-dim ⊝ = 0
dyck-dim (⇑ {d = d} dy) = dyck-dim dy ⊔ suc d
dyck-dim (⇓ dy) = dyck-dim dy

dyck-finish : Dyck n d → Dyck n 0
dyck-finish {d = zero} dy = dy
dyck-finish {d = suc d} dy = dyck-finish (⇓ dy)

dyck-disc : (n : ℕ) → Dyck n n
dyck-disc zero = ⊝
dyck-disc (suc n) = ⇑ (dyck-disc n)

dyck-disc-peak : (n : ℕ) → Peak (⇓ (dyck-disc (suc n)))
dyck-disc-peak n = ⇕pk (dyck-disc n)

dyck-finish-peak : {dy : Dyck n d} → Peak dy → Peak (dyck-finish dy)
dyck-finish-peak {d = zero} p = p
dyck-finish-peak {d = suc d} p = dyck-finish-peak (⇓pk p)
