module Catt.Dyck where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular

data Dyck : ℕ → ℕ → Set

data Dyck where
  End : Dyck 0 0
  ⇑ : Dyck n d → Dyck (suc n) (suc d)
  ⇓ : (dy : Dyck n (suc d)) → Dyck n d

variable
  dy ey fy : Dyck n d

dyck-to-ctx : Dyck n d → Ctx (suc (n * 2))
dyck-pre-type : Dyck n d → Ty (n * 2)
dyck-type : Dyck n d → Ty (suc (n * 2))
dyck-term : Dyck n d → Tm (suc (n * 2))

dyck-to-ctx End = ∅ , ⋆
dyck-to-ctx (⇑ d) = dyck-to-ctx d , dyck-type d , dyck-pre-type (⇑ d)
dyck-to-ctx (⇓ d) = dyck-to-ctx d

dyck-pre-type End = ⋆
dyck-pre-type (⇑ d) = (lift-tm (dyck-term d)) ─⟨ (lift-ty (dyck-type d)) ⟩⟶ 0V
dyck-pre-type (⇓ d) = ty-base (dyck-pre-type d)

dyck-type dy = lift-ty (dyck-pre-type dy)

dyck-term End = 0V
dyck-term (⇑ d) = 0V
dyck-term (⇓ d) = ty-tgt′ (dyck-type d)

data Peak : ∀ {n} → Dyck (suc n) d → Set where
  ⇕pk : (dy : Dyck n d) → Peak (⇓ (⇑ dy))
  ⇑pk : (p : Peak dy) → Peak (⇑ dy)
  ⇓pk : (p : Peak dy) → Peak (⇓ dy)

peak-term : {dy : Dyck (suc n) d} → Peak dy → Tm (3 + (n * 2))
peak-term (⇕pk dy) = 0V
peak-term (⇑pk p) = lift-tm (lift-tm (peak-term p))
peak-term (⇓pk p) = peak-term p

susp-dyck : Dyck n d → Dyck (suc n) (suc d)
susp-dyck End = ⇑ End
susp-dyck (⇑ d) = ⇑ (susp-dyck d)
susp-dyck (⇓ d) = ⇓ (susp-dyck d)

susp-peak : {dy : Dyck (suc n) d} → Peak dy → Peak (susp-dyck dy)
susp-peak (⇕pk dy) = ⇕pk (susp-dyck dy)
susp-peak (⇑pk p) = ⇑pk (susp-peak p)
susp-peak (⇓pk p) = ⇓pk (susp-peak p)

connect-dyck : (dy : Dyck n 0) → Dyck m d → Dyck (m + n) d
connect-dyck d End = d
connect-dyck d (⇑ e) = ⇑ (connect-dyck d e)
connect-dyck d (⇓ e) = ⇓ (connect-dyck d e)
