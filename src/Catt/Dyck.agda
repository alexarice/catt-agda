{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck where

open import Catt.Syntax
open import Data.Nat

data Dyck : ℕ → ℕ → Set where
  End : Dyck 0 0
  ⇑ : Dyck n d → Dyck (2 + n) (suc d)
  ⇓ : Dyck n (suc d) → Dyck n d

variable
  dy ey fy : Dyck n d

dyck-to-ctx : Dyck n d → Ctx (suc n)
dyck-type : Dyck n d → Ty (suc n)
dyck-term : Dyck n d → Tm (suc n)

dyck-to-ctx End = ∅ , ⋆
dyck-to-ctx (⇑ d) = dyck-to-ctx d , dyck-type d , (liftTerm (dyck-term d)) ─⟨ (liftType (dyck-type d)) ⟩⟶ 0V
dyck-to-ctx (⇓ d) = dyck-to-ctx d

ty-src : Ty (suc n) → Tm (suc n)
ty-src ⋆ = 0V
ty-src (s ─⟨ A ⟩⟶ t) = s

ty-tgt : Ty (suc n) → Tm (suc n)
ty-tgt ⋆ = 0V
ty-tgt (s ─⟨ A ⟩⟶ t) = t

ty-base : Ty n → Ty n
ty-base ⋆ = ⋆
ty-base (s ─⟨ A ⟩⟶ t) = A

dyck-type End = ⋆
dyck-type (⇑ d) = liftType ((liftTerm (dyck-term d)) ─⟨ (liftType (dyck-type d)) ⟩⟶ 0V)
dyck-type (⇓ d) = ty-base (dyck-type d)

dyck-term End = 0V
dyck-term (⇑ d) = 0V
dyck-term (⇓ d) = ty-tgt (dyck-type d)

data Peak : ∀ {n} {d} → Dyck n d → Set where
  ⇕pk : (d : Dyck n d) → Peak (⇓ (⇑ d))
  ⇑pk : {d : Dyck n d} → (p : Peak d) → Peak (⇑ d)
  ⇓pk : {d : Dyck n (suc d)} → (p : Peak d) → Peak (⇓ d)

susp-dyck : Dyck n d → Dyck (2 + n) (suc d)
susp-dyck End = ⇑ End
susp-dyck (⇑ d) = ⇑ (susp-dyck d)
susp-dyck (⇓ d) = ⇓ (susp-dyck d)

connect-dyck : Dyck n 0 → Dyck m d → Dyck (m + n) d
connect-dyck d End = d
connect-dyck d (⇑ e) = ⇑ (connect-dyck d e)
connect-dyck d (⇓ e) = ⇓ (connect-dyck d e)
