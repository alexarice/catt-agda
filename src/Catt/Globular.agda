{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
open import Data.Nat
open import Data.Empty

tm-to-ty : (Γ : Ctx n) → (t : Tm n) → Ty n
tm-to-ty Γ (Var i) = Γ ‼ i
tm-to-ty Γ (Coh Δ A σ) = A [ σ ]ty

tm-height : Ctx n → Tm n → ℕ
tm-height Γ t = ty-dim (tm-to-ty Γ t)

-- get-right-base-tm : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → Tm n
-- get-right-base-tm {d = suc zero} A = ty-tgt A
-- get-right-base-tm {d = suc (suc d)} A = get-right-base-tm (ty-base A)

-- ty-base′ : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → Ty n (pred d)
-- ty-base′ (s ─⟨ A ⟩⟶ t) = A

-- tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-src t = ty-src (tm-to-ty t)

-- tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-tgt t = ty-tgt (tm-to-ty t)
