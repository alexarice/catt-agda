{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
open import Catt.Dimension
open import Data.Nat

tm-to-ty : Ctx n → Tm n → Ty n
tm-to-ty Γ (Var i) = Γ ‼ i
tm-to-ty Γ (Coh Δ A σ) = A [ σ ]ty

tm-to-ty-is-dim : tm-is-dim Γ t → ty-is-dim Γ (tm-to-ty Γ t)
tm-to-ty-is-dim x = ?

-- tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-src t = ty-src (tm-to-ty t)

-- tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-tgt t = ty-tgt (tm-to-ty t)
