{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
open import Catt.Dimension
open import Data.Nat

tm-to-ty : Ctx n → Tm n → Ty n
tm-to-ty Γ (Var i) = Γ ‼ i
tm-to-ty Γ (Coh Δ A σ) = A [ σ ]ty

tm-to-ty-dim : tm-dim Γ t (suc d) → ty-dim Γ (tm-to-ty Γ t) d
tm-to-ty-dim (VarD c i) = lookupDim-dim c i
tm-to-ty-dim (CohD x y z) = {!!}

-- tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-src t = ty-src (tm-to-ty t)

-- tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-tgt t = ty-tgt (tm-to-ty t)
