{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
open import Catt.Dimension
open import Data.Nat

tm-to-ty : Tm Γ (suc d) → Ty Γ d
tm-to-ty {Γ = Γ} (Var i) = Γ ‼ i
tm-to-ty (Coh Δ A x σ) = A [ σ ]ty

tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
tm-src t = ty-src (tm-to-ty t)

tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
tm-tgt t = ty-tgt (tm-to-ty t)
