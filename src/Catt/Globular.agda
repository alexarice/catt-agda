{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
-- open import Catt.Dimension
open import Data.Nat
open import Catt.Variables
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)

get-tm-height : Tm Γ → ℕ
get-tm-height {Γ = Γ} (Var i) = lookupHeight Γ i
get-tm-height (Coh {d = d} Δ A σ) = d

tm-to-ty : (t : Tm Γ) → Ty Γ (get-tm-height t)
tm-to-ty {Γ = Γ} (Var i) = Γ ‼ i
tm-to-ty (Coh Δ A σ) = A [ σ ]ty

-- tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-src t = ty-src (tm-to-ty t)

-- tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-tgt t = ty-tgt (tm-to-ty t)
