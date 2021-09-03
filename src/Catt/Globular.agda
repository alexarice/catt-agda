{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
-- open import Catt.Dimension
open import Data.Nat
open import Catt.Variables
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)

tm-to-ty : Tm Γ (suc d) → Ty Γ d
tm-to-ty {Γ = Γ} (Var i) = Γ ‼ i
tm-to-ty (Coh Δ A x σ) = A [ σ ]ty

tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
tm-src t = ty-src (tm-to-ty t)

tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
tm-tgt t = ty-tgt (tm-to-ty t)

ty-globular-src : (A : Ty Γ (suc (suc d))) → (ty-is-globular A) → isVar (ty-src A)
ty-globular-tgt : (A : Ty Γ (suc (suc d))) → (ty-is-globular A) → isVar (ty-tgt A)
ty-globular-base : (A : Ty Γ (suc (suc d))) → (ty-is-globular A) → ty-is-globular (ty-base A)

ty-globular-src (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vs

ty-globular-tgt (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vt

ty-globular-base (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = gA
