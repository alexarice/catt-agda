{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dimension.Properties where

open import Data.Nat
open import Catt.Syntax
open import Catt.Dimension
open import Relation.Binary.PropositionalEquality

src-subbed : (A : Ty Γ (suc (suc d))) → (σ : Sub Γ Δ) → ty-src A [ σ ]tm ≡ ty-src (A [ σ ]ty)
src-subbed (s ─⟨ A ⟩⟶ t) σ = refl

tgt-subbed : (A : Ty Γ (suc (suc d))) → (σ : Sub Γ Δ) → ty-tgt A [ σ ]tm ≡ ty-tgt (A [ σ ]ty)
tgt-subbed (s ─⟨ A ⟩⟶ t) σ = refl

base-subbed : (A : Ty Γ (suc (suc d))) → (σ : Sub Γ Δ) → ty-base A [ σ ]ty ≡ ty-base (A [ σ ]ty)
base-subbed (s ─⟨ A ⟩⟶ t) σ = refl
