{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Typing.Properties.Substitution (index : ℕ)
                              (rule : Fin index → Rule) where

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)

apply-sub-eq-ty : (A : Ty n) → σ ≈[ Γ ]s τ → A [ σ ]ty ≈[ Γ ]ty A [ τ ]ty
apply-sub-eq-tm : {σ : Sub n m A} → {τ : Sub n m B} → (t : Tm n) → σ ≈[ Γ ]s τ → t [ σ ]tm ≈[ Γ ]tm t [ τ ]tm
apply-sub-eq-sub : (μ : Sub n m ⋆) → σ ≈[ Γ ]s τ → σ ∘ μ ≈[ Γ ]s τ ∘ μ

apply-sub-eq-ty ⋆ eq = sub-eq-implies-ty-eq eq
apply-sub-eq-ty (s ─⟨ A ⟩⟶ t) eq = Arr≈ (apply-sub-eq-tm s eq) (apply-sub-eq-ty A eq) (apply-sub-eq-tm t eq)

apply-sub-eq-tm (Var zero) (Ext≈ eq x) = x
apply-sub-eq-tm (Var (suc i)) (Ext≈ eq x) = apply-sub-eq-tm (Var i) eq
apply-sub-eq-tm {A = ⋆} {B = ⋆} (Coh T C τ) eq = Coh≈ refl≈ty (apply-sub-eq-sub τ eq)
apply-sub-eq-tm {A = ⋆} {B = s ─⟨ B ⟩⟶ t} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = ⋆} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Coh T C τ) eq = apply-sub-eq-tm (Coh (suspTree T) (suspTy C) (suspSub τ)) (unrestrictEq eq)

apply-sub-eq-sub ⟨⟩ eq = Null≈ (sub-eq-implies-ty-eq eq)
apply-sub-eq-sub ⟨ μ , t ⟩ eq = Ext≈ (apply-sub-eq-sub μ eq) (apply-sub-eq-tm t eq)
