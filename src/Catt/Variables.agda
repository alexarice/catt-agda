{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Variables where

open import Catt.Prelude
open import Catt.Syntax
open import Data.Sum
open import Catt.Syntax.SyntacticEquality

VarSplit : ℕ → ℕ → ℕ → Set
VarSplit n m l = ∀ (i : Fin n) → (Fin m ⊎ (Fin l))

VarSplitCompat : (σ : Sub m n ⋆) → (τ : Sub l n ⋆) → VarSplit n m l → Set
VarSplitCompat {m} {n} {l} σ τ vs = ∀ (i : Fin n) → P i (vs i)
  where
    P : (i : Fin n) → (Fin m ⊎ Fin l) → Set
    P i (inj₁ j) = Var j [ σ ]tm ≃tm Var i
    P i (inj₂ j) = Var j [ τ ]tm ≃tm Var i

isVar : Tm n → Set
isVar (Var i) = ⊤
isVar (Coh Δ A σ) = ⊥

getVarFin : (t : Tm n) → .⦃ isVar t ⦄ → Fin n
getVarFin (Var j) = j

varToVar : Sub n m A → Set
varToVar ⟨⟩ = ⊤
varToVar ⟨ σ , t ⟩ = varToVar σ × isVar t

ty-is-globular : Ty n → Set
ty-is-globular ⋆ = ⊤
ty-is-globular (s ─⟨ A ⟩⟶ t) = isVar s × ty-is-globular A × isVar t

ctx-is-globular : Ctx n → Set
ctx-is-globular ∅ = ⊤
ctx-is-globular (Γ , A) = (ctx-is-globular Γ) × (ty-is-globular A)

varToVarFunction : (σ : Sub n m ⋆) → .⦃ varToVar σ ⦄ → (i : Fin n) → Fin m
varToVarFunction ⟨ σ , t ⟩ ⦃ v ⦄ zero = getVarFin t ⦃ proj₂ v ⦄
varToVarFunction ⟨ σ , t ⟩ ⦃ v ⦄ (suc i) = varToVarFunction σ ⦃ proj₁ v ⦄ i

VarSplitFull₁ : (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → VarSplit n m l → Set
VarSplitFull₁ {m} σ vs = ∀ (i : Fin m) → vs (varToVarFunction σ i) ≡ inj₁ i

VarSplitFull₂ : (τ : Sub l n ⋆) → .⦃ varToVar τ ⦄ → VarSplit n m l → Set
VarSplitFull₂ {l} τ vs = ∀ (i : Fin l) → vs (varToVarFunction τ i) ≡ inj₂ i
