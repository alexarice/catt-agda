module Catt.Variables where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties

isVar : Tm n → Set
isVar (Var i) = ⊤
isVar (Coh Δ A σ) = ⊥

getVarFin : (t : Tm n) → .⦃ isVar t ⦄ → Fin n
getVarFin (Var j) = j

varToVar : Sub n m A → Set
varToVar ⟨ A ⟩′ = ⊤
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
