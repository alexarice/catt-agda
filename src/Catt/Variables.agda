{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Variables where

open import Catt.Syntax
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Fin
open import Catt.Syntax.SyntacticEquality
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality

VarSplit : ℕ → ℕ → ℕ → Set
VarSplit n m l = ∀ (i : Fin n) → (Fin m ⊎ (Fin l))

VarSplitCompat : (σ : Sub m n) → (τ : Sub l n) → VarSplit n m l → Set
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

varToVar : Sub n m → Set
varToVar ⟨⟩ = ⊤
varToVar ⟨ σ , Var i ⟩ = varToVar σ
varToVar ⟨ σ , Coh Δ A σ₁ ⟩ = ⊥

ty-is-globular : Ty n d → Set
ty-is-globular ⋆ = ⊤
ty-is-globular (s ─⟨ A ⟩⟶ t) = isVar s × ty-is-globular A × isVar t

ctx-is-globular : Ctx n → Set
ctx-is-globular ∅ = ⊤
ctx-is-globular (Γ , A) = (ctx-is-globular Γ) × (ty-is-globular A)

varToVarFunction : (σ : Sub n m) → .⦃ varToVar σ ⦄ → (i : Fin n) → Fin m
varToVarFunction ⟨ σ , Var j ⟩ zero = j
varToVarFunction ⟨ σ , Var j ⟩ (suc i) = varToVarFunction σ i
