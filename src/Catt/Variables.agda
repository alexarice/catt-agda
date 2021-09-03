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

VarSplit : (Γ : Ctx n) → (σ : Sub Δ Γ) → (τ : Sub Υ Γ) → Set
VarSplit {Δ = Δ} {Υ = Υ} Γ σ τ = ∀ (i : Fin (ctxLength Γ)) → (Σ[ j ∈ Fin (ctxLength Δ) ] (Var j [ σ ]tm ≃tm Var {Γ = Γ} i)) ⊎ (Σ[ j ∈ Fin (ctxLength Υ) ] (Var j [ τ ]tm ≃tm Var {Γ = Γ} i))

isVar : Tm Γ → Set
isVar (Var i) = ⊤
isVar (Coh Δ A σ) = ⊥

varToVar : Sub Γ Δ → Set
varToVar ⟨⟩ = ⊤
varToVar ⟨ σ , Var i ⟩ = varToVar σ
varToVar ⟨ σ , Coh Δ A σ₁ ⟩ = ⊥

ty-is-globular : Ty Γ d → Set
ty-is-globular ⋆ = ⊤
ty-is-globular (s ─⟨ A ⟩⟶ t) = isVar s × ty-is-globular A × isVar t

ctx-is-globular : Ctx n → Set
ctx-is-globular ∅ = ⊤
ctx-is-globular (Γ , A) = (ctx-is-globular Γ) × (ty-is-globular A)

varToVarFunction : (σ : Sub Γ Δ) → .(varToVar σ) → (i : Fin (ctxLength Γ)) → Fin (ctxLength Δ)
varToVarFunction ⟨ σ , Var j ⟩ v zero = j
varToVarFunction ⟨ σ , Var j ⟩ v (suc i) = varToVarFunction σ v i

varToVarFunctionProp : (σ : Sub Γ Δ) → .(v : varToVar σ) → (i : Fin (ctxLength Γ)) → Var {Γ = Δ} (varToVarFunction σ v i) ≃tm Var i [ σ ]tm
varToVarFunctionProp ⟨ σ , Var j ⟩ v zero = refl≃tm
varToVarFunctionProp ⟨ σ , Var j ⟩ v (suc i) = varToVarFunctionProp σ v i

liftSub-preserve-var-to-var : (σ : Sub Γ Δ) → .(varToVar σ) → varToVar (liftSub {A = A} σ)
liftSub-preserve-var-to-var ⟨⟩ v = tt
liftSub-preserve-var-to-var ⟨ σ , Var i ⟩ v = liftSub-preserve-var-to-var σ v

liftTerm-preserve-isVar : (t : Tm Γ) → .(isVar t) → isVar (liftTerm {A = A} t)
liftTerm-preserve-isVar (Var i) v = tt

liftType-preserve-is-globular : (A : Ty Γ d) → (ty-is-globular A) → ty-is-globular (liftType {A = B} A)
liftType-preserve-is-globular ⋆ g = tt
liftType-preserve-is-globular (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = liftTerm-preserve-isVar s vs ,, liftType-preserve-is-globular A gA ,, liftTerm-preserve-isVar t vt

id-is-var-to-var : (Γ : Ctx n) → varToVar (idSub Γ)
id-is-var-to-var ∅ = tt
id-is-var-to-var (Γ , A) = liftSub-preserve-var-to-var (idSub Γ) (id-is-var-to-var Γ)

extend-var-to-var : (σ : Sub Γ Δ) → (varToVar σ) → {A : Ty Γ d} → (t : Tm Δ) → .(isVar t) → varToVar (⟨_,_⟩ σ {A} t)
extend-var-to-var σ v (Var i) vt = v
