{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Variables.Properties where

open import Catt.Syntax
open import Catt.Variables
open import Relation.Binary.PropositionalEquality
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)

getVarFinProp : (t : Tm n) → .⦃ _ : isVar t ⦄ → t ≃tm Var (getVarFin t)
getVarFinProp (Var j) = refl≃tm

ty-globular-src : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-src A)
ty-globular-tgt : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-tgt A)
ty-globular-base : (A : Ty n (suc d)) → (ty-is-globular A) → ty-is-globular (ty-base A)

ty-globular-src (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vs

ty-globular-tgt (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vt

ty-globular-base (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = gA

varToVarFunctionProp : (σ : Sub n m) → .⦃ v : varToVar σ ⦄ → (i : Fin n) → Var (varToVarFunction σ i) ≃tm Var i [ σ ]tm
varToVarFunctionProp ⟨ σ , Var j ⟩ zero = refl≃tm
varToVarFunctionProp ⟨ σ , Var j ⟩ (suc i) = varToVarFunctionProp σ i

liftSub-preserve-var-to-var : (σ : Sub n m) → ⦃ varToVar σ ⦄ → varToVar (liftSub σ)
liftSub-preserve-var-to-var ⟨⟩ = tt
liftSub-preserve-var-to-var ⟨ σ , Var i ⟩ = liftSub-preserve-var-to-var σ

liftTerm-preserve-isVar : (t : Tm n) → .(isVar t) → isVar (liftTerm t)
liftTerm-preserve-isVar (Var i) v = tt

liftType-preserve-is-globular : (A : Ty n d) → (ty-is-globular A) → ty-is-globular (liftType A)
liftType-preserve-is-globular ⋆ g = tt
liftType-preserve-is-globular (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = liftTerm-preserve-isVar s vs ,, liftType-preserve-is-globular A gA ,, liftTerm-preserve-isVar t vt

≃c-preserve-globular : Γ ≃c Δ → ctx-is-globular Γ → ctx-is-globular Δ
≃ty-preserve-globular : A ≃ty B → ty-is-globular A → ty-is-globular B
≃tm-preserve-isVar : s ≃tm t → isVar s → isVar t
≃s-preserve-var-to-var : σ ≃s τ → varToVar σ → varToVar τ

≃c-preserve-globular Emp≃ c = tt
≃c-preserve-globular (Add≃ p x) (c ,, d) = ≃c-preserve-globular p c ,, ≃ty-preserve-globular x d

≃ty-preserve-globular (Star≃ x) c = tt
≃ty-preserve-globular (Arr≃ p q r) (a ,, b ,, c) = ≃tm-preserve-isVar p a ,, ≃ty-preserve-globular q b ,, ≃tm-preserve-isVar r c

≃tm-preserve-isVar (Var≃ x x₁) c = tt

≃s-preserve-var-to-var (Null≃ x) c = tt
≃s-preserve-var-to-var (Ext≃ p (Var≃ x x₁)) c = ≃s-preserve-var-to-var p c

id-is-var-to-var : (n : ℕ) → varToVar (idSub n)
id-is-var-to-var zero = tt
id-is-var-to-var (suc n) = liftSub-preserve-var-to-var (idSub n) ⦃ id-is-var-to-var n ⦄

varToVarFunction-lift : (σ : Sub n m) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction (liftSub σ) ⦃ liftSub-preserve-var-to-var σ ⦄ i ≡ suc (varToVarFunction σ i)
varToVarFunction-lift ⟨ σ , Var j ⟩ zero = refl
varToVarFunction-lift ⟨ σ , Var j ⟩ (suc i) = varToVarFunction-lift σ i

varToVarFunction-idSub : (n : ℕ) → (i : Fin n) → varToVarFunction (idSub n) ⦃ id-is-var-to-var n ⦄ i ≡ i
varToVarFunction-idSub (suc n) zero = refl
varToVarFunction-idSub (suc n) (suc i) = trans (varToVarFunction-lift (idSub n) ⦃ id-is-var-to-var n ⦄ i) (cong suc (varToVarFunction-idSub n i))

extend-var-to-var : (σ : Sub n m) → ⦃ varToVar σ ⦄ → (t : Tm m) → .⦃ isVar t ⦄ → varToVar ⟨ σ , t ⟩
extend-var-to-var σ ⦃ v ⦄ (Var i) = v

idSub≃-var-to-var : (p : Γ ≃c Δ) → varToVar (idSub≃ p)
idSub≃-var-to-var Emp≃ = tt
idSub≃-var-to-var (Add≃ p x) = liftSub-preserve-var-to-var (idSub≃ p) ⦃ idSub≃-var-to-var p ⦄

idSub≃-func : (p : Γ ≃c Δ) → Fin (ctxLength Γ) → Fin (ctxLength Δ)
idSub≃-func p = varToVarFunction (idSub≃ p) ⦃ idSub≃-var-to-var p ⦄

var-to-var-comp-ty : (A : Ty n d) → ⦃ ty-is-globular A ⦄ → (σ : Sub n m) → ⦃ varToVar σ ⦄ → ty-is-globular (A [ σ ]ty)
var-to-var-comp-tm : (t : Tm n) → ⦃ isVar t ⦄ → (σ : Sub n m) → ⦃ varToVar σ ⦄ → isVar (t [ σ ]tm)
var-to-var-comp-sub : (τ : Sub l n) → ⦃ varToVar τ ⦄ → (σ : Sub n m) → ⦃ varToVar σ ⦄ → varToVar (σ ∘ τ)

var-to-var-comp-ty ⋆ σ = tt
var-to-var-comp-ty (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ σ = var-to-var-comp-tm s ⦃ a ⦄ σ ,, var-to-var-comp-ty A ⦃ b ⦄ σ ,, var-to-var-comp-tm t ⦃ c ⦄ σ

var-to-var-comp-tm (Var zero) ⟨ σ , Var i ⟩ = tt
var-to-var-comp-tm (Var (suc i)) ⟨ σ , Var j ⟩ = var-to-var-comp-tm (Var i) σ

var-to-var-comp-sub ⟨⟩ σ = tt
var-to-var-comp-sub ⟨ τ , Var j ⟩ σ with Var j [ σ ]tm | var-to-var-comp-tm (Var j) σ ⦃ it ⦄
... | Var i | q = var-to-var-comp-sub τ σ
