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
VarSplitCompat {m} {n} {l} σ τ vs = ∀ (i : Fin n) → S i (vs i)
  where
    S : (i : Fin n) → (Fin m ⊎ Fin l) → Set
    S i (inj₁ j) = Var j [ σ ]tm ≃tm Var i
    S i (inj₂ j) = Var j [ τ ]tm ≃tm Var i

isVar : Tm n → Set
isVar (Var i) = ⊤
isVar (Coh Δ A σ) = ⊥

getVarFin : (t : Tm n) → .⦃ isVar t ⦄ → Fin n
getVarFin (Var j) = j

getVarFinProp : (t : Tm n) → .⦃ _ : isVar t ⦄ → t ≃tm Var (getVarFin t)
getVarFinProp (Var j) = refl≃tm

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

ty-globular-src : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-src A)
ty-globular-tgt : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-tgt A)
ty-globular-base : (A : Ty n (suc d)) → (ty-is-globular A) → ty-is-globular (ty-base A)

ty-globular-src (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vs

ty-globular-tgt (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vt

ty-globular-base (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = gA

varToVarFunction : (σ : Sub n m) → .⦃ varToVar σ ⦄ → (i : Fin n) → Fin m
varToVarFunction ⟨ σ , Var j ⟩ zero = j
varToVarFunction ⟨ σ , Var j ⟩ (suc i) = varToVarFunction σ i

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
