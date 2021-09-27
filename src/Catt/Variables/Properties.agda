{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Variables.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Relation.Binary.PropositionalEquality
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Nat.Properties
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Globular.Properties

getVarFinProp : (t : Tm n) → .⦃ _ : isVar t ⦄ → t ≃tm Var (getVarFin t)
getVarFinProp (Var j) = refl≃tm

-- ty-globular-src : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-src A)
-- ty-globular-tgt : (A : Ty n (suc d)) → (ty-is-globular A) → isVar (ty-tgt A)
-- ty-globular-base : (A : Ty n (suc d)) → (ty-is-globular A) → ty-is-globular (ty-base A)

-- ty-globular-src (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vs

-- ty-globular-tgt (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = vt

-- ty-globular-base (s ─⟨ A ⟩⟶ t) (vs ,, gA ,, vt) = gA

varToVarFunctionProp : (σ : Sub n m ⋆) → .⦃ v : varToVar σ ⦄ → (i : Fin n) → Var (varToVarFunction σ i) ≃tm Var i [ σ ]tm
varToVarFunctionProp ⟨ σ , Var j ⟩ zero = refl≃tm
varToVarFunctionProp ⟨ σ , Var j ⟩ ⦃ v ⦄ (suc i) = varToVarFunctionProp σ ⦃ proj₁ v ⦄ i

liftSub-preserve-var-to-var : (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → varToVar (liftSub σ)
liftSub-preserve-var-to-var ⟨⟩ = tt
liftSub-preserve-var-to-var ⟨ σ , Var i ⟩ ⦃ p ⦄ = (liftSub-preserve-var-to-var σ ⦃ proj₁ p ⦄) ,, tt

liftTerm-preserve-isVar : (t : Tm n) → .(isVar t) → isVar (liftTerm t)
liftTerm-preserve-isVar (Var i) v = tt

liftType-preserve-is-globular : (A : Ty n) → (ty-is-globular A) → ty-is-globular (liftType A)
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
≃s-preserve-var-to-var (Ext≃ p (Var≃ x x₁)) c = (≃s-preserve-var-to-var p (proj₁ c)) ,, tt

varToVarFunction-≃ : {σ τ : Sub n m ⋆} → (p : σ ≃s τ) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction σ i ≡ varToVarFunction τ ⦃ ≃s-preserve-var-to-var p it ⦄ i
varToVarFunction-≃ p i with ≃s-to-≡ p
... | refl = refl

id-is-var-to-var : (n : ℕ) → varToVar (idSub n)
id-is-var-to-var zero = tt
id-is-var-to-var (suc n) = liftSub-preserve-var-to-var (idSub n) ⦃ id-is-var-to-var n ⦄ ,, tt

varToVarFunction-lift : (σ : Sub n m ⋆) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction (liftSub σ) ⦃ liftSub-preserve-var-to-var σ ⦄ i ≡ suc (varToVarFunction σ i)
varToVarFunction-lift ⟨ σ , Var j ⟩ zero = refl
varToVarFunction-lift ⟨ σ , Var j ⟩ ⦃ v ⦄ (suc i) = varToVarFunction-lift σ ⦃ proj₁ v ⦄ i

varToVarFunction-idSub : (n : ℕ) → (i : Fin n) → varToVarFunction (idSub n) ⦃ id-is-var-to-var n ⦄ i ≡ i
varToVarFunction-idSub (suc n) zero = refl
varToVarFunction-idSub (suc n) (suc i) = trans (varToVarFunction-lift (idSub n) ⦃ id-is-var-to-var n ⦄ i) (cong suc (varToVarFunction-idSub n i))

extend-var-to-var : (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → (t : Tm m) → .⦃ isVar t ⦄ → varToVar ⟨ σ , t ⟩
extend-var-to-var σ ⦃ v ⦄ (Var i) = v ,, tt

idSub≃-var-to-var : (p : Γ ≃c Δ) → varToVar (idSub≃ p)
idSub≃-var-to-var Emp≃ = tt
idSub≃-var-to-var (Add≃ p x) = liftSub-preserve-var-to-var (idSub≃ p) ⦃ idSub≃-var-to-var p ⦄ ,, tt

idSub≃-func : (p : Γ ≃c Δ) → Fin (ctxLength Γ) → Fin (ctxLength Δ)
idSub≃-func p = varToVarFunction (idSub≃ p) ⦃ idSub≃-var-to-var p ⦄

varToVarFunction-idSub≃ : {Γ Δ : Ctx n} → (p : Γ ≃c Δ) → (i : Fin n) → idSub≃-func p i ≡ i
varToVarFunction-idSub≃ (Add≃ p x) zero = refl
varToVarFunction-idSub≃ (Add≃ p x) (suc i) = trans (varToVarFunction-lift (idSub≃ p) ⦃ idSub≃-var-to-var p ⦄ i) (cong suc (varToVarFunction-idSub≃ p i))

var-to-var-comp-ty : (A : Ty n) → ⦃ ty-is-globular A ⦄ → (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → ty-is-globular (A [ σ ]ty)
var-to-var-comp-tm : (t : Tm n) → ⦃ isVar t ⦄ → (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → isVar (t [ σ ]tm)
var-to-var-comp-sub : (τ : Sub l n ⋆) → ⦃ varToVar τ ⦄ → (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → varToVar (σ ∘ τ)

var-to-var-comp-ty ⋆ σ = tt
var-to-var-comp-ty (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ σ = var-to-var-comp-tm s ⦃ a ⦄ σ ,, var-to-var-comp-ty A ⦃ b ⦄ σ ,, var-to-var-comp-tm t ⦃ c ⦄ σ

var-to-var-comp-tm (Var zero) ⟨ σ , Var i ⟩ = tt
var-to-var-comp-tm (Var (suc i)) ⟨ σ , Var j ⟩ ⦃ v ⦄ = var-to-var-comp-tm (Var i) σ ⦃ proj₁ v ⦄

var-to-var-comp-sub ⟨⟩ σ = tt
var-to-var-comp-sub ⟨ τ , Var j ⟩ ⦃ v ⦄ σ with Var j [ σ ]tm | var-to-var-comp-tm (Var j) σ ⦃ it ⦄
... | Var i | q = var-to-var-comp-sub τ ⦃ proj₁ v ⦄ σ ,, tt

varToVarFunc-comp-sub : (τ : Sub m l ⋆) → .⦃ _ : varToVar τ ⦄ → (σ : Sub n m ⋆) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction (τ ∘ σ) ⦃ var-to-var-comp-sub σ τ ⦄ i ≡ varToVarFunction τ (varToVarFunction σ i)
varToVarFunc-comp-tm : (τ : Sub n l ⋆) → .⦃ _ : varToVar τ ⦄ → (i : Fin n) → getVarFin (Var i [ τ ]tm) ⦃ var-to-var-comp-tm (Var i) τ ⦄ ≡ varToVarFunction τ i

varToVarFunc-comp-sub τ ⟨ σ , Var j ⟩ zero = varToVarFunc-comp-tm τ j
varToVarFunc-comp-sub τ ⟨ σ , Var j ⟩ ⦃ v ⦄ (suc i) = varToVarFunc-comp-sub τ σ ⦃ proj₁ v ⦄ i

varToVarFunc-comp-tm ⟨ τ , t ⟩ zero = refl
varToVarFunc-comp-tm ⟨ τ , t ⟩ ⦃ v ⦄ (suc i) = varToVarFunc-comp-tm τ ⦃ proj₁ v ⦄ i

suspSub-var-to-var : (σ : Sub n m ⋆) → ⦃ varToVar σ ⦄ → varToVar (suspSub σ)
suspSub-var-to-var ⟨⟩ = (tt ,, tt) ,, tt
suspSub-var-to-var ⟨ σ , Var i ⟩ ⦃ v ⦄ = suspSub-var-to-var σ ⦃ proj₁ v ⦄ ,, tt

suspTm-var : (t : Tm n) → ⦃ isVar t ⦄ → isVar (suspTm t)
suspTm-var (Var i) = tt

truncate-≤ : (d : ℕ) → (A : Ty n) → d ≤ ty-dim A → truncate d (s ─⟨ A ⟩⟶ t) ≃ty truncate d A
truncate-≤ d A p
  rewrite +-∸-assoc 1 p = refl≃ty

suspTy-truncate : (A : Ty n) → truncate 1 (suspTy A) ≃ty getFst {n = n} ─⟨ ⋆ ⟩⟶ getSnd
suspTy-truncate ⋆ = refl≃ty
suspTy-truncate (s ─⟨ A ⟩⟶ t) = trans≃ty (truncate-≤ 1 (suspTy A) (≤-trans (s≤s z≤n) (≤-reflexive (sym (susp-dim A))))) (suspTy-truncate A)
-- suspTy-sub-truncate : (A : Ty n) → (σ : Sub (2 + n) m B) → truncate (suc (ty-dim B)) (suspTy A [ σ ]ty) ≃ty (getFst [ σ ]tm) ─⟨ B ⟩⟶ (getSnd [ σ ]tm)
-- suspTy-sub-truncate {B = B} ⋆ σ
--   rewrite n∸n≡0 (ty-dim B) = refl≃ty
-- suspTy-sub-truncate {B = B} (s ─⟨ A ⟩⟶ t) σ = trans≃ty (truncate-≤ {s = suspTm s [ σ ]tm} {t = suspTm t [ σ ]tm} (suc (ty-dim B)) (suspTy A [ σ ]ty) (≤-trans (s≤s (m≤n+m (ty-dim B) (ty-dim A))) (≤-reflexive (trans (cong (_+ ty-dim B) (sym (susp-dim A))) (sub-dim′ σ (suspTy A)))))) (suspTy-sub-truncate A σ)

truncate′-≃ : d ≡ d′ → A ≃ty A′ → truncate′ d A ≃ty truncate′ d′ A′
truncate′-≃ {d = zero} refl p = p
truncate′-≃ {d = suc d} refl (Star≃ x) = Star≃ x
truncate′-≃ {d = suc d} refl (Arr≃ x p x₁) = truncate′-≃ {d = d} refl p

truncate-≃ : d ≡ d′ → A ≃ty A′ → truncate d A ≃ty truncate d′ A′
truncate-≃ {d} {d′} {A = A} {A′ = A′} refl p = truncate′-≃ {d = ty-dim A ∸ d} {d′ = ty-dim A′ ∸ d} (cong (_∸ d) (≃ty-preserve-height p)) p

truncate′-sub : (d : ℕ) → (A : Ty n) → (σ : Sub n m B) → d ≤ ty-dim A → truncate′ d (A [ σ ]ty) ≃ty truncate′ d A [ σ ]ty
truncate′-sub zero A σ p = refl≃ty
truncate′-sub (suc d) (s ─⟨ A ⟩⟶ t) σ p = truncate′-sub d A σ (≤-pred p)

truncate-sub : (d : ℕ) → (A : Ty n) → (σ : Sub n m B) → truncate (d + ty-dim B) (A [ σ ]ty) ≃ty truncate d A [ σ ]ty
truncate-sub {B = B} d A σ = begin
  < truncate (d + ty-dim B) (A [ σ ]ty) >ty ≡⟨⟩
  < truncate′ (ty-dim (A [ σ ]ty) ∸ (d + ty-dim B)) (A [ σ ]ty) >ty
    ≈⟨ truncate′-≃ lem refl≃ty ⟩
  < truncate′ (ty-dim A ∸ d) (A [ σ ]ty) >ty
    ≈⟨ truncate′-sub (ty-dim A ∸ d) A σ (m∸n≤m (ty-dim A) d) ⟩
  < truncate′ (ty-dim A ∸ d) A [ σ ]ty >ty ≡⟨⟩
  < truncate d A [ σ ]ty >ty ∎
  where
    lem : ty-dim (A [ σ ]ty) ∸ (d + ty-dim B) ≡ ty-dim A ∸ d
    lem = begin
      ty-dim (A [ σ ]ty) ∸ (d + ty-dim B)
        ≡˘⟨ cong₂ _∸_ (sub-dim′ σ A) (+-comm (ty-dim B) d) ⟩
      ty-dim A + ty-dim B ∸ (ty-dim B + d)
        ≡˘⟨ ∸-+-assoc (ty-dim A + ty-dim B) (ty-dim B) d ⟩
      ty-dim A + ty-dim B ∸ ty-dim B ∸ d
        ≡⟨ cong (_∸ d) (+-∸-assoc (ty-dim A) {n = ty-dim B} ≤-refl) ⟩
      ty-dim A + (ty-dim B ∸ ty-dim B) ∸ d
        ≡⟨ cong (λ - → ty-dim A + - ∸ d) (n∸n≡0 (ty-dim B)) ⟩
      ty-dim A + 0 ∸ d
        ≡⟨ cong (_∸ d) (+-identityʳ (ty-dim A)) ⟩
      ty-dim A ∸ d ∎
      where
        open ≡-Reasoning

    open Reasoning ty-setoid
