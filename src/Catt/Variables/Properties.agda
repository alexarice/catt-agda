module Catt.Variables.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Globular
open import Catt.Globular.Properties

getVarFinProp : (t : Tm n) → .⦃ _ : isVar t ⦄ → t ≃tm Var (getVarFin t)
getVarFinProp (Var j) = refl≃tm

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

getVarFin-≃ : (p : s ≃tm t) → .⦃ v : isVar s ⦄ → getVarFin s ≡ getVarFin t ⦃ ≃tm-preserve-isVar p v ⦄
getVarFin-≃ (Var≃ x y) = toℕ-injective y

getVarFin-lift : (t : Tm n) → .⦃ v : isVar t ⦄ → getVarFin (liftTerm t) ⦃ liftTerm-preserve-isVar t v ⦄ ≡ suc (getVarFin t)
getVarFin-lift (Var i) = refl

varToVarFunction-≃ : {σ τ : Sub n m ⋆} → (p : σ ≃s τ) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction σ i ≡ varToVarFunction τ ⦃ ≃s-preserve-var-to-var p it ⦄ i
varToVarFunction-≃ p i with ≃s-to-≡ p
... | refl = refl

id-is-var-to-var : varToVar (idSub {n})
id-is-var-to-var {zero} = tt
id-is-var-to-var {suc n} = liftSub-preserve-var-to-var idSub ⦃ id-is-var-to-var {n} ⦄ ,, tt

varToVarFunction-lift : (σ : Sub n m ⋆) → .⦃ _ : varToVar σ ⦄ → (i : Fin n) → varToVarFunction (liftSub σ) ⦃ liftSub-preserve-var-to-var σ ⦄ i ≡ suc (varToVarFunction σ i)
varToVarFunction-lift ⟨ σ , Var j ⟩ zero = refl
varToVarFunction-lift ⟨ σ , Var j ⟩ ⦃ v ⦄ (suc i) = varToVarFunction-lift σ ⦃ proj₁ v ⦄ i

varToVarFunction-idSub : (i : Fin n) → varToVarFunction idSub ⦃ id-is-var-to-var {n} ⦄ i ≡ i
varToVarFunction-idSub {suc n} zero = refl
varToVarFunction-idSub {suc n} (suc i) = trans (varToVarFunction-lift idSub ⦃ id-is-var-to-var {n} ⦄ i) (cong suc (varToVarFunction-idSub i))

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

ty-base-globular : (A : Ty n) → ty-is-globular A → ty-is-globular (ty-base A)
ty-base-globular ⋆ g = tt
ty-base-globular (s ─⟨ A ⟩⟶ t) (g1 ,, g2 ,, g3) = g2

ty-src-globular : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-is-globular A → isVar (ty-src A)
ty-src-globular (s ─⟨ A ⟩⟶ t) (g1 ,, g2 ,, g3) = g1

ty-tgt-globular : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-is-globular A → isVar (ty-tgt A)
ty-tgt-globular (s ─⟨ A ⟩⟶ t) (g1 ,, g2 ,, g3) = g3
