{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Typing index rule
open import Catt.Typing.Properties.Base index rule public
open import Catt.Typing.Properties.Lifting index rule lift-rule public
open import Catt.Typing.Properties.Substitution index rule lift-rule susp-rule sub-rule public
open import Relation.Binary.PropositionalEquality
open import Catt.Variables

unrestrict-restrict-≈ : (σ : Sub (2 + n) m A) → s ≈[ Δ ]tm getFst [ σ ]tm → t ≈[ Δ ]tm getSnd [ σ ]tm → unrestrict (restrict σ s t) ≈[ Δ ]s σ
unrestrict-restrict-≈ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = Ext≈ (Ext≈ refl≈s p) q
unrestrict-restrict-≈ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ p q = Ext≈ (unrestrict-restrict-≈ ⟨ ⟨ σ , u ⟩ , s ⟩ p q) refl≈tm

restrictTy : {σ : Sub (2 + n) m A}
           → Typing-Sub (suspCtx Γ) Δ σ
           → Typing-Tm Δ s A
           → Typing-Tm Δ t A
           → s ≈[ Δ ]tm getFst [ σ ]tm
           → t ≈[ Δ ]tm getSnd [ σ ]tm
           → Typing-Sub Γ Δ (restrict σ s t)
restrictTy {Γ = ∅} (TyExt (TyExt (TyNull z) y) x) sty tty p q = TyNull (TyArr sty z tty)
restrictTy {Γ = ∅ , A} (TyExt (TyExt (TyExt σty z) y) x) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) sty tty p q) (term-conversion x (sym≈ty (trans≈ty (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _))) (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))))
restrictTy {Γ = ∅ , B , A} (TyExt (TyExt (TyExt σty z) y) x) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) sty tty p q) (term-conversion x (sym≈ty (trans≈ty (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _))) (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))))
restrictTy {Γ = Γ , C , B , A} (TyExt (TyExt (TyExt σty z) y) x) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) sty tty p q) (term-conversion x (sym≈ty (trans≈ty (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _))) (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))))

var-Ty : (Γ : Ctx n) → (i : Fin n) → Typing-Tm Γ (Var i) (Γ ‼ i)
var-Ty (Γ , A) zero = TyVarZ refl≈ty
var-Ty (Γ , A) (suc i) = TyVarS i (var-Ty Γ i) refl≈ty

isVar-Ty : (Γ : Ctx n) → (t : Tm n) → .⦃ _ : isVar t ⦄ → Typing-Tm Γ t (Γ ‼ getVarFin t)
isVar-Ty Γ (Var i) = var-Ty Γ i

Ty-unique : Typing-Tm Γ t A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique (TyVarZ x) (TyVarZ y) = trans≈ty (sym≈ty x) y
Ty-unique (TyVarS _ tty x) (TyVarS _ tty2 y) = trans≈ty (trans≈ty (sym≈ty x) (lift-ty-equality (Ty-unique tty tty2))) y
Ty-unique (TyCoh _ _ _ _ x) (TyCoh _ _ _ _ y) = trans≈ty (sym≈ty x) y

Ty-unique-≃ : s ≃tm t → Typing-Tm Γ s A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique-≃ p tty tty2 with ≃tm-to-≡ p
... | refl = Ty-unique tty tty2

truncate′-≈ : d ≡ d′ → A ≈[ Γ ]ty A′ → truncate′ d A ≈[ Γ ]ty truncate′ d′ A′
truncate′-≈ {d = zero} refl p = p
truncate′-≈ {d = suc d} refl Star≈ = Star≈
truncate′-≈ {d = suc d} refl (Arr≈ x p x₁) = truncate′-≈ {d = d} refl p

truncate-≈ : d ≡ d′ → A ≈[ Γ ]ty A′ → truncate d A ≈[ Γ ]ty truncate d′ A′
truncate-≈ {d} {d′} {A = A} {A′ = A′} refl p = truncate′-≈ {d = ty-dim A ∸ d} {d′ = ty-dim A′ ∸ d} (cong (_∸ d) (≈ty-preserve-height p)) p

src-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → s ≈[ Γ ]tm s′
src-eq (Arr≈ p q r) = p

tgt-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → t ≈[ Γ ]tm t′
tgt-eq (Arr≈ p q r) = r

base-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → A ≈[ Γ ]ty A′
base-eq (Arr≈ p q r) = q
