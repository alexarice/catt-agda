open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Typing.Properties {index : Set}
                              (rule : index → Rule)
                              (lift-rule : ∀ i → P.LiftRule rule i)
                              (susp-rule : ∀ i → P.SuspRule rule i)
                              (sub-rule : ∀ i → P.SubRule rule i) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Globular
open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule public
open import Catt.Typing.Properties.Lifting rule lift-rule public
open import Catt.Typing.Properties.Substitution.Suspended rule lift-rule susp-rule sub-rule public
open import Catt.Variables

unrestrict-restrict-≈ : (σ : Sub (2 + n) m A) → s ≈[ Δ ]tm getFst [ σ ]tm → t ≈[ Δ ]tm getSnd [ σ ]tm → unrestrict (restrict σ s t) ≈[ Δ ]s σ
unrestrict-restrict-≈ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = Ext≈ (Ext≈ refl≈s p) q
unrestrict-restrict-≈ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ p q = Ext≈ (unrestrict-restrict-≈ ⟨ ⟨ σ , u ⟩ , s ⟩ p q) refl≈tm

restrictTy : {σ : Sub (2 + n) m A}
           → Typing-Sub (suspCtx Γ) Δ σ
           → Typing-Ctx Γ
           → Typing-Tm Δ s A
           → Typing-Tm Δ t A
           → s ≈[ Δ ]tm getFst [ σ ]tm
           → t ≈[ Δ ]tm getSnd [ σ ]tm
           → Typing-Sub Γ Δ (restrict σ s t)
restrictTy {Γ = ∅} (TyExt (TyExt (TyNull z) y) x) Γty sty tty p q = TyNull (TyArr sty z tty)
restrictTy {Γ = ∅ , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd TyEmp Aty) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) TyEmp sty tty p q) (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q))) (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))
restrictTy {Γ = ∅ , B , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd Γty Aty) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) Γty sty tty p q) (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q))) (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))
restrictTy {Γ = Γ , C , B , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd Γty Aty) sty tty p q = TyExt (restrictTy (TyExt (TyExt σty z) y) Γty sty tty p q) (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (suspTy A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q))) (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))

truncate′-≈ : d ≡ d′ → A ≈[ Γ ]ty A′ → truncate′ d A ≈[ Γ ]ty truncate′ d′ A′
truncate′-≈ {d = zero} refl p = p
truncate′-≈ {d = suc d} refl Star≈ = refl≈ty
truncate′-≈ {d = suc d} refl (Arr≈ x p x₁) = truncate′-≈ {d = d} refl p

truncate-≈ : d ≡ d′ → A ≈[ Γ ]ty A′ → truncate d A ≈[ Γ ]ty truncate d′ A′
truncate-≈ {d} {d′} {A = A} {A′ = A′} refl p = truncate′-≈ {d = ty-dim A ∸ d} {d′ = ty-dim A′ ∸ d} (cong (_∸ d) (≈ty-preserve-height p)) p
