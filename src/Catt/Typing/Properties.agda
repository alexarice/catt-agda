open import Catt.Typing.Rule

module Catt.Typing.Properties {index : Set}
                              (rule : index → Rule)
                              (lift-rule : ∀ i → LiftRule rule (rule i))
                              (susp-rule : ∀ i → SuspRule rule (rule i))
                              (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Suspension

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule public
open import Catt.Typing.Properties.Lifting rule lift-rule public
open import Catt.Typing.Properties.Substitution.Suspended rule lift-rule susp-rule sub-rule public


unrestrict-restrict-≈ : (σ : Sub (2 + n) m A) → s ≈[ Δ ]tm get-fst [ σ ]tm → t ≈[ Δ ]tm get-snd [ σ ]tm → unrestrict (restrict σ s t) ≈[ Δ ]s σ
unrestrict-restrict-≈ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = Ext≈ (Ext≈ refl≈s p) q
unrestrict-restrict-≈ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ p q = Ext≈ (unrestrict-restrict-≈ ⟨ ⟨ σ , u ⟩ , s ⟩ p q) refl≈tm

restrictTy : {σ : Sub (2 + n) m A}
           → Typing-Sub (susp-ctx Γ) Δ σ
           → Typing-Ctx Γ
           → Typing-Tm Δ s A
           → Typing-Tm Δ t A
           → s ≈[ Δ ]tm get-fst [ σ ]tm
           → t ≈[ Δ ]tm get-snd [ σ ]tm
           → Typing-Sub Γ Δ (restrict σ s t)
restrictTy {Γ = ∅} (TyExt (TyExt (TyNull z) y) x) Γty sty tty p q = TyNull (TyArr sty z tty)
restrictTy {Γ = ∅ , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd TyEmp Aty) sty tty p q
  = TyExt (restrictTy (TyExt (TyExt σty z) y) TyEmp sty tty p q)
          (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (susp-ty A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))
                              (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))
restrictTy {Γ = ∅ , B , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd Γty Aty) sty tty p q
  = TyExt (restrictTy (TyExt (TyExt σty z) y) Γty sty tty p q)
          (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (susp-ty A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))
                              (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))
restrictTy {Γ = Γ , C , B , A} (TyExt (TyExt (TyExt σty z) y) x) (TyAdd Γty Aty) sty tty p q
  = TyExt (restrictTy (TyExt (TyExt σty z) y) Γty sty tty p q)
          (TyConv x (trans≈ty (sym≈ty (apply-sub-eq-ty (susp-ty A) (unrestrict-restrict-≈ ⟨ ⟨ _ , _ ⟩ , _ ⟩ p q)))
                              (reflexive≈ty (unrestrict-comp-ty A (restrict ⟨ ⟨ _ , _ ⟩ , _ ⟩ _ _)))))
