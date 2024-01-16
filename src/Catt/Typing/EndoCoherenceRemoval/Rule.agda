module Catt.Typing.EndoCoherenceRemoval.Rule where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Typing.Rule

open Rule

EndoCoherenceRemoval : (Γ : Ctx m)
                     → (Δ : Ctx (suc n))
                     → (s : Tm (suc n))
                     → (A : Ty (suc n))
                     → (σ : Sub (suc n) m ⋆)
                     → Rule
EndoCoherenceRemoval Γ Δ s A σ .len = _
EndoCoherenceRemoval Γ Δ s A σ .tgtCtx = Γ
EndoCoherenceRemoval Γ Δ s A σ .lhs = Coh Δ (s ─⟨ A ⟩⟶ s) σ
EndoCoherenceRemoval Γ Δ s A σ .rhs = identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))

data EndoCoherenceRemovalIdx : Set where
  ECR : (Γ : Ctx m)
      → (Δ : Ctx (suc n))
      → (s : Tm (suc n))
      → (A : Ty (suc n))
      → (σ : Sub (suc n) m ⋆)
      → EndoCoherenceRemovalIdx

EndoCoherenceRemovalSet : RuleSet
EndoCoherenceRemovalSet .proj₁ = EndoCoherenceRemovalIdx
EndoCoherenceRemovalSet .proj₂ (ECR Γ Δ s A σ) = EndoCoherenceRemoval Γ Δ s A σ

ecr-lift : LiftCond EndoCoherenceRemovalSet
ecr-lift (ECR Γ Δ s A σ) B .proj₁ = ECR (Γ , B) Δ s A (lift-sub σ)
ecr-lift (ECR Γ Δ s A σ) B .proj₂ .ctxeq = refl≃c
ecr-lift (ECR Γ Δ s A σ) B .proj₂ .lhseq = refl≃tm
ecr-lift (ECR Γ Δ s A σ) B .proj₂ .rhseq
  = identity-≃ refl (trans≃s (lift-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))
                             (sym≃s (sub-from-disc-≃ (ty-dim A)
                                                     (ty-dim A)
                                                     (apply-lifted-sub-ty-≃ A σ)
                                                     (sym (sub-dim (lift-sub σ) A))
                                                     (trans (lift-ty-dim (A [ σ ]ty)) (sym (sub-dim σ A)))
                                                     (apply-lifted-sub-tm-≃ s σ))))

ecr-susp : SuspCond EndoCoherenceRemovalSet
ecr-susp (ECR Γ Δ s A σ) .proj₁ = ECR (susp-ctx Γ) (susp-ctx Δ) (susp-tm s) (susp-ty A) (susp-sub σ)
ecr-susp (ECR Γ Δ s A σ) .proj₂ .ctxeq = refl≃c
ecr-susp (ECR Γ Δ s A σ) .proj₂ .lhseq = refl≃tm
ecr-susp (ECR Γ Δ s A σ) .proj₂ .rhseq = begin
  < susp-tm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) >tm
    ≈⟨ Coh≃ (disc-susp (ty-dim A))
            (Arr≃ refl≃tm
                  lem
                  refl≃tm)
            (susp-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)) ⟩
  < identity (suc (ty-dim A)) (sub-from-disc (suc (ty-dim A))
                                             (susp-ty (A [ σ ]ty))
                                             _
                                             (susp-tm (s [ σ ]tm))) >tm
    ≈⟨ identity-≃ (sym (susp-dim A))
                  (sub-from-disc-≃ (suc (ty-dim A))
                                   (ty-dim (susp-ty A))
                                   (susp-functorial-ty σ A)
                                   (trans (susp-dim (A [ σ ]ty)) (cong suc (sym (sub-dim σ A))))
                                   (sym (sub-dim (susp-sub σ) (susp-ty A)))
                                   (susp-functorial-tm σ s)) ⟩
  < identity (ty-dim (susp-ty A)) (sub-from-disc (ty-dim (susp-ty A))
                                                 (susp-ty A [ susp-sub σ ]ty)
                                                 (sym (sub-dim (susp-sub σ) (susp-ty A)))
                                                 (susp-tm s [ susp-sub σ ]tm)) >tm ∎
  where
    lem : susp-ty (lift-ty (sphere-type (ty-dim A)))
          ≃ty
          lift-ty (sphere-type (suc (ty-dim A)))
    lem = begin
      < susp-ty (lift-ty (sphere-type (ty-dim A))) >ty
        ≈⟨ susp-ty-lift (sphere-type (ty-dim A)) ⟩
      < lift-ty (susp-ty (sphere-type (ty-dim A))) >ty
        ≈⟨ lift-ty-≃ (sphere-type-susp (ty-dim A)) ⟩
      < lift-ty (sphere-type (suc (ty-dim A))) >ty ∎
      where
        open Reasoning ty-setoid

    open Reasoning tm-setoid

ecr-sub : SubCond EndoCoherenceRemovalSet
ecr-sub (ECR Γ Δ s A σ) Υ τ .proj₁ = ECR Υ Δ s A (τ ● σ)
ecr-sub (ECR Γ Δ s A σ) Υ τ .proj₂ .ctxeq = refl≃c
ecr-sub (ECR Γ Δ s A σ) Υ τ .proj₂ .lhseq = refl≃tm
ecr-sub (ECR Γ Δ s A σ) Υ τ .proj₂ .rhseq
  = identity-≃ refl (begin
    < τ ● sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm) >s
      ≈˘⟨ sub-from-disc-sub (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm) τ ⟩
    < sub-from-disc (ty-dim A) ((A [ σ ]ty) [ τ ]ty) _ (s [ σ ]tm [ τ ]tm) >s
      ≈˘⟨ sub-from-disc-≃ (ty-dim A)
                          (ty-dim A)
                          (assoc-ty τ σ A)
                          (sym (sub-dim (τ ● σ) A))
                          (trans (sym (sub-dim τ (A [ σ ]ty))) (sym (sub-dim σ A)))
                          (assoc-tm τ σ s) ⟩
    < sub-from-disc (ty-dim A) (A [ τ ● σ ]ty) _ (s [ τ ● σ ]tm) >s ∎)
    where
      open Reasoning sub-setoid

open Tame

ecr-tame : Tame EndoCoherenceRemovalSet
ecr-tame .lift-cond = ecr-lift
ecr-tame .susp-cond = ecr-susp
ecr-tame .sub-cond = ecr-sub
