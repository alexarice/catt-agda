module Catt.Typing.EndoCoherenceRemoval.Rule where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Support
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

data ECRSet : RuleSet where
  ECR : (Γ : Ctx m)
      → (Δ : Ctx (suc n))
      → (s : Tm (suc n))
      → (A : Ty (suc n))
      → (SuppTy Δ (s ─⟨ A ⟩⟶ s) ≡ full)
      → (σ : Sub (suc n) m ⋆)
      → ECRSet (EndoCoherenceRemoval Γ Δ s A σ)

ecr-lift : LiftCond ECRSet
ecr-lift B [ ECR Γ Δ s A supp σ ] = ∈r-≃ [ ECR (Γ , B) Δ s A supp (lift-sub σ) ] γ
  where
    γ : EndoCoherenceRemoval (Γ , B) Δ s A (lift-sub σ) ≃r lift-rule (EndoCoherenceRemoval Γ Δ s A σ) B
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = identity-≃ refl (trans≃s (sub-from-disc-≃ (ty-dim A)
                                                         (ty-dim A)
                                                         (apply-lifted-sub-ty-≃ A σ)
                                                         (sym (sub-dim (lift-sub σ) A))
                                                         (trans (lift-ty-dim (A [ σ ]ty)) (sym (sub-dim σ A)))
                                                         (apply-lifted-sub-tm-≃ s σ))
                                        (sym≃s (lift-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))))

ecr-susp : SuspCond ECRSet
ecr-susp [ ECR Γ Δ s A supp σ ] = ∈r-≃ [ ECR (susp-ctx Γ) (susp-ctx Δ) (susp-tm s) (susp-ty A) supp-lem (susp-sub σ) ] γ
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

    supp-lem : SuppTy (susp-ctx Δ) (susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm s) ≡ full
    supp-lem = begin
      SuppTy (susp-ctx Δ) (susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm s)
        ≡⟨ cong (DC (susp-ctx Δ)) (suspSuppTy (s ─⟨ A ⟩⟶ s)) ⟩
      DC (susp-ctx Δ) (suspSupp (FVTy (s ─⟨ A ⟩⟶ s)))
        ≡⟨ DC-suspSupp Δ (FVTy (s ─⟨ A ⟩⟶ s)) ⟩
      suspSupp (SuppTy Δ (s ─⟨ A ⟩⟶ s))
        ≡⟨ cong suspSupp supp ⟩
      suspSupp full
        ≡⟨ suspSuppFull ⟩
      full ∎
      where
        open ≡-Reasoning

    open Reasoning tm-setoid

    γ : EndoCoherenceRemoval (susp-ctx Γ) (susp-ctx Δ) (susp-tm s) (susp-ty A) (susp-sub σ)
        ≃r
        susp-rule (EndoCoherenceRemoval Γ Δ s A σ)
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = begin
      < identity (ty-dim (susp-ty A)) (sub-from-disc (ty-dim (susp-ty A))
                                                     (susp-ty A [ susp-sub σ ]ty)
                                                     (sym (sub-dim (susp-sub σ) (susp-ty A)))
                                                     (susp-tm s [ susp-sub σ ]tm)) >tm
        ≈˘⟨ identity-≃ (sym (susp-dim A))
                       (sub-from-disc-≃ (suc (ty-dim A))
                                        (ty-dim (susp-ty A))
                                        (susp-functorial-ty σ A)
                                        (trans (susp-dim (A [ σ ]ty)) (cong suc (sym (sub-dim σ A))))
                                        (sym (sub-dim (susp-sub σ) (susp-ty A)))
                                        (susp-functorial-tm σ s)) ⟩
      < identity (suc (ty-dim A)) (sub-from-disc (suc (ty-dim A))
                                                 (susp-ty (A [ σ ]ty))
                                                 _
                                                 (susp-tm (s [ σ ]tm))) >tm
        ≈˘⟨ Coh≃ (disc-susp (ty-dim A))
                 (Arr≃ refl≃tm
                       lem
                       refl≃tm)
                 (susp-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)) ⟩
      < susp-tm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) >tm ∎


ecr-sub : {rules : RuleSet} → SubCond′ rules ECRSet
ecr-sub Υ {σ = τ} τty [ ECR Γ Δ s A supp σ ] = ∈r-≃ [ ECR Υ Δ s A supp (τ ● σ) ] γ
  where
    γ : EndoCoherenceRemoval Υ Δ s A (τ ● σ) ≃r sub-rule (EndoCoherenceRemoval Γ Δ s A σ) Υ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = identity-≃ refl (begin
      < sub-from-disc (ty-dim A) (A [ τ ● σ ]ty) _ (s [ τ ● σ ]tm) >s
        ≈⟨ sub-from-disc-≃ (ty-dim A)
                              (ty-dim A)
                              (assoc-ty τ σ A)
                              (sym (sub-dim (τ ● σ) A))
                              (trans (sym (sub-dim τ (A [ σ ]ty))) (sym (sub-dim σ A)))
                              (assoc-tm τ σ s) ⟩
      < sub-from-disc (ty-dim A) ((A [ σ ]ty) [ τ ]ty) _ (s [ σ ]tm [ τ ]tm) >s
        ≈⟨ sub-from-disc-sub (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm) τ ⟩
      < τ ● sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm) >s ∎)
      where
        open Reasoning sub-setoid
