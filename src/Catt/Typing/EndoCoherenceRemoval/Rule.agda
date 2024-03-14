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
      → (supp : SuppTm Δ s ≡ full)
      → (A : Ty (suc n))
      → (σ : Sub (suc n) m ⋆)
      → ECRSet (EndoCoherenceRemoval Γ Δ s A σ)

ecr-wk : WkCond ECRSet
ecr-wk B [ ECR Γ Δ s sfull A σ ] = ∈r-≃ [ ECR (Γ , B) Δ s sfull A (wk-sub σ) ] γ
  where
    γ : EndoCoherenceRemoval (Γ , B) Δ s A (wk-sub σ) ≃r wk-rule (EndoCoherenceRemoval Γ Δ s A σ) B
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = identity-≃ refl (trans≃s (sub-from-disc-≃ (ty-dim A)
                                                         (ty-dim A)
                                                         (apply-wk-sub-ty-≃ A σ)
                                                         (sym (sub-dim (wk-sub σ) A))
                                                         (trans (wk-ty-dim (A [ σ ]ty)) (sym (sub-dim σ A)))
                                                         (apply-wk-sub-tm-≃ s σ))
                                        (sym≃s (wk-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))))

ecr-susp : SuspCond ECRSet
ecr-susp [ ECR Γ Δ s sfull A σ ] = ∈r-≃ [ ECR (susp-ctx Γ) (susp-ctx Δ) (susp-tm s) supp-lem (susp-ty A) (susp-sub σ) ] γ
  where
    lem : susp-ty (wk-ty (sphere-type (ty-dim A)))
          ≃ty
          wk-ty (sphere-type (suc (ty-dim A)))
    lem = begin
      < susp-ty (wk-ty (sphere-type (ty-dim A))) >ty
        ≈⟨ susp-ty-wk (sphere-type (ty-dim A)) ⟩
      < wk-ty (susp-ty (sphere-type (ty-dim A))) >ty
        ≈⟨ wk-ty-≃ (sphere-type-susp (ty-dim A)) ⟩
      < wk-ty (sphere-type (suc (ty-dim A))) >ty ∎
      where
        open Reasoning ty-setoid

    supp-lem : SuppTm (susp-ctx Δ) (susp-tm s) ≡ full
    supp-lem = begin
      SuppTm (susp-ctx Δ) (susp-tm s)
        ≡⟨ susp-SuppTm Δ s ⟩
      susp-vs (SuppTm Δ s)
        ≡⟨ cong susp-vs sfull ⟩
      susp-vs full
        ≡⟨ susp-vs-full ⟩
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


ecr-sub : {ops : Op} {rules : RuleSet} → SubCond′ ops rules ECRSet
ecr-sub Υ {σ = τ} τty [ ECR Γ Δ s sfull A σ ] = ∈r-≃ [ ECR Υ Δ s sfull A (σ ● τ) ] γ
  where
    γ : EndoCoherenceRemoval Υ Δ s A (σ ● τ) ≃r sub-rule (EndoCoherenceRemoval Γ Δ s A σ) Υ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = identity-≃ refl (begin
      < sub-from-disc (ty-dim A) (A [ σ ● τ ]ty) _ (s [ σ ● τ ]tm) >s
        ≈⟨ sub-from-disc-≃ (ty-dim A)
                              (ty-dim A)
                              (assoc-ty σ τ A)
                              (sym (sub-dim (σ ● τ) A))
                              (trans (sym (sub-dim τ (A [ σ ]ty))) (sym (sub-dim σ A)))
                              (assoc-tm σ τ s) ⟩
      < sub-from-disc (ty-dim A) ((A [ σ ]ty) [ τ ]ty) _ (s [ σ ]tm [ τ ]tm) >s
        ≈⟨ sub-from-disc-sub (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm) τ ⟩
      < sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm) ● τ >s ∎)
      where
        open Reasoning sub-setoid
