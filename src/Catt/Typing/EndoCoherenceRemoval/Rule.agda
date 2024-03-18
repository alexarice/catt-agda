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
EndoCoherenceRemoval Γ Δ s A σ .rhs = identity-term (A [ σ ]ty) (s [ σ ]tm)

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
    γ .rhseq = begin
      < identity-term (A [ wk-sub σ ]ty) (s [ wk-sub σ ]tm) >tm
        ≈⟨ identity-term-≃ (apply-wk-sub-ty-≃ A σ) (apply-wk-sub-tm-≃ s σ) ⟩
      < identity-term (wk-ty (A [ σ ]ty)) (wk-tm (s [ σ ]tm)) >tm
        ≈˘⟨ identity-term-wk (A [ σ ]ty) (s [ σ ]tm) ⟩
      < wk-tm (identity-term (A [ σ ]ty) (s [ σ ]tm)) >tm ∎
      where
        open Reasoning tm-setoid

ecr-susp : SuspCond ECRSet
ecr-susp [ ECR Γ Δ s sfull A σ ] = ∈r-≃ [ ECR (susp-ctx Γ) (susp-ctx Δ) (susp-tm s) supp-lem (susp-ty A) (susp-sub σ) ] γ
  where
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
      < identity-term (susp-ty A [ susp-sub σ ]ty) (susp-tm s [ susp-sub σ ]tm) >tm
        ≈˘⟨ identity-term-≃ (susp-functorial-ty σ A) (susp-functorial-tm σ s) ⟩
      < identity-term (susp-ty (A [ σ ]ty)) (susp-tm (s [ σ ]tm)) >tm
        ≈˘⟨ identity-term-susp (A [ σ ]ty) (s [ σ ]tm) ⟩
      < susp-tm (identity-term (A [ σ ]ty) (s [ σ ]tm)) >tm ∎

ecr-sub : {ops : Op} {rules : RuleSet} → SubCond′ ops rules ECRSet
ecr-sub Υ {σ = τ} τty [ ECR Γ Δ s sfull A σ ] = ∈r-≃ [ ECR Υ Δ s sfull A (σ ● τ) ] γ
  where
    γ : EndoCoherenceRemoval Υ Δ s A (σ ● τ) ≃r sub-rule (EndoCoherenceRemoval Γ Δ s A σ) Υ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = begin
      < identity-term (A [ σ ● τ ]ty) (s [ σ ● τ ]tm) >tm
        ≈⟨ identity-term-≃ (assoc-ty σ τ A) (assoc-tm σ τ s) ⟩
      < identity-term ((A [ σ ]ty) [ τ ]ty) ((s [ σ ]tm) [ τ ]tm) >tm
        ≈˘⟨ identity-term-sub (A [ σ ]ty) (s [ σ ]tm) τ ⟩
      < identity-term (A [ σ ]ty) (s [ σ ]tm) [ τ ]tm >tm ∎
      where
        open Reasoning tm-setoid
