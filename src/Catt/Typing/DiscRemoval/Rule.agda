open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Rule where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Typing.Rule

open Rule

DiscRemoval : (Γ : Ctx m)
            → (σ : Sub (disc-size n) m ⋆) → Rule
DiscRemoval Γ σ .len = _
DiscRemoval Γ σ .tgtCtx = Γ
DiscRemoval Γ σ .lhs = disc-term _ σ
DiscRemoval Γ σ .rhs = 0V [ σ ]tm

data DiscRemovalSet : RuleSet where
  DR : .⦃ NonZero n ⦄ → (Γ : Ctx m) → (σ : Sub (disc-size n) m ⋆) → DiscRemovalSet (DiscRemoval Γ σ)

dr-wk : WkCond DiscRemovalSet
dr-wk A [ DR Γ σ ] = ∈r-≃ [ DR (Γ , A) (wk-sub σ) ] γ
  where
    γ : DiscRemoval (Γ , A) (wk-sub σ) ≃r wk-rule (DiscRemoval Γ σ) A
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = apply-wk-sub-tm-≃ 0V σ

dr-susp : SuspCond DiscRemovalSet
dr-susp [ DR {n = n} Γ σ ] = ∈r-≃ [ DR {n = suc n} (susp-ctx Γ) (susp-sub σ) ] γ
  where
    γ : DiscRemoval (susp-ctx Γ) (susp-sub σ) ≃r susp-rule (DiscRemoval Γ σ)
    γ .ctxeq = refl≃c
    γ .lhseq = sym≃tm (disc-term-susp _ σ)
    γ .rhseq = sym≃tm (susp-functorial-tm σ 0V)

dr-sub : {ops : Op} {rules : RuleSet} → SubCond′ ops rules DiscRemovalSet
dr-sub Γ {σ = τ} τty [ DR Δ σ ] = ∈r-≃ [ DR Γ (σ ● τ) ] γ
  where
    γ : DiscRemoval Γ (σ ● τ) ≃r sub-rule (DiscRemoval Δ σ) Γ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = assoc-tm σ τ 0V
