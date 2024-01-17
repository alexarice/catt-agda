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

dr-lift : LiftCond DiscRemovalSet
dr-lift A [ DR Γ σ ] = ∈r-≃ [ DR (Γ , A) (lift-sub σ) ] γ
  where
    γ : DiscRemoval (Γ , A) (lift-sub σ) ≃r lift-rule (DiscRemoval Γ σ) A
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = apply-lifted-sub-tm-≃ 0V σ

dr-susp : SuspCond DiscRemovalSet
dr-susp [ DR {n = n} Γ σ ] = ∈r-≃ [ DR {n = suc n} (susp-ctx Γ) (susp-sub σ) ] γ
  where
    γ : DiscRemoval (susp-ctx Γ) (susp-sub σ) ≃r susp-rule (DiscRemoval Γ σ)
    γ .ctxeq = refl≃c
    γ .lhseq = sym≃tm (disc-term-susp _ σ)
    γ .rhseq = sym≃tm (susp-functorial-tm σ 0V)

dr-sub : SubCond DiscRemovalSet
dr-sub Γ τ [ DR Δ σ ] = ∈r-≃ [ DR Γ (τ ● σ) ] γ
  where
    γ : DiscRemoval Γ (τ ● σ) ≃r sub-rule (DiscRemoval Δ σ) Γ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = assoc-tm τ σ 0V

open Tame

dr-tame : Tame DiscRemovalSet
dr-tame .lift-cond = dr-lift
dr-tame .susp-cond = dr-susp
dr-tame .sub-cond = dr-sub
