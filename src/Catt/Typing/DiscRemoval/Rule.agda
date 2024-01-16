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

data DiscRemovalIdx : Set where
  DR : .⦃ NonZero n ⦄ → (Γ : Ctx m) → (σ : Sub (disc-size n) m ⋆) → DiscRemovalIdx

DiscRemovalSet : RuleSet
DiscRemovalSet .proj₁ = DiscRemovalIdx
DiscRemovalSet .proj₂ (DR Γ σ) = DiscRemoval Γ σ

dr-lift : LiftCond DiscRemovalSet
dr-lift (DR Γ σ) A .proj₁ = (DR (Γ , A) (lift-sub σ))
dr-lift (DR Γ σ) A .proj₂ .ctxeq = refl≃c
dr-lift (DR Γ σ) A .proj₂ .lhseq = refl≃tm
dr-lift (DR Γ σ) A .proj₂ .rhseq = sym≃tm (apply-lifted-sub-tm-≃ 0V σ)

dr-susp : SuspCond DiscRemovalSet
dr-susp (DR {n = n} Γ σ) .proj₁ = DR {n = suc n} (susp-ctx Γ) (susp-sub σ)
dr-susp (DR Γ σ) .proj₂ .ctxeq = refl≃c
dr-susp (DR Γ σ) .proj₂ .lhseq = disc-term-susp _ σ
dr-susp (DR Γ σ) .proj₂ .rhseq = susp-functorial-tm σ 0V

dr-sub : SubCond DiscRemovalSet
dr-sub (DR Δ σ) Γ τ .proj₁ = DR Γ (τ ● σ)
dr-sub (DR Δ σ) Γ τ .proj₂ .ctxeq = refl≃c
dr-sub (DR Δ σ) Γ τ .proj₂ .lhseq = refl≃tm
dr-sub (DR Δ σ) Γ τ .proj₂ .rhseq = sym≃tm (assoc-tm τ σ 0V)

open Tame

dr-tame : Tame DiscRemovalSet
dr-tame .lift-cond = dr-lift
dr-tame .susp-cond = dr-susp
dr-tame .sub-cond = dr-sub
