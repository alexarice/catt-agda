open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Support (ops : Op)
                                       (standard-op : StandardOp ops)
                                       (rules : RuleSet)
                                       (wk-cond : WkCond rules)
                                       (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Discs.Properties

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Discs.Support
open import Catt.Typing.Properties.Support ops rules supp-cond

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond
open import Catt.Typing.DiscRemoval.Rule

open import Catt.Typing.Weak ops
open import Catt.Discs.Typing.Base ops Weak-Rules weak-wk as W

dr-supp : SupportCond′ ops rules DiscRemovalSet
dr-supp [ DR {n = n} Γ σ ] tty = begin
  SuppTm Γ (disc-term n σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ cong (DC Γ) (FVSub-≃ (prop-sub-from-disc n σ)) ⟩
  SuppSub Γ (sub-from-disc n (wk-ty (sphere-type n) [ σ ]ty) _ (0V [ σ ]tm))
    ≡⟨ cong (DC Γ) (sub-from-disc-supp n (wk-ty (sphere-type n) [ σ ]ty) _ (0V [ σ ]tm)) ⟩
  DC Γ (FVTy (wk-ty (sphere-type n) [ σ ]ty) ∪ FVTm (0V [ σ ]tm))
    ≡⟨ DC-∪ Γ (FVTy (wk-ty (sphere-type n) [ σ ]ty)) (FVTm (0V [ σ ]tm)) ⟩
  SuppTy Γ (wk-ty (sphere-type n) [ σ ]ty) ∪ SuppTm Γ (0V [ σ ]tm)
    ≡⟨ cong (λ - → DC Γ - ∪ SuppTm Γ (0V [ σ ]tm)) (FVTy-≃ (apply-sub-wk-ty-≃ (sphere-type n) σ)) ⟩
  SuppTy Γ (sphere-type n [ sub-proj₁ σ ]ty) ∪ SuppTm Γ (sub-proj₂ σ)
    ≡˘⟨ SuppTmChar″ (sub-proj₂-Ty σty) (apply-sub-weak-ty-typing (W.sphere-type-Ty n) (sub-proj₁-Ty σty)) ⟩
  SuppTm Γ (0V [ σ ]tm) ∎
  where
    open ≡-Reasoning

    σty : Typing-Sub (Disc n) Γ σ
    σty = coh-sub-ty tty
