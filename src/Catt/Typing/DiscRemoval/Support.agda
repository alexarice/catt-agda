open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Support (ops : Op)
                                       (standard-op : StandardOp ops)
                                       (rules : RuleSet)
                                       (wk-cond : WkCond rules)
                                       (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
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

dr-supp : SupportCond′ ops rules DiscRemovalSet
dr-supp [ DR {n = n} Γ σ ] tty = begin
  SuppTm Γ (disc-term n σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ cong (DC Γ) (FVSub-≃ (prop-sub-from-disc σ)) ⟩
  DC Γ (FVSub (sub-from-disc n (sub-from-disc-type σ) _ (sub-from-disc-term σ)))
    ≡⟨ cong (DC Γ) (sub-from-disc-supp n (sub-from-disc-type σ) (sub-from-disc-type-dim σ) (sub-from-disc-term σ)) ⟩
  DC Γ (FVTy (sub-from-disc-type σ) ∪ FVTm (sub-from-disc-term σ))
    ≡⟨ DC-∪ Γ (FVTy (sub-from-disc-type σ)) (FVTm (sub-from-disc-term σ)) ⟩
  SuppTy Γ (sub-from-disc-type σ) ∪ SuppTm Γ (sub-from-disc-term σ)
    ≡˘⟨ SuppTmChar″ (sub-from-disc-term-Ty σty) (sub-from-disc-type-Ty σty) ⟩
  SuppTm Γ (sub-from-disc-term σ) ∎
  where
    open ≡-Reasoning

    σty : Typing-Sub (Disc n) Γ σ
    σty = coh-sub-ty tty
