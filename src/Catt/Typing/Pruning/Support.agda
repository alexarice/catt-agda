open import Catt.Typing.Rule

module Catt.Typing.Pruning.Support (ops : Op)
                                   (standard-op : StandardOp ops)
                                   (rules : RuleSet)
                                   (wk-cond : WkCond rules)
                                   (sub-cond : SubCond ops rules)
                                   (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Support

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Support ops rules supp-cond
open import Catt.Dyck.Pruning.Typing ops standard-op rules wk-cond sub-cond
open import Catt.Typing.Pruning.Rule

open import Catt.Support
open import Catt.Support.Properties

pruning-supp : SupportCond′ ops rules PruningSet
pruning-supp [ Prune Γ dy A p σ B t pf ] tty = begin
  SuppTm Γ (Coh ⌊ dy ⌋d A σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ EqSuppSub (prune-Eq p σty pf) ⟩
  SuppSub Γ (π p ● (σ //s p))
    ≡˘⟨ cong (DC Γ) (vs-sub-sub (π p) (σ //s p)) ⟩
  DC Γ (FVSub (π p) [ σ //s p ]vs)
    ≡⟨ cong (λ - → DC Γ (- [ σ //s p ]vs)) (π-full p) ⟩
  DC Γ (full [ σ //s p ]vs)
    ≡⟨ cong (DC Γ) (vs-sub-full (σ //s p)) ⟩
  SuppSub Γ (σ //s p)
    ≡⟨⟩
  SuppTm Γ (Coh ⌊ dy // p ⌋d (A [ π p ]ty) (σ //s p)) ∎
  where
    open ≡-Reasoning

    σty : Typing-Sub ⌊ dy ⌋d Γ σ
    σty = coh-sub-ty tty
