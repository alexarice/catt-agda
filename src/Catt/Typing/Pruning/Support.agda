open import Catt.Typing.Rule

module Catt.Typing.Pruning.Support (rules : RuleSet)
                                   (lift-cond : LiftCond rules)
                                   (sub-cond : SubCond rules)
                                   (supp-cond : SupportCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Support

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Support rules supp-cond
open import Catt.Dyck.Pruning.Typing rules lift-cond sub-cond
open import Catt.Typing.Pruning.Rule

open import Catt.Support
open import Catt.Support.Properties

pruning-supp : SupportCond′ rules PruningSet
pruning-supp [ Prune Γ dy A p σ B t pf ] tty = begin
  SuppTm Γ (Coh ⌊ dy ⌋d A σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ EqSuppSub (prune-Eq p σty pf) ⟩
  SuppSub Γ (π p ● (σ //s p))
    ≡˘⟨ cong (DC Γ) (TransportVarSet-sub (π p) (σ //s p)) ⟩
  DC Γ (TransportVarSet (FVSub (π p)) (σ //s p))
    ≡⟨ cong (λ - → DC Γ (TransportVarSet - (σ //s p))) (π-full p) ⟩
  DC Γ (TransportVarSet full (σ //s p))
    ≡⟨ cong (DC Γ) (TransportVarSet-full (σ //s p)) ⟩
  SuppSub Γ (σ //s p)
    ≡⟨⟩
  SuppTm Γ (Coh ⌊ dy // p ⌋d (A [ π p ]ty) (σ //s p)) ∎
  where
    open ≡-Reasoning

    σty : Typing-Sub ⌊ dy ⌋d Γ σ
    σty = coh-sub-ty tty
