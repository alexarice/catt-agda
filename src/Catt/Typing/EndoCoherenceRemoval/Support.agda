open import Catt.Typing.Rule

module Catt.Typing.EndoCoherenceRemoval.Support (rules : RuleSet)
                                                (supp-cond : SupportCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Discs.Support

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Support rules supp-cond
open import Catt.Typing.EndoCoherenceRemoval.Rule

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

ecr-supp : SupportCond′ rules ECRSet
ecr-supp [ ECR Γ Δ s A supp σ ] tty = begin
  SuppTm Γ (Coh Δ (s ─⟨ A ⟩⟶ s) σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ SuppSubFV σty ⟩
  FVSub σ
    ≡˘⟨ TransportVarSet-full σ ⟩
  TransportVarSet full σ
    ≡˘⟨ cong (λ - → TransportVarSet - σ) supp ⟩
  TransportVarSet (SuppTy Δ (s ─⟨ A ⟩⟶ s)) σ
    ≡⟨ cong (λ - → TransportVarSet (DC Δ -) σ) (prove 2 ((var 0F ⊕ var 1F) ⊕ var 1F) (var 0F ⊕ var 1F) (FVTy A ∷ FVTm s ∷ emp)) ⟩
  TransportVarSet (DC Δ (FVTy A ∪ FVTm s)) σ
    ≡˘⟨ TransportVarSet-DC (FVTy A ∪ FVTm s) σty ⟩
  DC Γ (TransportVarSet (FVTy A ∪ FVTm s) σ)
    ≡⟨ cong (DC Γ) (TransportVarSet-∪ (FVTy A) (FVTm s) σ) ⟩
  DC Γ (TransportVarSet (FVTy A) σ ∪ TransportVarSet (FVTm s) σ)
    ≡⟨ cong₂ (λ a b → DC Γ (a ∪ b)) (TransportVarSet-ty A σ) (TransportVarSet-tm s σ) ⟩
  DC Γ (FVTy (A [ σ ]ty) ∪ FVTm (s [ σ ]tm))
    ≡˘⟨ cong (DC Γ) (sub-from-disc-supp (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)) ⟩
  SuppSub Γ (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))
    ≡⟨⟩
  SuppTm Γ (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ∎
  where
    open ≡-Reasoning
    open Solver ∪-idempotentCommutativeMonoid

    σty : Typing-Sub Δ Γ σ
    σty = coh-sub-ty tty
