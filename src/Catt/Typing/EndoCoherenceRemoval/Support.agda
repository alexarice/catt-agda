open import Catt.Typing.Rule

module Catt.Typing.EndoCoherenceRemoval.Support (ops : Op)
                                                (standard-op : StandardOp ops)
                                                (rules : RuleSet)
                                                (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Discs.Support

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Support ops rules supp-cond
open import Catt.Globular.Typing ops rules
open import Catt.Typing.EndoCoherenceRemoval.Rule

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

ecr-supp : SupportCond′ ops rules ECRSet
ecr-supp [ ECR Γ Δ s sfull A σ ] tty = begin
  SuppTm Γ (Coh Δ (s ─⟨ A ⟩⟶ s) σ)
    ≡⟨⟩
  SuppSub Γ σ
    ≡⟨ SuppSubFV σty ⟩
  FVSub σ
    ≡˘⟨ vs-sub-full σ ⟩
  full [ σ ]vs
    ≡˘⟨ cong (_[ σ ]vs) sfull ⟩
  SuppTm Δ s [ σ ]vs
    ≡⟨ cong (_[ σ ]vs) (SuppTmChar″ (ty-src-Ty Asty) (ty-base-Ty Asty)) ⟩
  (SuppTy Δ A ∪ SuppTm Δ s) [ σ ]vs
    ≡˘⟨ cong (_[ σ ]vs) (DC-∪ Δ (FVTy A) (FVTm s)) ⟩
  (DC Δ (FVTy A ∪ FVTm s)) [ σ ]vs
    ≡˘⟨ vs-sub-DC (FVTy A ∪ FVTm s) σty ⟩
  DC Γ ((FVTy A ∪ FVTm s) [ σ ]vs)
    ≡⟨ cong (DC Γ) (vs-sub-∪ (FVTy A) (FVTm s) σ) ⟩
  DC Γ (FVTy A [ σ ]vs ∪ FVTm s [ σ ]vs)
    ≡⟨ cong₂ (λ a b → DC Γ (a ∪ b)) (vs-sub-ty A σ) (vs-sub-tm s σ) ⟩
  DC Γ (FVTy (A [ σ ]ty) ∪ FVTm (s [ σ ]tm))
    ≡˘⟨ cong (DC Γ) (sub-from-disc-fv (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)) ⟩
  SuppSub Γ (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))
    ≡⟨⟩
  SuppTm Γ (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ∎
  where
    open ≡-Reasoning

    σty : Typing-Sub Δ Γ σ
    σty = coh-sub-ty tty

    Asty : Typing-Ty Δ (s ─⟨ A ⟩⟶ s)
    Asty = coh-ty-ty tty
