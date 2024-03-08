module Catt.Typing.Pruning.Rule where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties
open import Catt.Typing.Rule

open Rule

Pruning : (Γ : Ctx m)
        → (dy : Dyck (suc n) 0)
        → (A : Ty (3 + n * 2))
        → (p : Peak dy)
        → (σ : Sub (3 + n * 2) m ⋆)
        → Rule
Pruning Γ dy A p σ .len = _
Pruning Γ dy A p σ .tgtCtx = Γ
Pruning Γ dy A p σ .lhs = Coh ⌊ dy ⌋d A σ
Pruning Γ dy A p σ .rhs = Coh ⌊ dy // p ⌋d (A [ π p ]ty) (σ //s p)

data PruningSet : RuleSet where
  Prune : (Γ : Ctx m)
        → (dy : Dyck (suc n) 0)
        → (A : Ty (3 + n * 2))
        → (p : Peak dy)
        → (σ : Sub (3 + n * 2) m ⋆)
        → (B : Ty m)
        → (t : Tm m)
        → (pf : peak-term p [ σ ]tm ≃tm identity-term B t)
        → PruningSet (Pruning Γ dy A p σ)

pruning-wk : WkCond PruningSet
pruning-wk C [ Prune Γ dy A p σ B t pf ]
  = ∈r-≃ [ Prune (Γ , C) dy A p (wk-sub σ) (wk-ty B) (wk-tm t) lem ] γ
  where
    lem : (peak-term p [ wk-sub σ ]tm) ≃tm identity-term (wk-ty B) (wk-tm t)
    lem = begin
      < peak-term p [ wk-sub σ ]tm >tm
        ≈⟨ apply-wk-sub-tm-≃ (peak-term p) σ ⟩
      < wk-tm (peak-term p [ σ ]tm) >tm
        ≈⟨ wk-tm-≃ pf ⟩
      < wk-tm (identity-term B t) >tm
        ≈⟨ identity-term-wk B t ⟩
      < identity-term (wk-ty B) (wk-tm t) >tm ∎
      where
        open Reasoning tm-setoid

    γ : Pruning (Γ , C) dy A p (wk-sub σ) ≃r wk-rule (Pruning Γ dy A p σ) C
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = Coh≃ refl≃c refl≃ty (wk-//s p σ)

pruning-susp : SuspCond PruningSet
pruning-susp [ Prune Γ dy A p σ B t pf ]
  = ∈r-≃ [ Prune (susp-ctx Γ)
                 (⇓ (susp-dyck dy))
                 (susp-ty A)
                 (⇓pk (susp-peak p))
                 (susp-sub σ)
                 (susp-ty B)
                 (susp-tm t)
                 lem ]
         γ
  where
    lem : (peak-term (susp-peak p) [ susp-sub σ ]tm) ≃tm identity-term (susp-ty B) (susp-tm t)
    lem = begin
      < peak-term (susp-peak p) [ susp-sub σ ]tm >tm
        ≈⟨ sub-action-≃-tm (susp-peak-term p) refl≃s ⟩
      < susp-tm (peak-term p) [ susp-sub σ ]tm >tm
        ≈˘⟨ susp-functorial-tm σ (peak-term p) ⟩
      < susp-tm (peak-term p [ σ ]tm) >tm
        ≈⟨ susp-tm-≃ pf ⟩
      < susp-tm (identity-term B t) >tm
        ≈⟨ identity-term-susp B t ⟩
      < identity-term (susp-ty B) (susp-tm t) >tm ∎
      where
        open Reasoning tm-setoid

    l1 : ⌊ susp-dyck dy // (susp-peak p) ⌋d ≃c susp-ctx ⌊ dy // p ⌋d
    l1 = begin
      < ⌊ susp-dyck dy // (susp-peak p) ⌋d >c
        ≈⟨ ⌊⌋d-≃ (prune-susp-peak p) ⟩
      < ⌊ susp-dyck (dy // p) ⌋d >c
        ≈⟨ susp-⌊⌋d (dy // p) ⟩
      < susp-ctx ⌊ dy // p ⌋d >c ∎
      where
        open Reasoning ctx-setoid

    l2 : (susp-ty A [ π (susp-peak p) ]ty) ≃ty susp-ty (A [ π p ]ty)
    l2 = begin
      < susp-ty A [ π (susp-peak p) ]ty >ty
        ≈⟨ sub-action-≃-ty refl≃ty (susp-π p) ⟩
      < susp-ty A [ susp-sub (π p) ]ty >ty
        ≈˘⟨ susp-functorial-ty (π p) A ⟩
      < susp-ty (A [ π p ]ty) >ty ∎
      where
        open Reasoning ty-setoid

    γ : Pruning (susp-ctx Γ) (⇓ (susp-dyck dy)) (susp-ty A) (⇓pk (susp-peak p)) (susp-sub σ)
        ≃r
        susp-rule (Pruning Γ dy A p σ)
    γ .ctxeq = refl≃c
    γ .lhseq = Coh≃ (susp-⌊⌋d dy) refl≃ty refl≃s
    γ .rhseq = Coh≃ l1 l2 (susp-//s p σ)


pruning-sub : {ops : Op} {rules : RuleSet} → SubCond′ ops rules PruningSet
pruning-sub Δ {σ = τ} τty [ Prune Γ dy A p σ B t pf ] = ∈r-≃ [ Prune Δ dy A p (σ ● τ) (B [ τ ]ty) (t [ τ ]tm) lem ] γ
  where
    lem : (peak-term p [ σ ● τ ]tm) ≃tm identity-term (B [ τ ]ty) (t [ τ ]tm)
    lem = begin
      < peak-term p [ σ ● τ ]tm >tm
        ≈⟨ assoc-tm σ τ (peak-term p) ⟩
      < peak-term p [ σ ]tm [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm pf refl≃s ⟩
      < identity-term B t [ τ ]tm >tm
        ≈⟨ identity-term-sub B t τ ⟩
      < identity-term (B [ τ ]ty) (t [ τ ]tm) >tm ∎
      where
        open Reasoning tm-setoid

    γ : Pruning Δ dy A p (σ ● τ) ≃r sub-rule (Pruning Γ dy A p σ) Δ τ
    γ .ctxeq = refl≃c
    γ .lhseq = refl≃tm
    γ .rhseq = Coh≃ refl≃c refl≃ty (//s-sub p σ τ)
