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

data PruningIdx : Set where
  Prune : (Γ : Ctx m)
        → (dy : Dyck (suc n) 0)
        → (A : Ty (3 + n * 2))
        → (p : Peak dy)
        → (σ : Sub (3 + n * 2) m ⋆)
        → (B : Ty m)
        → (t : Tm m)
        → (peak-term p [ σ ]tm ≃tm identity-term B t)
        → PruningIdx

PruningSet : RuleSet
PruningSet .proj₁ = PruningIdx
PruningSet .proj₂ (Prune Γ dy A p σ B t pf) = Pruning Γ dy A p σ

pruning-lift : LiftCond PruningSet
pruning-lift (Prune Γ dy A p σ B t pf) C .proj₁
  = Prune (Γ , C) dy A p (lift-sub σ) (lift-ty B) (lift-tm t) lem
  where
    lem : (peak-term p [ lift-sub σ ]tm) ≃tm identity-term (lift-ty B) (lift-tm t)
    lem = begin
      < peak-term p [ lift-sub σ ]tm >tm
        ≈⟨ apply-lifted-sub-tm-≃ (peak-term p) σ ⟩
      < lift-tm (peak-term p [ σ ]tm) >tm
        ≈⟨ lift-tm-≃ pf ⟩
      < lift-tm (identity-term B t) >tm
        ≈⟨ identity-term-lift B t ⟩
      < identity-term (lift-ty B) (lift-tm t) >tm ∎
      where
        open Reasoning tm-setoid
pruning-lift (Prune Γ dy A p σ B t x) C .proj₂ .ctxeq = refl≃c
pruning-lift (Prune Γ dy A p σ B t x) C .proj₂ .lhseq = refl≃tm
pruning-lift (Prune Γ dy A p σ B t x) C .proj₂ .rhseq
  = sym≃tm (Coh≃ refl≃c refl≃ty (lift-//s p σ))

pruning-susp : SuspCond PruningSet
pruning-susp (Prune Γ dy A p σ B t pf) .proj₁
  = Prune (susp-ctx Γ)
          (⇓ (susp-dyck dy))
          (susp-ty A)
          (⇓pk (susp-peak p))
          (susp-sub σ)
          (susp-ty B)
          (susp-tm t)
          lem
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
pruning-susp (Prune Γ dy A p σ B t pf) .proj₂ .ctxeq = refl≃c
pruning-susp (Prune Γ dy A p σ B t pf) .proj₂ .lhseq = Coh≃ (sym≃c (susp-⌊⌋d dy)) refl≃ty refl≃s
pruning-susp (Prune Γ dy A p σ B t pf) .proj₂ .rhseq
  = sym≃tm (Coh≃ l1 l2 (susp-//s p σ))
  where
    l1 : ⌊ susp-dyck dy // (susp-peak p) ⌋d ≃c
          susp-ctx ⌊ dy // p ⌋d
    l1 = begin
      < ⌊ susp-dyck dy // (susp-peak p) ⌋d >c
        ≈⟨ ⌊⌋d-≃ (prune-susp-peak p) ⟩
      < ⌊ susp-dyck (dy // p) ⌋d >c
        ≈⟨ susp-⌊⌋d (dy // p) ⟩
      < susp-ctx ⌊ dy // p ⌋d >c ∎
      where
        open Reasoning ctx-setoid

    l2 : (susp-ty A [ π (susp-peak p) ]ty) ≃ty
          susp-ty (A [ π p ]ty)
    l2 = begin
      < susp-ty A [ π (susp-peak p) ]ty >ty
        ≈⟨ sub-action-≃-ty refl≃ty (susp-π p) ⟩
      < susp-ty A [ susp-sub (π p) ]ty >ty
        ≈˘⟨ susp-functorial-ty (π p) A ⟩
      < susp-ty (A [ π p ]ty) >ty ∎
      where
        open Reasoning ty-setoid

pruning-sub : SubCond PruningSet
pruning-sub (Prune Γ dy A p σ B t pf) Δ τ .proj₁ = Prune Δ dy A p (τ ● σ) (B [ τ ]ty) (t [ τ ]tm) lem
  where
    lem : (peak-term p [ τ ● σ ]tm) ≃tm identity-term (B [ τ ]ty) (t [ τ ]tm)
    lem = begin
      < peak-term p [ τ ● σ ]tm >tm
        ≈⟨ assoc-tm τ σ (peak-term p) ⟩
      < peak-term p [ σ ]tm [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm pf refl≃s ⟩
      < identity-term B t [ τ ]tm >tm
        ≈⟨ identity-term-sub B t τ ⟩
      < identity-term (B [ τ ]ty) (t [ τ ]tm) >tm ∎
      where
        open Reasoning tm-setoid
pruning-sub (Prune Γ dy A p σ B t pf) Δ τ .proj₂ .ctxeq = refl≃c
pruning-sub (Prune Γ dy A p σ B t pf) Δ τ .proj₂ .lhseq = refl≃tm
pruning-sub (Prune Γ dy A p σ B t pf) Δ τ .proj₂ .rhseq = Coh≃ refl≃c refl≃ty (sym≃s (//s-sub p σ τ))

open Tame

pruning-tame : Tame PruningSet
pruning-tame .lift-cond = pruning-lift
pruning-tame .susp-cond = pruning-susp
pruning-tame .sub-cond = pruning-sub
