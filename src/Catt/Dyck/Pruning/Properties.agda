module Catt.Dyck.Pruning.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning

dyck-type-prune : (p : Peak dy) → dyck-type (dy // p) ≃ty dyck-type dy [ π p ]ty
dyck-term-prune : (p : Peak dy) → dyck-term (dy // p) ≃tm dyck-term dy [ π p ]tm

dyck-type-prune (⇕pk dy) = begin
  < dyck-type dy >ty
    ≈˘⟨ id-on-ty (dyck-type dy) ⟩
  < dyck-type dy [ idSub ]ty >ty
    ≈˘⟨ apply-sub-lifted-ty-≃ (dyck-type dy) ⟨ idSub , dyck-term dy ⟩ ⟩
  < lift-ty (dyck-type dy) [ ⟨ idSub , dyck-term dy ⟩ ]ty >ty
    ≈˘⟨ apply-sub-lifted-ty-≃ (lift-ty (dyck-type dy)) (π (⇕pk dy)) ⟩
  < dyck-type (⇓ (⇑ dy)) [ π (⇕pk dy) ]ty >ty ∎
  where
    open Reasoning ty-setoid
dyck-type-prune (⇑pk {dy = dy} p) = Arr≃ l1 l2 refl≃tm
  where
    l1 : lift-tm (lift-tm (dyck-term (dy // p))) ≃tm
           (lift-tm (lift-tm (dyck-term dy)) [ π (⇑pk p) ]tm)
    l1 = begin
      < lift-tm (lift-tm (dyck-term (dy // p))) >tm
        ≈⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-prune p)) ⟩
      < lift-tm (lift-tm (dyck-term dy [ π p ]tm)) >tm
        ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term dy) (π p)) ⟩
      < lift-tm (dyck-term dy [ lift-sub (π p) ]tm) >tm
        ≈˘⟨ apply-lifted-sub-tm-≃ (dyck-term dy) (lift-sub (π p)) ⟩
      < dyck-term dy [ lift-sub (lift-sub (π p)) ]tm >tm
        ≈˘⟨ apply-sub-lifted-tm-≃ (dyck-term dy) ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ ⟩
      < lift-tm (dyck-term dy) [ ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ ]tm >tm
        ≈˘⟨ apply-sub-lifted-tm-≃  (lift-tm (dyck-term dy)) ⟨ ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ , 0V ⟩ ⟩
      < lift-tm (lift-tm (dyck-term dy)) [ ⟨ ⟨ (lift-sub (lift-sub (π p))) , 1V ⟩ , 0V ⟩ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : lift-ty (lift-ty (dyck-type (dy // p))) ≃ty
           (lift-ty (lift-ty (dyck-type dy)) [ π (⇑pk p) ]ty)
    l2 = begin
      < lift-ty (lift-ty (dyck-type (dy // p))) >ty
        ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-prune p)) ⟩
      < lift-ty (lift-ty (dyck-type dy [ π p ]ty)) >ty
        ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type dy) (π p)) ⟩
      < lift-ty (dyck-type dy [ lift-sub (π p) ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type dy) (lift-sub (π p)) ⟩
      < dyck-type dy [ lift-sub (lift-sub (π p)) ]ty >ty
        ≈˘⟨ apply-sub-lifted-ty-≃ (dyck-type dy) ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ ⟩
      < lift-ty (dyck-type dy) [ ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ ]ty >ty
        ≈˘⟨ apply-sub-lifted-ty-≃ (lift-ty (dyck-type dy)) ⟨ ⟨ lift-sub (lift-sub (π p)) , 1V ⟩ , 0V ⟩ ⟩
      < lift-ty (lift-ty (dyck-type dy)) [ ⟨ ⟨ (lift-sub (lift-sub (π p))) , 1V ⟩ , 0V ⟩ ]ty >ty ∎
      where
        open Reasoning ty-setoid
dyck-type-prune (⇓pk {dy = dy} p) = begin
  < dyck-type (⇓ dy // (⇓pk p)) >ty
    ≈˘⟨ ty-base-lift (dyck-pre-type (dy // p)) ⟩
  < ty-base (dyck-type (dy // p)) >ty
    ≈⟨ ty-base-≃ (dyck-type-prune p) ⟩
  < ty-base (dyck-type dy [ π p ]ty) >ty
    ≈˘⟨ ty-base-sub (dyck-type dy) (π p) ⟩
  < ty-base (dyck-type dy) [ π p ]ty >ty
    ≈⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type dy)) refl≃s ⟩
  < dyck-type (⇓ dy) [ π (⇓pk p) ]ty >ty ∎
  where
    open Reasoning ty-setoid

dyck-term-prune (⇕pk dy) = refl≃tm
dyck-term-prune (⇑pk p) = refl≃tm
dyck-term-prune (⇓pk {dy = dy} p) = begin
  < ty-tgt′ (dyck-type (dy // p)) >tm
    ≈⟨ ty-tgt′-≃ (dyck-type-prune p) ⟩
  < ty-tgt′ (dyck-type dy [ π p ]ty) >tm
    ≈˘⟨ ty-tgt′-sub (dyck-type dy) (π p) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄ ⟩
  < dyck-term (⇓ dy) [ π (⇓pk p) ]tm >tm ∎
  where
    open Reasoning tm-setoid

lift-//s : (p : Peak dy) → (σ : Sub _ n ⋆) → lift-sub σ //s p ≃s lift-sub (σ //s p)
lift-//s (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = refl≃s
lift-//s (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (lift-//s p σ) refl≃tm) refl≃tm
lift-//s (⇓pk p) σ = lift-//s p σ

prune-susp-peak : (p : Peak dy) → susp-dyck dy // (susp-peak p) ≃d susp-dyck (dy // p)
prune-susp-peak (⇕pk dy) = refl≃d
prune-susp-peak (⇑pk p) = ⇑≃ (prune-susp-peak p)
prune-susp-peak (⇓pk p) = ⇓≃ (prune-susp-peak p)

susp-π : (p : Peak dy) → π (susp-peak p) ≃s susp-sub (π p)
susp-π (⇕pk dy) = Ext≃ (Ext≃ (sym≃s susp-functorial-id) (susp-dyck-term dy)) (begin
  < identity-term (dyck-type (susp-dyck dy)) (dyck-term (susp-dyck dy)) >tm
    ≈⟨ identity-term-≃ (susp-dyck-type dy) (susp-dyck-term dy) ⟩
  < identity-term (susp-ty (dyck-type dy)) (susp-tm (dyck-term dy)) >tm
    ≈˘⟨ identity-term-susp (dyck-type dy) (dyck-term dy) ⟩
  < susp-tm (identity-term (dyck-type dy) (dyck-term dy)) >tm ∎)
  where
    open Reasoning tm-setoid
susp-π (⇑pk p)
  = Ext≃ (Ext≃ lem
               refl≃tm)
         refl≃tm
  where
    lem : lift-sub (lift-sub (π (susp-peak p))) ≃s
           unrestrict (susp-sub-res (lift-sub (lift-sub (π p))))
    lem = begin
      < lift-sub (lift-sub (π (susp-peak p))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ (susp-π p)) ⟩
      < lift-sub (lift-sub (susp-sub (π p))) >s
        ≈˘⟨ lift-sub-≃ (susp-sub-lift (π p)) ⟩
      < lift-sub (susp-sub (lift-sub (π p))) >s
        ≈˘⟨ susp-sub-lift (lift-sub (π p)) ⟩
      < susp-sub (lift-sub (lift-sub (π p))) >s ∎
      where
        open Reasoning sub-setoid
susp-π (⇓pk p) = susp-π p

susp-//s : {dy : Dyck (suc n) d} → (p : Peak dy) → (σ : Sub (3 + n * 2) m ⋆) → susp-sub σ //s susp-peak p ≃s susp-sub (σ //s p)
susp-//s (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = refl≃s
susp-//s (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (susp-//s p σ) refl≃tm) refl≃tm
susp-//s (⇓pk p) σ = susp-//s p σ

//s-sub : {dy : Dyck (suc n) d} → (p : Peak dy) → (σ : Sub (3 + n * 2) m ⋆) → (τ : Sub m l ⋆) → τ ● σ //s p ≃s τ ● (σ //s p)
//s-sub (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ τ = refl≃s
//s-sub (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ τ = Ext≃ (Ext≃ (//s-sub p σ τ) refl≃tm) refl≃tm
//s-sub (⇓pk p) σ τ = //s-sub p σ τ
