module Catt.Dyck.Pruning.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning

dyck-type-prune : (p : Peak dy) → dyck-type (prune-peak p) ≃ty dyck-type dy [ prune-project p ]ty
dyck-term-prune : (p : Peak dy) → dyck-term (prune-peak p) ≃tm dyck-term dy [ prune-project p ]tm

dyck-type-prune (⇕pk dy) = begin
  < dyck-type dy >ty
    ≈˘⟨ id-on-ty (dyck-type dy) ⟩
  < dyck-type dy [ idSub ]ty >ty
    ≈˘⟨ lift-sub-comp-lem-ty idSub (dyck-type dy) ⟩
  < lift-ty (dyck-type dy) [ ⟨ idSub , dyck-term dy ⟩ ]ty >ty
    ≈˘⟨ lift-sub-comp-lem-ty ⟨ idSub , dyck-term dy ⟩ (lift-ty (dyck-type dy)) ⟩
  < dyck-type (⇓ (⇑ dy)) [ prune-project (⇕pk dy) ]ty >ty ∎
  where
    open Reasoning ty-setoid
dyck-type-prune (⇑pk {dy = dy} p) = Arr≃ l1 l2 refl≃tm
  where
    l1 : lift-tm (lift-tm (dyck-term (prune-peak p))) ≃tm
           (lift-tm (lift-tm (dyck-term dy)) [ prune-project (⇑pk p) ]tm)
    l1 = begin
      < lift-tm (lift-tm (dyck-term (prune-peak p))) >tm
        ≈⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-prune p)) ⟩
      < lift-tm (lift-tm (dyck-term dy [ prune-project p ]tm)) >tm
        ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term dy) (prune-project p)) ⟩
      < lift-tm (dyck-term dy [ lift-sub (prune-project p) ]tm) >tm
        ≈˘⟨ apply-lifted-sub-tm-≃ (dyck-term dy) (lift-sub (prune-project p)) ⟩
      < dyck-term dy [ lift-sub (lift-sub (prune-project p)) ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm (lift-sub (lift-sub (prune-project p))) (dyck-term dy) ⟩
      < lift-tm (dyck-term dy) [ ⟨ lift-sub (lift-sub (prune-project p)) , 1V ⟩ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm ⟨ lift-sub (lift-sub (prune-project p)) , 1V ⟩ (lift-tm (dyck-term dy)) ⟩
      < lift-tm (lift-tm (dyck-term dy)) [ ⟨ ⟨ (lift-sub (lift-sub (prune-project p))) , 1V ⟩ , 0V ⟩ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : lift-ty (lift-ty (dyck-type (prune-peak p))) ≃ty
           (lift-ty (lift-ty (dyck-type dy)) [ prune-project (⇑pk p) ]ty)
    l2 = begin
      < lift-ty (lift-ty (dyck-type (prune-peak p))) >ty
        ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-prune p)) ⟩
      < lift-ty (lift-ty (dyck-type dy [ prune-project p ]ty)) >ty
        ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type dy) (prune-project p)) ⟩
      < lift-ty (dyck-type dy [ lift-sub (prune-project p) ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type dy) (lift-sub (prune-project p)) ⟩
      < dyck-type dy [ lift-sub (lift-sub (prune-project p)) ]ty >ty
        ≈˘⟨ lift-sub-comp-lem-ty (lift-sub (lift-sub (prune-project p))) (dyck-type dy) ⟩
      < lift-ty (dyck-type dy) [ ⟨ lift-sub (lift-sub (prune-project p)) , 1V ⟩ ]ty >ty
        ≈˘⟨ lift-sub-comp-lem-ty ⟨ lift-sub (lift-sub (prune-project p)) , 1V ⟩ (lift-ty (dyck-type dy)) ⟩
      < lift-ty (lift-ty (dyck-type dy)) [ ⟨ ⟨ (lift-sub (lift-sub (prune-project p))) , 1V ⟩ , 0V ⟩ ]ty >ty ∎
      where
        open Reasoning ty-setoid
dyck-type-prune (⇓pk {dy = dy} p) = begin
  < dyck-type (prune-peak (⇓pk p)) >ty
    ≈˘⟨ ty-base-lift (dyck-pre-type (prune-peak p)) ⟩
  < ty-base (dyck-type (prune-peak p)) >ty
    ≈⟨ ty-base-≃ (dyck-type-prune p) ⟩
  < ty-base (dyck-type dy [ prune-project p ]ty) >ty
    ≈˘⟨ ty-base-sub (dyck-type dy) (prune-project p) ⟩
  < ty-base (dyck-type dy) [ prune-project p ]ty >ty
    ≈⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type dy)) refl≃s ⟩
  < dyck-type (⇓ dy) [ prune-project (⇓pk p) ]ty >ty ∎
  where
    open Reasoning ty-setoid

dyck-term-prune (⇕pk dy) = refl≃tm
dyck-term-prune (⇑pk p) = refl≃tm
dyck-term-prune (⇓pk {dy = dy} p) = begin
  < ty-tgt′ (dyck-type (prune-peak p)) >tm
    ≈⟨ ty-tgt′-≃ (dyck-type-prune p) ⟩
  < ty-tgt′ (dyck-type dy [ prune-project p ]ty) >tm
    ≈˘⟨ ty-tgt′-sub (dyck-type dy) (prune-project p) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄ ⟩
  < dyck-term (⇓ dy) [ prune-project (⇓pk p) ]tm >tm ∎
  where
    open Reasoning tm-setoid

lift-prune-sub : (p : Peak dy) → (σ : Sub _ n ⋆) → prune-sub p (lift-sub σ) ≃s lift-sub (prune-sub p σ)
lift-prune-sub (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = refl≃s
lift-prune-sub (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (lift-prune-sub p σ) refl≃tm) refl≃tm
lift-prune-sub (⇓pk p) σ = lift-prune-sub p σ
