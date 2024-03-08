module Catt.Wedge.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Wedge
open import Catt.Wedge.Properties

wedge-pdb : (pd : Γ ⊢pd) → Δ ⊢pdb → wedge Γ (pd-focus-tm pd) Δ ⊢pdb
wedge-focus-ty : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-ty (wedge-pdb {Δ = Δ} pd pdb) ≃ty focus-ty pdb [ wedge-inc-right (pd-focus-tm pd) m ]ty
wedge-focus-tm : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-tm (wedge-pdb {Δ = Δ} pd pdb) ≃tm focus-tm pdb [ wedge-inc-right (pd-focus-tm pd) m ]tm

wedge-pdb pd Base = pd-to-pdb pd
wedge-pdb pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
wedge-pdb pd (Extend {Γ = Δ , _} {A = A} {B = B} pdb p q) = Extend (wedge-pdb pd pdb) lem1 lem2
  where
    lem3 : wk-tm (focus-tm pdb) [
              wedge-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]tm
             ≃tm wk-tm (focus-tm (wedge-pdb pd pdb))
    lem3 = begin
      < wk-tm (focus-tm pdb) [ ⟨ wk-sub (wedge-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]tm >tm
        ≈⟨ apply-sub-wk-tm-≃ (focus-tm pdb) ⟨ wk-sub (wedge-inc-right (pd-focus-tm pd) _) , 0V ⟩ ⟩
      < focus-tm pdb [ wk-sub (wedge-inc-right (pd-focus-tm pd) _) ]tm >tm
        ≈⟨ apply-wk-sub-tm-≃ (focus-tm pdb) (wedge-inc-right (pd-focus-tm pd) _) ⟩
      < wk-tm (focus-tm pdb [ wedge-inc-right (pd-focus-tm pd) _ ]tm) >tm
        ≈˘⟨ wk-tm-≃ (wedge-focus-tm pd pdb) ⟩
      < wk-tm (focus-tm (wedge-pdb pd pdb)) >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning ty-setoid
    lem1 : (A [ wedge-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty) ≃ty
             focus-ty (wedge-pdb pd pdb)
    lem1 = begin
      < A [ wedge-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty >ty
        ≈⟨ sub-action-≃-ty p refl≃s ⟩
      < focus-ty pdb [ wedge-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty >ty
        ≈˘⟨ wedge-focus-ty pd pdb ⟩
      < focus-ty (wedge-pdb pd pdb) >ty ∎

    lem4 : wk-ty (focus-ty pdb) [ wedge-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty
             ≃ty wk-ty (focus-ty (wedge-pdb pd pdb))
    lem4 = begin
      < wk-ty (focus-ty pdb) [ ⟨ wk-sub (wedge-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]ty >ty
        ≈⟨ apply-sub-wk-ty-≃ (focus-ty pdb) ⟨ wk-sub (wedge-inc-right (pd-focus-tm pd) _) , 0V ⟩ ⟩
      < focus-ty pdb [ wk-sub (wedge-inc-right (pd-focus-tm pd) _) ]ty >ty
        ≈⟨ apply-wk-sub-ty-≃ (focus-ty pdb) (wedge-inc-right (pd-focus-tm pd) _) ⟩
      < wk-ty (focus-ty pdb [ wedge-inc-right (pd-focus-tm pd) _ ]ty) >ty
        ≈˘⟨ wk-ty-≃ (wedge-focus-ty pd pdb) ⟩
      < wk-ty (focus-ty (wedge-pdb pd pdb)) >ty ∎

    lem2 : (B [ wedge-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty) ≃ty
             (wk-tm (focus-tm (wedge-pdb pd pdb)) ─⟨
              wk-ty (focus-ty (wedge-pdb pd pdb)) ⟩⟶
              0V)
    lem2 = begin
      < B [ wedge-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty >ty
        ≈⟨ sub-action-≃-ty q refl≃s ⟩
      < (wk-tm (focus-tm pdb) ─⟨ wk-ty (focus-ty pdb) ⟩⟶ 0V)
        [ wedge-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty >ty
        ≈⟨ Arr≃ lem3 lem4 refl≃tm ⟩
      < wk-tm (focus-tm (wedge-pdb pd pdb)) ─⟨ wk-ty (focus-ty (wedge-pdb pd pdb)) ⟩⟶ 0V >ty ∎

wedge-pdb pd (Restr pdb) = Restr (wedge-pdb pd pdb) ⦃ NonZero-subst (sym (trans (ty-dim-≃ (wedge-focus-ty pd pdb)) (sym (sub-dim (wedge-inc-right (pd-focus-tm pd) _) (focus-ty pdb))))) it ⦄

wedge-focus-ty pd Base = ⋆-is-only-0-d-ty ⦃ pd-to-pdb-0-d pd ⦄
wedge-focus-ty pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
wedge-focus-ty pd (Extend {Γ = Δ , A} {B = B} pdb p q) = begin
  < wk-ty (B [ ⟨ wk-sub (wedge-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]ty) >ty
    ≈˘⟨ apply-wk-sub-ty-≃ B _ ⟩
  < B [ ⟨ wk-sub (wk-sub (wedge-inc-right (pd-focus-tm pd) _)) , 1V ⟩ ]ty >ty
    ≈˘⟨ apply-sub-wk-ty-≃ B _ ⟩
  < wk-ty B [ ⟨ ⟨ wk-sub (wk-sub (wedge-inc-right (pd-focus-tm pd) _)) , 1V ⟩ , 0V ⟩ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-focus-ty pd (Restr pdb) = begin
  < ty-base (focus-ty (wedge-pdb pd pdb)) >ty
    ≈⟨ ty-base-≃ (wedge-focus-ty pd pdb) ⟩
  < ty-base (focus-ty pdb [ wedge-inc-right (pd-focus-tm pd) _ ]ty) >ty
    ≈˘⟨ ty-base-sub (focus-ty pdb) (wedge-inc-right (pd-focus-tm pd) _) ⟩
  < ty-base (focus-ty pdb) [ wedge-inc-right (pd-focus-tm pd) _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-focus-tm pd Base = pd-to-pdb-focus-tm pd
wedge-focus-tm pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
wedge-focus-tm pd (Extend {Γ = Δ , A} pdb p q) = refl≃tm
wedge-focus-tm pd (Restr pdb) = let
  instance .x : _
           x = NonZero-subst (sym (trans (ty-dim-≃ (wedge-focus-ty pd pdb)) (sym (sub-dim (wedge-inc-right (pd-focus-tm pd) _) (focus-ty pdb))))) it
  instance .y : _
           y = NonZero-subst (sub-dim (wedge-inc-right (pd-focus-tm pd) _) (focus-ty pdb)) it
  in begin
  < ty-tgt (focus-ty (wedge-pdb pd pdb)) >tm
    ≈⟨ ty-tgt-≃ (wedge-focus-ty pd pdb) ⟩
  < ty-tgt (focus-ty pdb [ wedge-inc-right (pd-focus-tm pd) _ ]ty) ⦃ y ⦄ >tm
    ≈˘⟨ ty-tgt-sub (focus-ty pdb) (wedge-inc-right (pd-focus-tm pd) _) ⟩
  < ty-tgt (focus-ty pdb) [ wedge-inc-right (pd-focus-tm pd) _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

wedge-susp-pdb : (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → wedge-susp Γ Δ ⊢pdb
wedge-susp-pdb {Γ = Γ} {Δ = Δ} pd pdb = pdb-≃ (wedge-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (wedge-pdb (susp-pd pd) pdb)

wedge-susp-focus-ty : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-ty (wedge-susp-pdb pd pdb) ≃ty focus-ty pdb [ wedge-susp-inc-right n m ]ty
wedge-susp-focus-ty {Γ = Γ} {Δ = Δ} pd pdb = begin
  < focus-ty (wedge-susp-pdb pd pdb) >ty
    ≈⟨ pdb-≃-focus-ty (wedge-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (wedge-pdb (susp-pd pd) pdb) ⟩
  < focus-ty (wedge-pdb (susp-pd pd) pdb) >ty
    ≈⟨ wedge-focus-ty (susp-pd pd) pdb ⟩
  < focus-ty pdb [ wedge-inc-right (pd-focus-tm (susp-pd pd)) _ ]ty >ty
    ≈⟨ sub-action-≃-ty refl≃ty (wedge-inc-right-≃ refl (susp-pd-focus pd) refl) ⟩
  < focus-ty pdb [ wedge-susp-inc-right _ _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-susp-focus-tm : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-tm (wedge-susp-pdb pd pdb) ≃tm focus-tm pdb [ wedge-susp-inc-right n m ]tm
wedge-susp-focus-tm {Γ = Γ} {Δ = Δ} pd pdb = begin
  < focus-tm (wedge-susp-pdb pd pdb) >tm
    ≈⟨ pdb-≃-focus-tm (wedge-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (wedge-pdb (susp-pd pd) pdb) ⟩
  < focus-tm (wedge-pdb (susp-pd pd) pdb) >tm
    ≈⟨ wedge-focus-tm (susp-pd pd) pdb ⟩
  < focus-tm pdb [ wedge-inc-right (pd-focus-tm (susp-pd pd)) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = focus-tm pdb}) (wedge-inc-right-≃ refl (susp-pd-focus pd) refl) ⟩
  < focus-tm pdb [ wedge-susp-inc-right _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

wedge-susp-pd : (pd : Γ ⊢pd) → (pd2 : Δ ⊢pd) → wedge-susp Γ Δ ⊢pd
wedge-susp-pd pd pd2 = Finish (wedge-susp-pdb pd (pd-to-pdb pd2)) ⦃ IsZero-subst (sym (trans (ty-dim-≃ (wedge-susp-focus-ty pd (pd-to-pdb pd2))) (sym (sub-dim (wedge-susp-inc-right _ _) (pd-focus-ty pd2))))) (pd-to-pdb-0-d pd2) ⦄
