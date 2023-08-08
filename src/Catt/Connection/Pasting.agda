module Catt.Connection.Pasting where

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
open import Catt.Connection
open import Catt.Connection.Properties

connect-pdb : (pd : Γ ⊢pd) → Δ ⊢pdb → connect Γ (pd-focus-tm pd) Δ ⊢pdb
connect-focus-ty : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-ty (connect-pdb {Δ = Δ} pd pdb) ≃ty focus-ty pdb [ connect-inc-right (pd-focus-tm pd) m ]ty
connect-focus-tm : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-tm (connect-pdb {Δ = Δ} pd pdb) ≃tm focus-tm pdb [ connect-inc-right (pd-focus-tm pd) m ]tm

connect-pdb pd Base = pd-to-pdb pd
connect-pdb pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
connect-pdb pd (Extend {Γ = Δ , _} {A = A} {B = B} pdb p q) = Extend (connect-pdb pd pdb) lem1 lem2
  where
    lem3 : lift-tm (focus-tm pdb) [
              connect-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]tm
             ≃tm lift-tm (focus-tm (connect-pdb pd pdb))
    lem3 = begin
      < lift-tm (focus-tm pdb) [ ⟨ lift-sub (connect-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]tm >tm
        ≈⟨ lift-sub-comp-lem-tm (lift-sub (connect-inc-right (pd-focus-tm pd) _)) (focus-tm pdb) ⟩
      < focus-tm pdb [ lift-sub (connect-inc-right (pd-focus-tm pd) _) ]tm >tm
        ≈⟨ apply-lifted-sub-tm-≃ (focus-tm pdb) (connect-inc-right (pd-focus-tm pd) _) ⟩
      < lift-tm (focus-tm pdb [ connect-inc-right (pd-focus-tm pd) _ ]tm) >tm
        ≈˘⟨ lift-tm-≃ (connect-focus-tm pd pdb) ⟩
      < lift-tm (focus-tm (connect-pdb pd pdb)) >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning ty-setoid
    lem1 : (A [ connect-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty) ≃ty
             focus-ty (connect-pdb pd pdb)
    lem1 = begin
      < A [ connect-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty >ty
        ≈⟨ sub-action-≃-ty p refl≃s ⟩
      < focus-ty pdb [ connect-inc-right (pd-focus-tm pd) (ctxLength Δ) ]ty >ty
        ≈˘⟨ connect-focus-ty pd pdb ⟩
      < focus-ty (connect-pdb pd pdb) >ty ∎

    lem4 : lift-ty (focus-ty pdb) [ connect-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty
             ≃ty lift-ty (focus-ty (connect-pdb pd pdb))
    lem4 = begin
      < lift-ty (focus-ty pdb) [ ⟨ lift-sub (connect-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty (lift-sub (connect-inc-right (pd-focus-tm pd) _)) (focus-ty pdb) ⟩
      < focus-ty pdb [ lift-sub (connect-inc-right (pd-focus-tm pd) _) ]ty >ty
        ≈⟨ apply-lifted-sub-ty-≃ (focus-ty pdb) (connect-inc-right (pd-focus-tm pd) _) ⟩
      < lift-ty (focus-ty pdb [ connect-inc-right (pd-focus-tm pd) _ ]ty) >ty
        ≈˘⟨ lift-ty-≃ (connect-focus-ty pd pdb) ⟩
      < lift-ty (focus-ty (connect-pdb pd pdb)) >ty ∎

    lem2 : (B [ connect-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty) ≃ty
             (lift-tm (focus-tm (connect-pdb pd pdb)) ─⟨
              lift-ty (focus-ty (connect-pdb pd pdb)) ⟩⟶
              0V)
    lem2 = begin
      < B [ connect-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty >ty
        ≈⟨ sub-action-≃-ty q refl≃s ⟩
      < (lift-tm (focus-tm pdb) ─⟨ lift-ty (focus-ty pdb) ⟩⟶ 0V)
        [ connect-inc-right (pd-focus-tm pd) (suc (ctxLength Δ)) ]ty >ty
        ≈⟨ Arr≃ lem3 lem4 refl≃tm ⟩
      < lift-tm (focus-tm (connect-pdb pd pdb)) ─⟨ lift-ty (focus-ty (connect-pdb pd pdb)) ⟩⟶ 0V >ty ∎

connect-pdb pd (Restr pdb) = Restr (connect-pdb pd pdb) ⦃ NonZero-subst (sym (trans (ty-dim-≃ (connect-focus-ty pd pdb)) (sym (sub-dim (connect-inc-right (pd-focus-tm pd) _) (focus-ty pdb))))) it ⦄

connect-focus-ty pd Base = ⋆-is-only-0-d-ty ⦃ pd-to-pdb-0-d pd ⦄
connect-focus-ty pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
connect-focus-ty pd (Extend {Γ = Δ , A} {B = B} pdb p q) = begin
  < lift-ty (B [ ⟨ lift-sub (connect-inc-right (pd-focus-tm pd) _) , 0V ⟩ ]ty) >ty
    ≈˘⟨ apply-lifted-sub-ty-≃ B _ ⟩
  < B [ ⟨ lift-sub (lift-sub (connect-inc-right (pd-focus-tm pd) _)) , 1V ⟩ ]ty >ty
    ≈˘⟨ lift-sub-comp-lem-ty _ B ⟩
  < lift-ty B [ ⟨ ⟨ lift-sub (lift-sub (connect-inc-right (pd-focus-tm pd) _)) , 1V ⟩ , 0V ⟩ ]ty >ty ∎
  where
    open Reasoning ty-setoid

connect-focus-ty pd (Restr pdb) = begin
  < ty-base (focus-ty (connect-pdb pd pdb)) >ty
    ≈⟨ ty-base-≃ (connect-focus-ty pd pdb) ⟩
  < ty-base (focus-ty pdb [ connect-inc-right (pd-focus-tm pd) _ ]ty) >ty
    ≈˘⟨ ty-base-sub (focus-ty pdb) (connect-inc-right (pd-focus-tm pd) _) ⟩
  < ty-base (focus-ty pdb) [ connect-inc-right (pd-focus-tm pd) _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

connect-focus-tm pd Base = pd-to-pdb-focus-tm pd
connect-focus-tm pd (Extend {Γ = ∅} pdb p q) = ⊥-elim (pdb-odd-length pdb)
connect-focus-tm pd (Extend {Γ = Δ , A} pdb p q) = refl≃tm
connect-focus-tm pd (Restr pdb) = let
  instance .x : _
           x = NonZero-subst (sym (trans (ty-dim-≃ (connect-focus-ty pd pdb)) (sym (sub-dim (connect-inc-right (pd-focus-tm pd) _) (focus-ty pdb))))) it
  instance .y : _
           y = NonZero-subst (sub-dim (connect-inc-right (pd-focus-tm pd) _) (focus-ty pdb)) it
  in begin
  < ty-tgt (focus-ty (connect-pdb pd pdb)) >tm
    ≈⟨ ty-tgt-≃ (connect-focus-ty pd pdb) ⟩
  < ty-tgt (focus-ty pdb [ connect-inc-right (pd-focus-tm pd) _ ]ty) ⦃ y ⦄ >tm
    ≈˘⟨ ty-tgt-sub (focus-ty pdb) (connect-inc-right (pd-focus-tm pd) _) ⟩
  < ty-tgt (focus-ty pdb) [ connect-inc-right (pd-focus-tm pd) _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

connect-susp-pdb : (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → connect-susp Γ Δ ⊢pdb
connect-susp-pdb {Γ = Γ} {Δ = Δ} pd pdb = pdb-≃ (connect-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (connect-pdb (susp-pd pd) pdb)

connect-susp-focus-ty : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-ty (connect-susp-pdb pd pdb) ≃ty focus-ty pdb [ connect-susp-inc-right n m ]ty
connect-susp-focus-ty {Γ = Γ} {Δ = Δ} pd pdb = begin
  < focus-ty (connect-susp-pdb pd pdb) >ty
    ≈⟨ pdb-≃-focus-ty (connect-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (connect-pdb (susp-pd pd) pdb) ⟩
  < focus-ty (connect-pdb (susp-pd pd) pdb) >ty
    ≈⟨ connect-focus-ty (susp-pd pd) pdb ⟩
  < focus-ty pdb [ connect-inc-right (pd-focus-tm (susp-pd pd)) _ ]ty >ty
    ≈⟨ sub-action-≃-ty refl≃ty (connect-inc-right-≃ refl (susp-pd-focus pd) refl) ⟩
  < focus-ty pdb [ connect-susp-inc-right _ _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

connect-susp-focus-tm : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd) → (pdb : Δ ⊢pdb) → focus-tm (connect-susp-pdb pd pdb) ≃tm focus-tm pdb [ connect-susp-inc-right n m ]tm
connect-susp-focus-tm {Γ = Γ} {Δ = Δ} pd pdb = begin
  < focus-tm (connect-susp-pdb pd pdb) >tm
    ≈⟨ pdb-≃-focus-tm (connect-≃ (refl≃c {Γ = susp-ctx Γ}) (susp-pd-focus pd) (refl≃c {Γ = Δ})) (connect-pdb (susp-pd pd) pdb) ⟩
  < focus-tm (connect-pdb (susp-pd pd) pdb) >tm
    ≈⟨ connect-focus-tm (susp-pd pd) pdb ⟩
  < focus-tm pdb [ connect-inc-right (pd-focus-tm (susp-pd pd)) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = focus-tm pdb}) (connect-inc-right-≃ refl (susp-pd-focus pd) refl) ⟩
  < focus-tm pdb [ connect-susp-inc-right _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

connect-susp-pd : (pd : Γ ⊢pd) → (pd2 : Δ ⊢pd) → connect-susp Γ Δ ⊢pd
connect-susp-pd pd pd2 = Finish (connect-susp-pdb pd (pd-to-pdb pd2)) ⦃ IsZero-subst (sym (trans (ty-dim-≃ (connect-susp-focus-ty pd (pd-to-pdb pd2))) (sym (sub-dim (connect-susp-inc-right _ _) (pd-focus-ty pd2))))) (pd-to-pdb-0-d pd2) ⦄
