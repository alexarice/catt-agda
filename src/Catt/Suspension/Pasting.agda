module Catt.Suspension.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Suspension.Properties

susp-pdb : Γ ⊢pdb → susp-ctx Γ ⊢pdb
susp-focus-ty : (pdb : Γ ⊢pdb) → focus-ty (susp-pdb pdb) ≃ty susp-ty (focus-ty pdb)
susp-focus-tm : (pdb : Γ ⊢pdb) → focus-tm (susp-pdb pdb) ≃tm susp-tm (focus-tm pdb)

susp-pdb Base = Extend Base refl≃ty refl≃ty
susp-pdb (Extend pdb p q) = Extend (susp-pdb pdb)
                                   (trans≃ty (susp-ty-≃ p) (sym≃ty (susp-focus-ty pdb)))
                                   (trans≃ty (susp-ty-≃ q)
                                             (Arr≃ (trans≃tm (susp-tm-wk (focus-tm pdb)) (wk-tm-≃ (sym≃tm (susp-focus-tm pdb))))
                                                   (trans≃ty (susp-ty-wk (focus-ty pdb)) (wk-ty-≃ (sym≃ty (susp-focus-ty pdb))))
                                                   refl≃tm))
susp-pdb (Restr pdb) = Restr (susp-pdb pdb) ⦃ NonZero-subst (trans (sym (susp-dim (focus-ty pdb))) (cong ty-dim (≃ty-to-≡ (sym≃ty (susp-focus-ty pdb))))) it ⦄

susp-focus-ty Base = refl≃ty
susp-focus-ty (Extend pdb p q) = sym≃ty (susp-ty-wk _)
susp-focus-ty (Restr pdb) = begin
  < ty-base (focus-ty (susp-pdb pdb)) >ty
    ≈⟨ ty-base-≃ (susp-focus-ty pdb) ⟩
  < ty-base (susp-ty (focus-ty pdb)) >ty
    ≈⟨ ty-base-susp (focus-ty pdb) ⟩
  < susp-ty (ty-base (focus-ty pdb)) >ty ∎
  where
    open Reasoning ty-setoid

susp-focus-tm Base = refl≃tm
susp-focus-tm (Extend pdb p q) = refl≃tm
susp-focus-tm (Restr pdb) = let
  instance .x : _
           x = NonZero-subst (sym (susp-dim (focus-ty pdb))) it
  instance .y : _
           y = NonZero-subst (sym (trans (ty-dim-≃ (susp-focus-ty pdb)) (susp-dim (focus-ty pdb)))) it
  in begin
  < ty-tgt (focus-ty (susp-pdb pdb)) ⦃ y ⦄ >tm
    ≈⟨ ty-tgt-≃ (susp-focus-ty pdb) ⦃ y ⦄ ⟩
  < ty-tgt (susp-ty (focus-ty pdb)) >tm
    ≈⟨ ty-tgt-susp (focus-ty pdb) ⟩
  < susp-tm (ty-tgt (focus-ty pdb)) >tm ∎
  where
    open Reasoning tm-setoid

susp-pd : Γ ⊢pd → susp-ctx Γ ⊢pd
susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb) ⦃ NonZero-subst (sym (trans (ty-dim-≃ (susp-focus-ty pdb)) (susp-dim (focus-ty pdb)))) it ⦄) ⦃ IsZero-subst (sym (trans (ty-dim-≃ (ty-base-≃ (susp-focus-ty pdb))) (trans (ty-base-dim (susp-ty (focus-ty pdb))) (cong pred (susp-dim (focus-ty pdb)))))) it ⦄

susp-pd-focus : (pd : Γ ⊢pd) → pd-focus-tm (susp-pd pd) ≃tm get-snd {n = ctxLength Γ}
susp-pd-focus (Finish pdb) = let
  instance .x : _
           x = NonZero-subst (sym (trans (ty-dim-≃ (susp-focus-ty pdb)) (susp-dim (focus-ty pdb)))) it
  instance .y : _
           y = NonZero-subst (sym (susp-dim (focus-ty pdb))) it
  in begin
  < ty-tgt (focus-ty (susp-pdb pdb)) >tm
    ≈⟨ ty-tgt-≃ (susp-focus-ty pdb) ⟩
  < ty-tgt (susp-ty (focus-ty pdb)) ⦃ y ⦄ >tm
    ≈⟨ ty-tgt-≃ (susp-ty-≃ ⋆-is-only-0-d-ty) ⟩
  < ty-tgt (susp-ty ⋆) >tm ∎
  where
    open Reasoning tm-setoid
