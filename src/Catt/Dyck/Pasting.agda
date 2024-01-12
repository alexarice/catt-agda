module Catt.Dyck.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Dyck
open import Catt.Dyck.Properties

dyck-to-pdb : (dy : Dyck n d) → ⌊ dy ⌋d ⊢pdb
dyck-to-pdb-focus-ty : (dy : Dyck n d) → focus-ty (dyck-to-pdb dy) ≃ty dyck-type dy
dyck-to-pdb-focus-tm : (dy : Dyck n d) → focus-tm (dyck-to-pdb dy) ≃tm dyck-term dy
dyck-to-pdb-focus-ty-dim : (dy : Dyck n d) → ty-dim (focus-ty (dyck-to-pdb dy)) ≡ d

dyck-to-pdb End = Base
dyck-to-pdb (⇑ dy) = Extend (dyck-to-pdb dy)
                            (sym≃ty (dyck-to-pdb-focus-ty dy))
                            (sym≃ty (Arr≃ (lift-tm-≃ (dyck-to-pdb-focus-tm dy))
                                          (lift-ty-≃ (dyck-to-pdb-focus-ty dy))
                                          refl≃tm))
dyck-to-pdb (⇓ dy) = Restr (dyck-to-pdb dy) ⦃ NonZero-subst (sym (dyck-to-pdb-focus-ty-dim dy)) it ⦄

dyck-to-pdb-focus-ty End = refl≃ty
dyck-to-pdb-focus-ty (⇑ dy) = refl≃ty
dyck-to-pdb-focus-ty (⇓ dy) = begin
  < ty-base (focus-ty (dyck-to-pdb dy)) >ty
    ≈⟨ ty-base-≃ (dyck-to-pdb-focus-ty dy) ⟩
  < ty-base (dyck-type dy) >ty
    ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
  < lift-ty (ty-base (dyck-pre-type dy)) >ty ∎
  where
    open Reasoning ty-setoid

dyck-to-pdb-focus-tm End = refl≃tm
dyck-to-pdb-focus-tm (⇑ dy) = refl≃tm
dyck-to-pdb-focus-tm (⇓ dy) = begin
  < ty-tgt (focus-ty (dyck-to-pdb dy)) ⦃ _ ⦄ >tm
    ≈⟨ ty-tgt-≃ (dyck-to-pdb-focus-ty dy) ⦃ _ ⦄ ⟩
  < ty-tgt (dyck-type dy) ⦃ _ ⦄ >tm
    ≈⟨ ty-tgt′-compat (dyck-type dy) ⦃ _ ⦄ ⟩
  < ty-tgt′ (dyck-type dy) >tm ∎
  where
    open Reasoning tm-setoid

dyck-to-pdb-focus-ty-dim dy = begin
  ty-dim (focus-ty (dyck-to-pdb dy))
    ≡⟨ ty-dim-≃ (dyck-to-pdb-focus-ty dy) ⟩
  ty-dim (dyck-type dy)
    ≡⟨ dyck-type-dim dy ⟩
  _ ∎
  where
    open ≡-Reasoning

dyck-to-pd : (dy : Dyck n 0) → ⌊ dy ⌋d ⊢pd
dyck-to-pd dy = Finish (dyck-to-pdb dy) ⦃ IsZero-subst (sym (dyck-to-pdb-focus-ty-dim dy)) it ⦄
