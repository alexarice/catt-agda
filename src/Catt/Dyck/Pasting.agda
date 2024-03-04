module Catt.Dyck.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
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

⇓-NonZero : Dyck n d → .⦃ NonZero d ⦄ → Dyck n (pred d)
⇓-NonZero {d = suc d} dy = ⇓ dy

⇓-NonZero-≃ : {dy : Dyck n d} → {ey : Dyck m d′} → (p : dy ≃d ey) → .⦃ _ : NonZero d ⦄ → ⇓-NonZero dy ≃d ⇓-NonZero ey ⦃ NonZero-subst (≃d-to-same-d p) it ⦄
⇓-NonZero-≃ {d = suc d} {d′ = zero} p with ≃d-to-same-d p
... | ()
⇓-NonZero-≃ {d = suc d} {d′ = suc d′} p = ⇓≃ p

⇓-NonZero-⌊⌋d : (dy : Dyck n d) → .⦃ _ : NonZero d ⦄ → ⌊ ⇓-NonZero dy ⌋d ≃c ⌊ dy ⌋d
⇓-NonZero-⌊⌋d {d = suc d} dy = refl≃c

dyck-type-⇓-NonZero : (dy : Dyck n d) → .⦃ _ : NonZero d ⦄ → dyck-type (⇓-NonZero dy) ≃ty ty-base (dyck-type dy)
dyck-type-⇓-NonZero {d = suc d} dy = sym≃ty (ty-base-lift (dyck-pre-type dy))

dyck-term-⇓-NonZero : (dy : Dyck n d) → .⦃ _ : NonZero d ⦄ → dyck-term (⇓-NonZero dy) ≃tm ty-tgt′ (dyck-type dy)
dyck-term-⇓-NonZero {d = suc d} dy = refl≃tm

pdb-to-dyck : (pdb : Γ ⊢pdb) → Dyck (pdb-length pdb) (pdb-focus-dim pdb)
pdb-to-dyck Base = End
pdb-to-dyck (Extend pdb p q) = ⇑ (pdb-to-dyck pdb)
pdb-to-dyck (Restr pdb) = ⇓-NonZero (pdb-to-dyck pdb) ⦃ NonZero-subst (sym (pdb-focus-dim-prop pdb)) it ⦄

pd-to-dyck : (pd : Γ ⊢pd) → Dyck (pd-length pd) (pd-focus-dim pd)
pd-to-dyck (Finish pdb) = pdb-to-dyck pdb

pdb-to-dyck-focus-ty : (pdb : Γ ⊢pdb) → dyck-type (pdb-to-dyck pdb) ≃ty focus-ty pdb
pdb-to-dyck-focus-tm : (pdb : Γ ⊢pdb) → dyck-term (pdb-to-dyck pdb) ≃tm focus-tm pdb

pdb-to-dyck-focus-ty Base = refl≃ty
pdb-to-dyck-focus-ty (Extend {B = B} pdb p q) = begin
  < lift-ty (lift-tm (dyck-term (pdb-to-dyck pdb))
            ─⟨ lift-ty (dyck-type (pdb-to-dyck pdb)) ⟩⟶
            Var 0F) >ty
    ≈⟨ lift-ty-≃ (Arr≃ (lift-tm-≃ (pdb-to-dyck-focus-tm pdb)) (lift-ty-≃ (pdb-to-dyck-focus-ty pdb)) (Var≃ (cong suc (pdb-length-prop pdb)) refl)) ⟩
  < lift-ty (lift-tm (focus-tm pdb) ─⟨ lift-ty (focus-ty pdb) ⟩⟶ Var 0F) >ty
    ≈˘⟨ lift-ty-≃ q ⟩
  < lift-ty B >ty ∎
  where
    open Reasoning ty-setoid
pdb-to-dyck-focus-ty (Restr pdb) = begin
  < dyck-type (⇓-NonZero (pdb-to-dyck pdb) ⦃ _ ⦄) >ty
    ≈⟨ dyck-type-⇓-NonZero (pdb-to-dyck pdb) ⦃ _ ⦄ ⟩
  < ty-base (dyck-type (pdb-to-dyck pdb)) >ty
    ≈⟨ ty-base-≃ (pdb-to-dyck-focus-ty pdb) ⟩
  < ty-base (focus-ty pdb) >ty ∎
  where
    open Reasoning ty-setoid

pdb-to-dyck-focus-tm Base = refl≃tm
pdb-to-dyck-focus-tm (Extend pdb p q) = Var≃ (cong 2+ (pdb-length-prop pdb)) refl
pdb-to-dyck-focus-tm (Restr pdb) = begin
  < dyck-term (⇓-NonZero (pdb-to-dyck pdb) ⦃ _ ⦄) >tm
    ≈⟨ dyck-term-⇓-NonZero (pdb-to-dyck pdb) ⦃ _ ⦄ ⟩
  < ty-tgt′ (dyck-type (pdb-to-dyck pdb)) >tm
    ≈˘⟨ ty-tgt′-compat (dyck-type (pdb-to-dyck pdb)) ⦃ NonZero-subst (ty-dim-≃ (sym≃ty (pdb-to-dyck-focus-ty pdb))) it ⦄ ⟩
  < ty-tgt (dyck-type (pdb-to-dyck pdb)) ⦃ _ ⦄ >tm
    ≈⟨ ty-tgt-≃ (pdb-to-dyck-focus-ty pdb) ⦃ _ ⦄ ⟩
  < ty-tgt (focus-ty pdb) ⦃ it ⦄ >tm ∎
  where
    open Reasoning tm-setoid

dyck-to-pdb-to-dyck : (dy : Dyck n d) → pdb-to-dyck (dyck-to-pdb dy) ≃d dy
dyck-to-pdb-to-dyck End = refl≃d
dyck-to-pdb-to-dyck (⇑ dy) = ⇑≃ (dyck-to-pdb-to-dyck dy)
dyck-to-pdb-to-dyck (⇓ dy) = sym≃d (⇓-NonZero-≃ (sym≃d (dyck-to-pdb-to-dyck dy)))

dyck-to-pd-to-dyck : (dy : Dyck n 0) → pd-to-dyck (dyck-to-pd dy) ≃d dy
dyck-to-pd-to-dyck dy = dyck-to-pdb-to-dyck dy

pdb-to-dyck-to-ctx : (pdb : Γ ⊢pdb) → ⌊ pdb-to-dyck pdb ⌋d ≃c Γ
pdb-to-dyck-to-ctx Base = refl≃c
pdb-to-dyck-to-ctx (Extend {A = A} {B = B} pdb p q)
  = Add≃ (Add≃ (pdb-to-dyck-to-ctx pdb) l1) l2
  where
    open Reasoning ty-setoid

    l1 : dyck-type (pdb-to-dyck pdb) ≃ty A
    l1 = begin
      < dyck-type (pdb-to-dyck pdb) >ty
        ≈⟨ pdb-to-dyck-focus-ty pdb ⟩
      < focus-ty pdb >ty
        ≈˘⟨ p ⟩
      < A >ty ∎

    l2 : dyck-pre-type (⇑ (pdb-to-dyck pdb)) ≃ty B
    l2 = begin
      < dyck-pre-type (⇑ (pdb-to-dyck pdb)) >ty
        ≈⟨ Arr≃ (lift-tm-≃ (pdb-to-dyck-focus-tm pdb))
                (lift-ty-≃ (pdb-to-dyck-focus-ty pdb))
                (Var≃ (cong suc (pdb-length-prop pdb)) refl) ⟩
      < lift-tm (focus-tm pdb) ─⟨ lift-ty (focus-ty pdb) ⟩⟶ Var 0F >ty
        ≈˘⟨ q ⟩
      < B >ty ∎
pdb-to-dyck-to-ctx {Γ = Γ} (Restr pdb) = begin
  < ⌊ ⇓-NonZero (pdb-to-dyck pdb) ⦃ _ ⦄ ⌋d >c
    ≈⟨ ⇓-NonZero-⌊⌋d (pdb-to-dyck pdb) ⦃ _ ⦄ ⟩
  < ⌊ pdb-to-dyck pdb ⌋d >c
    ≈⟨ pdb-to-dyck-to-ctx pdb ⟩
  < Γ >c ∎
  where
    open Reasoning ctx-setoid
