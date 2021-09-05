{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular.Properties where

open import Catt.Syntax
open import Catt.Globular
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin using (Fin;suc;zero)
open import Relation.Binary.PropositionalEquality

-- src-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_(ty-src_A)_[_σ_]tm_≡_ty-src_(A_[_σ_]ty)
-- src-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

-- tgt-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_ty-tgt_A_[_σ_]tm_≡_ty-tgt_(A_[_σ_]ty)
-- tgt-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

-- base-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_ty-base_A_[_σ_]ty_≡_ty-base_(A_[_σ_]ty)
-- base-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

-- tm-to-ty-≃ : {s : Tm Γ (suc d)} {t : Tm Δ (suc d′)} → Γ ≃c Δ → s ≃tm t → tm-to-ty s ≃ty tm-to-ty t
-- tm-to-ty-≃ p (Var≃ x) = ‼-≃ _ _ x p
-- tm-to-ty-≃ p (Coh≃ q r s) = sub-action-≃-ty r s

ty-src-≃ : A ≃ty B → ty-src A ≃tm ty-src B
ty-src-≃ (Arr≃ p q r) = p

ty-tgt-≃ : A ≃ty B → ty-tgt A ≃tm ty-tgt B
ty-tgt-≃ (Arr≃ p q r) = r

ty-base-≃ : A ≃ty B → ty-base A ≃ty ty-base B
ty-base-≃ (Arr≃ p q r) = q

-- tm-to-ty-sub : (t : Tm Γ (suc d)) → (σ : Sub Γ Δ) → tm-to-ty (t [ σ ]tm) ≃ty tm-to-ty t [ σ ]ty
-- tm-to-ty-sub (Var i) σ = {!!}
--   where
--     lem : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → tm-to-ty (Var i [ σ ]tm) ≃ty (Γ ‼ i [ σ ]ty)
--     lem {Γ = Γ , A} zero ⟨ σ , t ⟩ = trans≃ty {!!} (sym≃ty (lift-sub-comp-lem-ty σ A))
--     lem {Γ = Γ , A} (suc i) ⟨ σ , t ⟩ = {!!}
-- tm-to-ty-sub (Coh Δ A x τ) σ = assoc-ty σ τ A
