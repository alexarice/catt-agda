{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular.Properties where

open import Catt.Syntax
open import Catt.Globular
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin using (Fin;suc;zero)

tm-to-ty-≃ : {s : Tm Γ (suc d)} {t : Tm Δ (suc d′)} → Γ ≃c Δ → s ≃tm t → tm-to-ty s ≃ty tm-to-ty t
tm-to-ty-≃ p (Var≃ x) = ‼-≃ _ _ x p
tm-to-ty-≃ p (Coh≃ q r s) = sub-action-≃-ty r s

-- tm-to-ty-sub : (t : Tm Γ (suc d)) → (σ : Sub Γ Δ) → tm-to-ty (t [ σ ]tm) ≃ty tm-to-ty t [ σ ]ty
-- tm-to-ty-sub (Var i) σ = {!!}
--   where
--     lem : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → tm-to-ty (Var i [ σ ]tm) ≃ty (Γ ‼ i [ σ ]ty)
--     lem {Γ = Γ , A} zero ⟨ σ , t ⟩ = trans≃ty {!!} (sym≃ty (lift-sub-comp-lem-ty σ A))
--     lem {Γ = Γ , A} (suc i) ⟨ σ , t ⟩ = {!!}
-- tm-to-ty-sub (Coh Δ A x τ) σ = assoc-ty σ τ A
