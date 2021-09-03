{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
-- open import Catt.Syntax.Properties
-- open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Nat
-- open import Data.Nat.Properties
-- open import Data.Fin using (Fin;zero;suc;inject₁;toℕ)
open import Relation.Binary.PropositionalEquality
-- open import Catt.Globular
-- open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)
open import Catt.Suspension.Base public

susp-ty-lift : (B : Ty Γ) → suspTy (liftType {A = A} B) ≃ty liftType {A = suspTy A} (suspTy B)
susp-tm-lift : (t : Tm Γ) → suspTm (liftTerm {A = A} t) ≃tm liftTerm {A = suspTy A} (suspTm t)
susp-sub-lift : (σ : Sub Δ Γ ⋆) → suspSub (liftSub {A = A} σ) ≃s liftSub {A = suspTy A} (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm Star≃ refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ (Null≃ Star≃) refl≃tm) refl≃tm
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

susp-ty-height : ⦃ TyHeight A d ⦄ → TyHeight (suspTy A) (suc d)
susp-ty-height {A = ⋆} {_} ⦃ TyHeightB ⦄ = TyHeightS
susp-ty-height {A = s ─⟨ A ⟩⟶ t} ⦃ TyHeightS ⦄ = TyHeightS ⦃ susp-ty-height ⦄

susp-src-compat : (A : Ty Γ) → .⦃ _ : TyHeight A (suc d) ⦄ → suspTm (ty-src A) ≃tm ty-src (suspTy A) ⦃ susp-ty-height ⦄
susp-src-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-tgt-compat : (A : Ty Γ) → .⦃ _ : TyHeight A (suc d) ⦄ → suspTm (ty-tgt A) ≃tm ty-tgt (suspTy A) ⦃ susp-ty-height ⦄
susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-base-compat : (A : Ty Γ) → .⦃ _ : TyHeight A (suc d) ⦄ → suspTy (ty-base A) ≃ty ty-base (suspTy A) ⦃ susp-ty-height ⦄
susp-base-compat (s ─⟨ A ⟩⟶ t) = refl≃ty

-- suspLiftTy : {A : Ty Γ d′} (B : Ty Γ d) → suspTy (liftType {A = A} B) ≡ liftType (suspTy B)
-- suspLiftTm : {A : Ty Γ d′} (t : Tm Γ d) → suspTm (liftTerm {A = A} t) ≡ liftTerm (suspTm t)
-- suspLiftSub : {A : Ty Δ d′} (σ : Sub Γ Δ) → suspSub (liftSub {A = A} σ) ≡ liftSub (suspSub σ)

-- suspLiftTy ⋆ = refl
-- suspLiftTy (s ─⟨ A ⟩⟶ t)
--   = arr-equality (suspLiftTm s)
--                  (suspLiftTy A)
--                  (suspLiftTm t)

-- suspLiftTm (Var i) = refl
-- suspLiftTm (Coh Δ A p σ) = coh-equality refl (suspLiftSub σ)

-- suspLiftSub ⟨⟩ = refl
-- suspLiftSub {A = A} ⟨ σ , t ⟩
--   = sub-equality (suspLiftSub σ)
--                  (suspLiftTm t)

susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≃ty getFocusType (susp-pdb pdb)
susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≃tm getFocusTerm (susp-pdb pdb)

susp-pdb Base = Extend Base
susp-pdb (Extend pdb)
  = extend-pd-eq (susp-pdb pdb)
                 (susp-pdb-foc-ty pdb)
                 (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                       (trans≃ty (susp-ty-lift (getFocusType pdb)) (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                       (Var≃ refl))
                 -- (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                 --                      (cong liftTerm (susp-pdb-foc-tm pdb)))
                 --               (trans (suspLiftTy (getFocusType pdb))
                 --                      (cong liftType (susp-pdb-foc-ty pdb)))
                 --               refl)
susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

susp-pdb-foc-tm Base = Var≃ refl
susp-pdb-foc-tm (Extend pdb)
  = extend-pd-eq-foc-tm (susp-pdb pdb)
                        (susp-pdb-foc-ty pdb)
                        (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                              (trans≃ty (susp-ty-lift (getFocusType pdb)) (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                              (Var≃ refl))
susp-pdb-foc-tm (Restr pdb)
  = trans≃tm (susp-tgt-compat (getFocusType pdb) ⦃ getFocusTypeDim pdb ⦄) (ty-tgt-≃ (susp-pdb-foc-ty pdb) ⦃ susp-ty-height ⦃ getFocusTypeDim pdb ⦄ ⦄ ⦃ getFocusTypeDim (susp-pdb pdb) ⦄)

susp-pdb-foc-ty Base = refl≃ty
susp-pdb-foc-ty (Extend pdb)
  = trans≃ty (Arr≃ (susp-tm-lift (liftTerm (getFocusTerm pdb)))
                   (susp-ty-lift (liftType (getFocusType pdb)))
                   (Var≃ refl))
             (extend-pd-eq-foc-ty (susp-pdb pdb)
                                  (susp-pdb-foc-ty pdb)
                                  (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                                        (trans≃ty (susp-ty-lift (getFocusType pdb)) (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                                        (Var≃ refl)))
susp-pdb-foc-ty (Restr pdb)
  = trans≃ty (susp-base-compat (getFocusType pdb) ⦃ getFocusTypeDim pdb ⦄) (ty-base-≃ (susp-pdb-foc-ty pdb) ⦃ susp-ty-height ⦃ getFocusTypeDim pdb ⦄ ⦄ ⦃ getFocusTypeDim (susp-pdb pdb) ⦄)

susp-pd : Γ ⊢pd₀ d → suspCtx Γ ⊢pd₀ suc d
susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb))
