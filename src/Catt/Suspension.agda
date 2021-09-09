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
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ)
open import Relation.Binary.PropositionalEquality
open import Catt.Globular
open import Catt.Globular.Properties
-- open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)

suspCtx : Ctx n → Ctx (2 + n)
suspTy : Ty n d → Ty (2 + n) (suc d)
getFst : Tm (2 + n)
getSnd : Tm (2 + n)
suspTm : Tm n → Tm (2 + n)
suspSub : Sub n m → Sub (2 + n) (2 + m)

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst = Var (fromℕ _)

getSnd = Var (inject₁ (fromℕ _))

suspTm (Var i) = Var (inject₁ (inject₁ i))
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

susp-ty-lift : (B : Ty n d) → suspTy (liftType B) ≃ty liftType (suspTy B)
susp-tm-lift : (t : Tm n) → suspTm (liftTerm t) ≃tm liftTerm (suspTm t)
susp-sub-lift : (σ : Sub n m) → suspSub (liftSub σ) ≃s liftSub (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm (Star≃ refl) refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ (Null≃ refl) refl≃tm) refl≃tm
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

susp-src-compat : (A : Ty n (suc d)) → suspTm (ty-src A) ≃tm ty-src (suspTy A)
susp-src-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-tgt-compat : (A : Ty n (suc d)) → suspTm (ty-tgt A) ≃tm ty-tgt (suspTy A)
susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-base-compat : (A : Ty n (suc d)) → suspTy (ty-base A) ≃ty ty-base (suspTy A)
susp-base-compat (s ─⟨ A ⟩⟶ t) = refl≃ty

susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≃ty getFocusType (susp-pdb pdb)
susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≃tm getFocusTerm (susp-pdb pdb)

susp-pdb-≃-lem : (pdb : Γ ⊢pd[ submax ][ d ]) → (suspTm (liftTerm (getFocusTerm pdb)) ─⟨
                                                   suspTy (liftType (getFocusType pdb)) ⟩⟶ 0V)
                                                  ≃ty
                                                  (liftTerm (getFocusTerm (susp-pdb pdb)) ─⟨
                                                   liftType (getFocusType (susp-pdb pdb)) ⟩⟶ 0V)
susp-pdb-≃-lem pdb = Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                          (trans≃ty (susp-ty-lift (getFocusType pdb)) (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                          (Var≃ refl refl)

susp-pdb Base = Extend Base
susp-pdb (Extend pdb)
  = extend-pd-eq (susp-pdb pdb)
                 (susp-pdb-foc-ty pdb)
                 (susp-pdb-≃-lem pdb)
susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

susp-pdb-foc-tm Base = refl≃tm
susp-pdb-foc-tm (Extend pdb)
  = extend-pd-eq-foc-tm (susp-pdb pdb)
                        (susp-pdb-foc-ty pdb)
                        (susp-pdb-≃-lem pdb)
susp-pdb-foc-tm (Restr pdb)
  = trans≃tm (susp-tgt-compat (getFocusType pdb)) (ty-tgt-≃ (susp-pdb-foc-ty pdb))

susp-pdb-foc-ty Base = refl≃ty
susp-pdb-foc-ty (Extend pdb)
  = trans≃ty (Arr≃ (susp-tm-lift (liftTerm (getFocusTerm pdb)))
                   (susp-ty-lift (liftType (getFocusType pdb)))
                   refl≃tm)
             (extend-pd-eq-foc-ty (susp-pdb pdb)
                                  (susp-pdb-foc-ty pdb)
                                  (susp-pdb-≃-lem pdb))
susp-pdb-foc-ty (Restr pdb)
  = trans≃ty (susp-base-compat (getFocusType pdb)) (ty-base-≃ (susp-pdb-foc-ty pdb))

susp-pd : Γ ⊢pd₀ d → suspCtx Γ ⊢pd₀ suc d
susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb))
