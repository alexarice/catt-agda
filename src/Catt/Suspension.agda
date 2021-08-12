{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Patterns
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Catt.Dimension

suspCtx : Ctx n d → Ctx (suc (suc n)) (suc d)
suspTy : Ty Γ n → Ty (suspCtx Γ) (suc n)
getFst : Tm (suspCtx Γ) 2
getSnd : Tm (suspCtx Γ) 2
suspTm : Tm Γ n → Tm (suspCtx Γ) (suc n)
suspSub : Sub Γ Δ → Sub (suspCtx Γ) (suspCtx Δ)
lookupSusp : (i : Fin (ctxLength Γ)) → Tm (suspCtx Γ) (suc (suc (lookupDim Γ i)))

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst {Γ = ∅} = 1V
getFst {Γ = Γ , A} = liftTerm getFst

getSnd {Γ = ∅} = 0V
getSnd {Γ = Γ , A} = liftTerm getSnd

suspTm (Var i) = lookupSusp i
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

lookupSusp {Γ = Γ , A} zero = 0V
lookupSusp {Γ = Γ , A} (suc i) = liftTerm (lookupSusp i)

susp-src-compat : (A : Ty Γ (suc (suc d))) → suspTm (ty-src A) ≡ ty-src (suspTy A)
susp-src-compat (s ─⟨ A ⟩⟶ t) = refl

susp-tgt-compat : (A : Ty Γ (suc (suc d))) → suspTm (ty-tgt A) ≡ ty-tgt (suspTy A)
susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl

susp-base-compat : (A : Ty Γ (suc (suc d))) → suspTy (ty-base A) ≡ ty-base (suspTy A)
susp-base-compat (s ─⟨ A ⟩⟶ t) = refl

suspLiftTy : {A : Ty Γ d′} (B : Ty Γ d) → suspTy (liftType {A = A} B) ≡ liftType (suspTy B)
suspLiftTm : {A : Ty Γ d′} (t : Tm Γ d) → suspTm (liftTerm {A = A} t) ≡ liftTerm (suspTm t)
suspLiftSub : {A : Ty Δ d′} (σ : Sub Γ Δ) → suspSub (liftSub {A = A} σ) ≡ liftSub (suspSub σ)

suspLiftTy ⋆ = refl
suspLiftTy (s ─⟨ A ⟩⟶ t)
  = arr-equality (suspLiftTm s)
                 (suspLiftTy A)
                 (suspLiftTm t)

suspLiftTm (Var i) = refl
suspLiftTm (Coh Δ A σ) = coh-equality refl (suspLiftSub σ)

suspLiftSub ⟨⟩ = refl
suspLiftSub {A = A} ⟨ σ , t ⟩
  = sub-equality (suspLiftSub σ)
                 (suspLiftTm t)

susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≡ getFocusType (susp-pdb pdb)
susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≡ getFocusTerm (susp-pdb pdb)

susp-pdb Base = Extend Base
susp-pdb (Extend pdb)
  = extend-pd-eq (susp-pdb pdb)
                 (susp-pdb-foc-ty pdb)
                 (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                                      (cong liftTerm (susp-pdb-foc-tm pdb)))
                               (trans (suspLiftTy (getFocusType pdb))
                                      (cong liftType (susp-pdb-foc-ty pdb)))
                               refl)
susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

susp-pdb-foc-tm Base = refl
susp-pdb-foc-tm (Extend pdb)
  = extend-pd-eq-foc-tm (susp-pdb pdb)
                        (susp-pdb-foc-ty pdb)
                        (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                                             (cong liftTerm (susp-pdb-foc-tm pdb)))
                                      (trans (suspLiftTy (getFocusType pdb))
                                             (cong liftType (susp-pdb-foc-ty pdb)))
                                      refl)
susp-pdb-foc-tm (Restr pdb)
  = trans (susp-tgt-compat (getFocusType pdb))
          (cong ty-tgt (susp-pdb-foc-ty pdb))

susp-pdb-foc-ty Base = refl
susp-pdb-foc-ty (Extend pdb)
  = trans (arr-equality (trans (suspLiftTm (liftTerm (getFocusTerm pdb)))
                               (cong liftTerm (trans (suspLiftTm (getFocusTerm pdb))
                                                     (cong liftTerm (susp-pdb-foc-tm pdb)))))
                        (trans (suspLiftTy (liftType (getFocusType pdb)))
                               (cong liftType (trans (suspLiftTy (getFocusType pdb))
                                                     (cong liftType (susp-pdb-foc-ty pdb)))))
                        refl)
          (extend-pd-eq-foc-ty (susp-pdb pdb)
                               (susp-pdb-foc-ty pdb)
                               (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                                                    (cong liftTerm (susp-pdb-foc-tm pdb)))
                                             (trans (suspLiftTy (getFocusType pdb))
                                                    (cong liftType (susp-pdb-foc-ty pdb)))
                                             refl))
susp-pdb-foc-ty (Restr pdb)
  = trans (susp-base-compat (getFocusType pdb))
          (cong ty-base (susp-pdb-foc-ty pdb))

susp-pd : Γ ⊢pd₀ d → suspCtx Γ ⊢pd₀ suc d
susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb))
