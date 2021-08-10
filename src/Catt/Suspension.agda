{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
open import Catt.Pasting
open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns
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

getFst {Γ = ∅} = Var 1F
getFst {Γ = Γ , A} = liftTerm getFst

getSnd {Γ = ∅} = Var 0F
getSnd {Γ = Γ , A} = liftTerm getSnd

suspTm (Var i) = lookupSusp i
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

lookupSusp {Γ = Γ , A} 0F = Var 0F
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
suspLiftTy {A = A} (s ─⟨ B ⟩⟶ t)
  rewrite suspLiftTm {A = A} s
  rewrite suspLiftTm {A = A} t
  rewrite suspLiftTy {A = A} B = refl
suspLiftTm (Var i) = refl
suspLiftTm {A = A} (Coh Δ B σ)
  rewrite suspLiftSub {A = A} σ = refl
suspLiftSub ⟨⟩ = refl
suspLiftSub {A = A} ⟨ σ , t ⟩
  rewrite suspLiftSub {A = A} σ
  rewrite suspLiftTm {A = A} t = refl

susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≡ getFocusType (susp-pdb pdb)
susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≡ getFocusTerm (susp-pdb pdb)

susp-pdb Base = ExtendM Base
susp-pdb (ExtendM pdb)
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = ExtendM (susp-pdb pdb)
susp-pdb (Extend pdb)
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = Extend (susp-pdb pdb)
susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

susp-pdb-foc-tm Base = refl
susp-pdb-foc-tm (ExtendM pdb)
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = refl
susp-pdb-foc-tm (Extend pdb)
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = refl
susp-pdb-foc-tm (Restr pdb)
  rewrite susp-tgt-compat (getFocusType pdb)
  rewrite susp-pdb-foc-ty pdb
  = refl

susp-pdb-foc-ty Base = refl
susp-pdb-foc-ty (ExtendM pdb)
  rewrite suspLiftTy {A = liftTerm {A = getFocusType pdb} (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F} (liftType (getFocusType pdb))
  rewrite suspLiftTm {A = liftTerm {A = getFocusType pdb} (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F} (liftTerm (getFocusTerm pdb))
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = refl
susp-pdb-foc-ty (Extend pdb)
  rewrite suspLiftTy {A = liftTerm {A = getFocusType pdb} (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F} (liftType (getFocusType pdb))
  rewrite suspLiftTm {A = liftTerm {A = getFocusType pdb} (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F} (liftTerm (getFocusTerm pdb))
  rewrite suspLiftTm {A = getFocusType pdb} (getFocusTerm pdb)
  rewrite suspLiftTy {A = getFocusType pdb} (getFocusType pdb)
  rewrite susp-pdb-foc-tm pdb
  rewrite susp-pdb-foc-ty pdb
  = refl
susp-pdb-foc-ty (Restr pdb)
  rewrite susp-base-compat (getFocusType pdb)
  rewrite susp-pdb-foc-ty pdb
  = refl
