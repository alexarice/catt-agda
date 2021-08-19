{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ)
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)
open import Relation.Binary.PropositionalEquality

getFst-is-Fst : getFst {Γ = Γ} ≃tm Var {Γ = suspCtx Γ} (fromℕ _)
getFst-is-Fst {Γ = ∅} = Var≃ refl
getFst-is-Fst {Γ = Γ , A} = lift-tm-≃ getFst-is-Fst

susp-ty-lift : (B : Ty Γ d) → suspTy (liftType {A = A} B) ≃ty liftType {A = suspTy A} (suspTy B)
susp-tm-lift : (t : Tm Γ d) → suspTm (liftTerm {A = A} t) ≃tm liftTerm {A = suspTy A} (suspTm t)
susp-sub-lift : (σ : Sub Δ Γ) → suspSub (liftSub {A = A} σ) ≃s liftSub {A = suspTy A} (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm Star≃ refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A x σ) = Coh≃ refl≃c refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ Null≃ refl≃tm) refl≃tm
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

lookupSusp-is-inject : (i : Fin (ctxLength Γ)) → lookupSusp {Γ = Γ} i ≃tm Var {Γ = suspCtx Γ} (inject₁ (inject₁ i))
lookupSusp-is-inject {Γ = Γ , A} zero = Var≃ refl
lookupSusp-is-inject {Γ = Γ , A} (suc i) = lift-tm-≃ (lookupSusp-is-inject i)

susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
susp-ty-≃ : {A : Ty Γ d} {B : Ty Δ d′} → Γ ≃c Δ → A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : {s : Tm Γ d} {t : Tm Δ d′} → Γ ≃c Δ → s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : {σ : Sub Γ Δ} {τ : Sub Γ′ Δ′} → Δ ≃c Δ′ → σ ≃s τ → suspSub σ ≃s suspSub τ

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ p q)

susp-ty-≃ p Star≃ with ≃c-preserve-len p
... | refl with ≃c-to-≡ p
... | refl = refl≃ty
susp-ty-≃ p (Arr≃ q r s) = Arr≃ (susp-tm-≃ p q) (susp-ty-≃ p r) (susp-tm-≃ p s)

susp-tm-≃ _ (Var≃ q) = trans≃tm (lookupSusp-is-inject _) (trans≃tm (Var≃ (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))) (sym≃tm (lookupSusp-is-inject _)))
susp-tm-≃ p (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ q r) (susp-sub-≃ p s)

susp-sub-≃ p Null≃ with ≃c-preserve-len p
... | refl with ≃c-to-≡ p
... | refl = refl≃s
susp-sub-≃ p (Ext≃ r s) = Ext≃ (susp-sub-≃ p r) (susp-tm-≃ p s)

susp-fst-var : (σ : Sub Γ Δ) → Var (fromℕ _) [ suspSub σ ]tm ≃tm Var {Γ = suspCtx Δ} (fromℕ _)
susp-fst-var ⟨⟩ = getFst-is-Fst
susp-fst-var ⟨ σ , t ⟩ = susp-fst-var σ

susp-sub-preserve-getFst : {Γ : Ctx n} → {Δ : Ctx m} → (σ : Sub Γ Δ) → getFst {Γ = Δ} ≃tm getFst [ suspSub σ ]tm
susp-sub-preserve-getFst ⟨⟩ = refl≃tm
susp-sub-preserve-getFst ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getFst σ) (sym≃tm (lift-sub-comp-lem-tm (suspSub σ) getFst))

susp-sub-preserve-getSnd : {Γ : Ctx n} → {Δ : Ctx m} → (σ : Sub Γ Δ) → getSnd {Γ = Δ} ≃tm getSnd [ suspSub σ ]tm
susp-sub-preserve-getSnd ⟨⟩ = refl≃tm
susp-sub-preserve-getSnd ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getSnd σ) (sym≃tm (lift-sub-comp-lem-tm (suspSub σ) getSnd))

susp-functorial : (σ : Sub Δ Υ) → (τ : Sub Γ Δ) → suspSub (σ ∘ τ) ≃s suspSub σ ∘ suspSub τ
susp-functorial-tm : (σ : Sub Δ Υ) → (t : Tm Δ d) → suspTm (t [ σ ]tm) ≃tm suspTm t [ suspSub σ ]tm
susp-functorial-ty : (σ : Sub Δ Υ) → (A : Ty Δ d) → suspTy (A [ σ ]ty) ≃ty suspTy A [ suspSub σ ]ty

susp-functorial σ ⟨⟩ = Ext≃ (Ext≃ Null≃ (susp-sub-preserve-getFst σ)) (susp-sub-preserve-getSnd σ)
susp-functorial σ ⟨ τ , t ⟩ = Ext≃ (susp-functorial σ τ) (susp-functorial-tm σ t)

susp-functorial-tm σ (Var i) = lem σ i
  where
    lem : {Γ : Ctx n} → (σ : Sub Γ Δ) → (i : Fin (ctxLength Γ)) → suspTm (Var i [ σ ]tm) ≃tm (lookupSusp i [ suspSub σ ]tm)
    lem ⟨ σ , t ⟩ zero = refl≃tm
    lem ⟨ σ , t ⟩ (suc i) = trans≃tm (lem σ i) (sym≃tm (lift-sub-comp-lem-tm (suspSub σ) (lookupSusp i)))
susp-functorial-tm σ (Coh Δ A x τ) = Coh≃ refl≃c refl≃ty (susp-functorial σ τ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-getFst σ) Star≃ (susp-sub-preserve-getSnd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

susp-functorial-id : (Γ : Ctx n) → suspSub (idSub Γ) ≃s idSub (suspCtx Γ)
susp-functorial-id ∅ = Ext≃ (Ext≃ Null≃ (Var≃ refl)) (Var≃ refl)
susp-functorial-id (Γ , A) = Ext≃ (trans≃s (susp-sub-lift (idSub Γ)) (lift-sub-≃ (susp-functorial-id Γ))) (Var≃ refl)
