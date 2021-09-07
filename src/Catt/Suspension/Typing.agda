{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base

module Catt.Suspension.Typing (Index : Set) (rule : Index → Rule) (props : (i : Index) → Catt.Typing.Properties.Base.Props Index rule i) where

open import Catt.Typing Index rule
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Catt.Typing.Properties Index rule props
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Relation.Binary.PropositionalEquality

suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
-- suspLookupTy : {Γ : Ctx n} → (i : Fin (ctxLength Γ)) → Typing-Tm (suspCtx Γ) (lookupSusp i) (suspTy (Γ ‼ i))
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

suspCtxEq : Γ ≈c Δ → suspCtx Γ ≈c suspCtx Δ
suspTyEq : A ≈ty B → suspTy A ≈ty suspTy B
suspTmEq : s ≈tm t → suspTm s ≈tm suspTm t
suspSubEq : σ ≈s τ → suspSub σ ≈s suspSub τ

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ} (TyVar i x) = TyVar (inject₁ (inject₁ i)) (trans≈ty (reflexive≈ty (susp-‼ Γ i)) (suspTyEq x))
suspTmTy (TyCoh p q r s t) = TyCoh (susp-pd p) (suspTyTy q) (suspSubTy r) {!!} (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq t))
suspTmTy (TyComp {s = s} {A = A} {t = t} {σ = σ} pd p q r x y) = TyComp (susp-pd pd) (suspTyTy p) (suspSubTy q) {!!} {!!} (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty σ (s ─⟨ A ⟩⟶ t)))) (suspTyEq y))

suspSubTy TyNull = TyExt (TyExt TyNull TyStar getFstTy) TyStar getSndTy
suspSubTy (TyExt p q r) = TyExt (suspSubTy p) (suspTyTy q) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVar (suc zero) (Star≈ refl)
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVar zero (Star≈ refl)
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

suspCtxEq Emp≈ = refl≈c
suspCtxEq (Add≈ eq x) = Add≈ (suspCtxEq eq) (suspTyEq x)

suspTyEq (Star≈ refl) = refl≈ty

suspTyEq (Arr≈ q r s) = Arr≈ (suspTmEq q) (suspTyEq r) (suspTmEq s)

suspTmEq (Var≈ x y) = Var≈ (cong suc (cong suc x)) (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ y ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning
suspTmEq (Sym≈ eq) = Sym≈ (suspTmEq eq)
suspTmEq (Trans≈ eq eq′) = Trans≈ (suspTmEq eq) (suspTmEq eq′)
suspTmEq (Coh≈ p q r) = Coh≈ (suspCtxEq p) (suspTyEq q) (suspSubEq r)
suspTmEq (Rule≈ i a tct eqt) = props i .susp-rule a (λ j → suspTmTy (tct j)) (λ j → suspTmEq (eqt j))

suspSubEq (Null≈ refl) = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)
