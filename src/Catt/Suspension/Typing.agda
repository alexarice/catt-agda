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
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst Γ) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd Γ) ⋆

suspCtxEq : Γ ≈c Δ → suspCtx Γ ≈c suspCtx Δ
suspTyEq : A ≈ty B → suspTy A ≈ty suspTy B
suspTmEq : s ≈tm t → suspTm s ≈tm suspTm t

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ} (TyVar i x) = TyVar (inject₁ (inject₁ i)) (trans≈ty (reflexive≈ty (susp-‼ _ i)) (suspTyEq (refl≈c {Γ = Γ}) x))
-- term-conversion (suspLookupTy i) {!!}
suspTmTy (TyCoh p q r s t) = TyCoh (susp-pd p) (suspTyTy q) (suspSubTy r) {!!} {!!}
suspTmTy (TyComp pd p q r s t) = TyComp (susp-pd pd) (suspTyTy p) (suspSubTy q) {!!} {!!} {!!}

suspSubTy TyNull = TyExt (TyExt TyNull TyStar getFstTy) TyStar getSndTy
suspSubTy (TyExt p q r) = TyExt (suspSubTy p) (suspTyTy q) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVar (suc zero) Star≈
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVar zero Star≈
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

suspCtxEq Emp≈ = refl≈c
suspCtxEq (Add≈ eq x) = Add≈ (suspCtxEq eq) (suspTyEq eq x)

suspTyEq p Star≈ = Arr≈ (Var≈ (cong (λ - → suc (toℕ (fromℕ -))) (≈c-preserve-len p)))
                        Star≈
                        (Var≈ (cong (λ - → toℕ (inject₁ (fromℕ -))) (≈c-preserve-len p)))
suspTyEq p (Arr≈ q r s) = Arr≈ (suspTmEq p q) (suspTyEq p r) (suspTmEq p s)

suspTmEq p (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning
suspTmEq p (Sym≈ eq) = Sym≈ (suspTmEq (sym≈c p) eq)
suspTmEq p (Trans≈ eq eq₁) = Trans≈ (suspTmEq {!!} eq) {!!}
suspTmEq p (Coh≈ x x₁ x₂) = {!!}
suspTmEq p (Rule≈ i a tct₁ eqt) = {!!}
