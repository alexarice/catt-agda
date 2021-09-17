{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Suspension.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Data.Fin.Properties using (toℕ-inject₁)
open import Catt.Typing.Properties index rule props
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (drop)
open import Data.Bool

suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

-- suspCtxEq : Γ ≈c Δ → suspCtx Γ ≈c suspCtx Δ
suspTyEq : A ≈[ Γ ]ty B → suspTy A ≈[ suspCtx Γ ]ty suspTy B
suspTmEq : s ≈[ Γ ]tm t → suspTm s ≈[ suspCtx Γ ]tm suspTm t
suspSubEq : σ ≈[ Γ ]s τ → suspSub σ ≈[ suspCtx Γ ]s suspSub τ

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ , A} (TyVarZ {Γ = .(Γ , A)} x) = TyVarZ (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift A))) (suspTyEq x))
suspTmTy (TyVarS i tvi x) = TyVarS (inject₁ (inject₁ i)) (suspTmTy tvi) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift _))) (suspTyEq x))
suspTmTy (TyCoh {A = A} q r s t) = TyCoh (suspTyTy q) (suspSubTy r) (lem) (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq t))
  where
    open ≡-Reasoning
    lem : FVTy (suspTy A) ≡ full
    lem = begin
      FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
      suspSupp (FVTy A) ≡⟨ cong suspSupp s ⟩
      suspSupp full ≡⟨ suspSuppFull ⟩
      full ∎

suspTmTy (TyComp {T = T} {s = s} {A = A} {t = t} {σ = σ} p q r x y) = TyComp (suspTyTy p) (suspSubTy q) lem1 lem2 (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty σ (s ─⟨ A ⟩⟶ t)))) (suspTyEq y))
  where
    open ≡-Reasoning
    suc-pred : (n : ℕ) → .⦃ NonZero′ n ⦄ → suc (pred n) ≡ n
    suc-pred (suc n) = refl

    lem1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false
    lem1 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp r ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
      supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false ∎

    lem2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true
    lem2 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp x ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
      supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

suspSubTy TyNull = TyExt (TyExt TyNull getFstTy) getSndTy
suspSubTy (TyExt p r) = TyExt (suspSubTy p) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVarS zero (TyVarZ Star≈) Star≈
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVarZ Star≈
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

-- suspCtxEq Emp≈ = refl≈c
-- suspCtxEq (Add≈ eq x) = Add≈ (suspCtxEq eq) (suspTyEq x)

suspTyEq Star≈ = refl≈ty

suspTyEq (Arr≈ q r s) = Arr≈ (suspTmEq q) (suspTyEq r) (suspTmEq s)

suspTmEq (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning
suspTmEq (Sym≈ eq) = Sym≈ (suspTmEq eq)
suspTmEq (Trans≈ eq eq′) = Trans≈ (suspTmEq eq) (suspTmEq eq′)
suspTmEq (Coh≈ q r) = Coh≈ (suspTyEq q) (suspSubEq r)
suspTmEq (Rule≈ i a eqt tc) = props i .susp-rule a (λ j → suspTmEq (eqt j)) (suspTmTy tc)

suspSubEq Null≈ = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)
