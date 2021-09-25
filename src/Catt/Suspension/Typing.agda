{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Suspension.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Data.Fin.Properties using (toℕ-inject₁)
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (drop)
open import Data.Bool
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty
open P index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule

suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

suspTyEq : A ≈[ Γ ]ty B → suspTy A ≈[ suspCtx Γ ]ty suspTy B
suspTmEq : s ≈[ Γ ]tm t → suspTm s ≈[ suspCtx Γ ]tm suspTm t
suspSubEq : σ ≈[ Γ ]s τ → suspSub σ ≈[ suspCtx Γ ]s suspSub τ

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {T : Tree n} → supp-condition b A T → supp-condition b (suspTy A) (suspTree T)
suspSuppCondition {b = false} {A} {T} sc = begin
  FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
  suspSupp (FVTy A) ≡⟨ cong suspSupp sc ⟩
  suspSupp full ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {T@(Join S₁ S₂)} (sc1 ,, sc2) = l1 ,, l2
  where
    open ≡-Reasoning
    suc-pred : (n : ℕ) → zero ≢ n → suc (pred n) ≡ n
    suc-pred zero p = ⊥-elim (p refl)
    suc-pred (suc n) p = refl

    l1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (tree-dim T) (suspTree T) false
    l1 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T) (join-tree-has-non-zero-dim S₁ S₂)) ⟩
      supp-bd (tree-dim T) (suspTree T) false ∎

    l2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (tree-dim T) (suspTree T) true
    l2 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T) (join-tree-has-non-zero-dim S₁ S₂)) ⟩
      supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ , A} (TyVarZ {Γ = .(Γ , A)} x) = TyVarZ (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift A))) (suspTyEq x))
suspTmTy (TyVarS i tvi x) = TyVarS (inject₁ (inject₁ i)) (suspTmTy tvi) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift _))) (suspTyEq x))
suspTmTy (TyCoh Aty σty b sc p) = TyCoh (suspTyTy Aty) (suspSubTy σty) b (suspSuppCondition sc) (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq p))


-- suspTmTy (TyComp {T = T} {s = s} {A = A} {t = t} {σ = σ} p q r x y) = TyComp (suspTyTy p) (suspSubTy q) lem1 lem2 (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty σ (s ─⟨ A ⟩⟶ t)))) (suspTyEq y))
--   where
--     open ≡-Reasoning
--

--     lem1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false
--     lem1 = begin
--       FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
--       suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp r ⟩
--       suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
--       supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
--       supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false ∎

--     lem2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true
--     lem2 = begin
--       FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
--       suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp x ⟩
--       suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
--       supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
--       supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

suspSubTy (TyNull x) = TyExt (TyExt (TyNull TyStar) getFstTy) getSndTy
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
suspTmEq (Rule≈ i a tc) = susp-rule i a (suspTmTy tc)

suspSubEq (Null≈ x) = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)

unrestrictTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) Δ (unrestrict σ)
unrestrictTy (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) p) r
unrestrictTy (TyExt σty x) = TyExt (unrestrictTy σty) (term-conversion x (reflexive≈ty (unrestrict-comp-ty _ _)))

unrestrictEq : σ ≈[ Δ ]s τ → unrestrict σ ≈[ Δ ]s unrestrict τ
unrestrictEq (Null≈ (Arr≈ p q r)) = Ext≈ (Ext≈ (Null≈ q) p) r
unrestrictEq (Ext≈ eq x) = Ext≈ (unrestrictEq eq) x
