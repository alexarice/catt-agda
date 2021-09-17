{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Support where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Data.Nat
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Support
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool using (Bool; true; false)
open import Tactic.MonoidSolver
open import Data.Nat.Properties

supp-unbiased : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d) → FVTy (unbiased-type d T) ∪ FVTm (unbiased-term d T) ≡ full
supp-unbiased zero Sing p = refl
supp-unbiased zero (Join S T) p with .(join-tree-has-non-zero-dim S T (sym p))
... | ()
supp-unbiased {n} (suc d) T p with is-linear-dec T
... | yes q = trans (cong (_∪ ewt empty) l1) (linear-tree-supp-lem d T ⦃ q ⦄ p)
  where
    open ≡-Reasoning
    l2 : (b : Bool) → FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T b ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) ≡ supp-bd d T b
    l2 b = begin
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T b ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty (unbiased-type d (tree-bd d T)) (tree-inc d T b)) (TransportVarSet-tm (unbiased-term d (tree-bd d T)) (tree-inc d T b)) ⟩
      TransportVarSet (FVTy (unbiased-type d (tree-bd d T))) (tree-inc d T b)
      ∪ TransportVarSet (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
        ≡˘⟨ TransportVarSet-∪ (FVTy (unbiased-type d (tree-bd d T))) (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b) ⟩
      TransportVarSet (FVTy (unbiased-type d (tree-bd d T)) ∪ FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
        ≡⟨ cong (λ - → TransportVarSet - (tree-inc d T b)) (supp-unbiased d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) (≤-reflexive (sym p))))) ⟩
      TransportVarSet full (tree-inc d T b) ≡⟨ TransportVarSet-full (tree-inc d T b) ⟩
      FVSub (tree-inc d T b) ≡⟨ supp-bd-compat d T b ⟩
      supp-bd d T b ∎

    l3 : FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡ supp-bd d T true
    l3 = begin
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)
        ≡˘⟨ cong (λ - → FVTy - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)) (≃ty-to-≡ (unbiased-type-inc-lem d T)) ⟩
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T true ]ty) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)
        ≡⟨ l2 true ⟩
      supp-bd d T true ∎

    l1 : FVTy (unbiased-type (suc d) T) ≡ supp-bd d T false ∪ supp-bd d T true
    l1 = begin
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)
        ≡˘⟨ cong (λ - → - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
                       ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm))
                       (∪-idem (FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty))) ⟩
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ solve (∪-monoid {suc n}) ⟩
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ (FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm))
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ cong (λ - → FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty) ∪ - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)) (∪-comm _ _) ⟩
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ (FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
      ∪ FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty))
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ solve (∪-monoid {suc n}) ⟩
      (FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm))
      ∪ (FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm))
        ≡⟨ cong₂ _∪_ (l2 false) l3 ⟩
      supp-bd d T false ∪ supp-bd d T true ∎


... | no q = begin
  FVTy (unbiased-type (suc d) T) ∪ FVSub (idSub _) ≡⟨ cong (FVTy (unbiased-type (suc d) T) ∪_) (idSub-supp (suc _)) ⟩
  FVTy (unbiased-type (suc d) T) ∪ full ≡⟨ ∪-right-zero (FVTy (unbiased-type (suc d) T)) ⟩
  full ∎
  where
    open ≡-Reasoning
