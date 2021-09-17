{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Insertion.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; fromℕ)

exterior-sub-fst-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                     → Var {suc (insertion-tree-size S P T)} (fromℕ _) ≃tm Var (fromℕ _) [ exterior-sub S P T ]tm
exterior-sub-fst-var (Join S₁ S₂) PHere T = begin
  < Var (fromℕ (insertion-tree-size (Join S₁ S₂) PHere T)) >tm
    ≈˘⟨ idSub≃-fst-var (sym≃c (connect-tree-to-ctx T S₂)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (sub-between-connects-fst-var (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))) ∘ idSub≃ (linear-tree-compat (suspTree S₁))) getSnd (idSub (suc _)) (tree-last-var T) lem) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))}) ⟩
  < Var (fromℕ _)
    [ sub-between-connects (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))) ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           getSnd
                           (idSub (suc _))
                           (tree-last-var T) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm
    >tm
    ≈˘⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub _)) ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           getSnd
                           (idSub _)
                           (tree-last-var T)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub _)) ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           getSnd
                           (idSub _)
                           (tree-last-var T) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm ∎
  where
    open Reasoning tm-setoid

    lem : Var (fromℕ _)
            [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
             ∘ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm
            ≃tm Var (fromℕ _)
    lem = begin
      < Var (fromℕ _)
          [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
            ∘ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm >tm
        ≈⟨ assoc-tm _ (idSub≃ (linear-tree-compat (suspTree S₁))) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm
          [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))) ]tm >tm
        ≈⟨ sub-action-≃-tm (idSub≃-fst-var (linear-tree-compat (suspTree S₁))) refl≃s ⟩
      < Var (fromℕ _)
          [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))) ]tm >tm
        ≈⟨ unbiased-type-disc-lem (suc (tree-dim S₁)) T (sym it) ⟩
      < Var (fromℕ (tree-size T)) >tm ∎

exterior-sub-fst-var (Join S₁ S₂) (PExt P) (Join T Sing) = sym≃tm (sub-between-connect-susps-fst-var (exterior-sub S₁ P T ⦃ p = cong pred it ⦄) (idSub _))

exterior-sub-fst-var (Join S₁ S₂) (PShift P) T = sym≃tm (sub-between-connect-susps-fst-var (idSub _) (exterior-sub S₂ P T))
