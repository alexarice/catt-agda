{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Insertion.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Globular

branching-path-to-var-is-var : (S : Tree n) → (P : Path S) → .⦃ _ : is-branching-path P ⦄ → isVar (branching-path-to-var S P)
branching-path-to-var-is-var (Join S T) PHere = var-to-var-comp-tm 0V (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
branching-path-to-var-is-var (Join S T) (PExt P) = var-to-var-comp-tm (suspTm (branching-path-to-var S P)) ⦃ suspTm-var (branching-path-to-var S P) ⦃ branching-path-to-var-is-var S P ⦄ ⦄ (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
branching-path-to-var-is-var (Join S T) (PShift P) = var-to-var-comp-tm (branching-path-to-var T P) ⦃ branching-path-to-var-is-var T P ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄

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
    ≈˘⟨ sub-action-≃-tm (sub-between-connects-fst-var (sub-from-linear-tree-unbiased (suspTree S₁) T 0) idSub (tree-last-var T) (sym≃tm (unrestrict-fst (sub-from-linear-tree-unbiased S₁ T 1)))) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))}) ⟩
  < Var (fromℕ _)
    [ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm
    >tm
    ≈˘⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-fst-var (Join S₁ S₂) (PExt P) (Join T Sing) = sym≃tm (sub-between-connect-susps-fst-var (exterior-sub S₁ P T) idSub)

exterior-sub-fst-var (Join S₁ S₂) (PShift P) T = sym≃tm (sub-between-connect-susps-fst-var idSub (exterior-sub S₂ P T))

exterior-sub-last-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                     → tree-last-var (insertion-tree S P T) ≃tm tree-last-var S [ exterior-sub S P T ]tm
exterior-sub-last-var (Join S₁ S₂) PHere T = begin
  < tree-last-var (connect-tree T S₂) >tm
    ≈⟨ connect-tree-last-var T S₂ ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ connect-inc-right (tree-last-var T) (tree-size S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (id-right-unit (connect-inc-right (tree-last-var T) (tree-size S₂))) refl≃s) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ (connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (sub-between-connects-inc-right (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd idSub (tree-last-var T) (sym≃tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1))) (id-on-tm (Var (fromℕ _)))) refl≃s) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
      ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (∘-assoc _ _ _) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-last-var (Join S₁ S₂) (PExt P) (Join T Sing) = begin
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size (insertion-tree S₁ P T)) (tree-size S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (id-right-unit (connect-susp-inc-right (insertion-tree-size S₁ P T) _)) ⟩
  < tree-last-var S₂ [ connect-susp-inc-right (insertion-tree-size S₁ P T) _
                     ∘ idSub ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-between-connect-susps-inc-right (exterior-sub S₁ P T) idSub (id-on-tm (Var (fromℕ _)))) ⟩
  < tree-last-var S₂
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub ]tm >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-last-var (Join S₁ S₂) (PShift P) T = begin
  < tree-last-var (insertion-tree S₂ P T)
    [ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (exterior-sub-last-var S₂ P T) refl≃s ⟩
  < tree-last-var S₂ [ exterior-sub S₂ P T ]tm
                     [ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
    ∘ exterior-sub S₂ P T ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-between-connect-susps-inc-right idSub (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < tree-last-var S₂
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T) ]tm >tm ∎
  where
    open Reasoning tm-setoid


insertion-eq : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
             → branching-path-to-var S P [ exterior-sub S P T ]tm ≃tm Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S P T)
insertion-eq (Join S₁ S₂) PHere T = begin
  < 0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
       [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) 0V ⟩
  < 0V [ exterior-sub (Join S₁ S₂) PHere T
       ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (∘-assoc _ _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂))) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
         ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (sub-action-≃-sub (sub-between-connects-inc-left (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd idSub (tree-last-var T)) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))})) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0)) ⟩
  < 0V [ connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm >tm
    ≈⟨ assoc-tm (connect-inc-left (tree-last-var T) _) (sub-from-linear-tree-unbiased (suspTree S₁) T 0) 0V ⟩
  < 0V [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
       [ connect-inc-left (tree-last-var T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (sub-from-linear-tree-unbiased-0V (suspTree S₁) T 0) refl≃s ⟩
  < unbiased-comp (tree-dim (suspTree S₁)) T [ connect-inc-left (tree-last-var T) _ ]tm >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim (suspTree S₁)) T) (connect-inc-left (tree-last-var T) _ ∘ idSub) >tm
    ≈⟨ Coh≃ refl≃c (unbiased-type-≃ (trans (max-lem (suc (tree-dim S₁))) (recompute (suc (tree-dim S₁) ≟ tree-dim T) it)) refl≃) lem ⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T)
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       connect-inc-left (tree-last-var T) _) >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) PHere T) >tm ∎
  where
    lem : connect-inc-left (tree-last-var T) _ ∘ idSub
          ≃s idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
    lem = begin
      < connect-inc-left (tree-last-var T) _ ∘ idSub >s
        ≈⟨ id-right-unit (connect-inc-left (tree-last-var T) _) ⟩
      < connect-inc-left (tree-last-var T) _ >s
        ≈˘⟨ idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _) ⟩
      < idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _ >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid

insertion-eq (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = let
  instance .x : _
           x = cong pred p
  in begin
  < suspTm (branching-path-to-var S₁ P)
    [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub
    ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P)}) (sub-between-connect-susps-inc-left (exterior-sub S₁ P T) idSub) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _
    ∘ suspSub (exterior-sub S₁ P T) ]tm
    >tm
    ≈⟨ assoc-tm _ _ (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ suspSub (exterior-sub S₁ P T) ]tm
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-functorial-tm (exterior-sub S₁ P T) (branching-path-to-var S₁ P)) refl≃s ⟩
  < suspTm (branching-path-to-var S₁ P [ exterior-sub S₁ P T ]tm)
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (insertion-eq S₁ P T ⦃ p = trans x (max-lem (tree-dim T)) ⦄)) refl≃s ⟩
  < suspTm (Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S₁ P T))
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ Coh≃ refl≃c (trans≃ty (susp-ty-≃ (unbiased-type-≃ (sym (max-lem (tree-dim T))) refl≃)) (unbiased-type-susp-lem (max (tree-dim T) (pred (tree-dim Sing))) T)) refl≃s ⟩
  < Coh (suspCtx (tree-to-ctx T)) (unbiased-type (tree-dim (Join T Sing)) (Join T Sing)) (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) >tm ∎
  where
    open Reasoning tm-setoid

insertion-eq (Join S₁ S₂) (PShift P) T = begin
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P}) (sub-between-connect-susps-inc-right idSub (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
    ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P [ exterior-sub S₂ P T ]tm
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (insertion-eq S₂ P T) refl≃s ⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S₂ P T)
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) (PShift P) T) >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-susp : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → exterior-sub (suspTree S) (PExt P) (suspTree T) ≃s suspSub (exterior-sub S P T)
exterior-sub-susp S P T = begin
  < exterior-sub (suspTree S) (PExt P) (suspTree T) >s ≡⟨⟩
  < idSub ∘ suspSub (exterior-sub S P T) >s
    ≈⟨ id-left-unit (suspSub (exterior-sub S P T)) ⟩
  < suspSub (exterior-sub S P T) >s ∎
    where
      open Reasoning sub-setoid

{-
insertion-var-split-compat : (S : Tree n)
                           → (P : Path S)
                           → .⦃ bp : is-branching-path P ⦄
                           → (T : Tree m)
                           → .⦃ lh : has-linear-height (path-length P) T ⦄
                           → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                           → VarSplitCompat (exterior-sub S P T) (interior-sub S P T) (insertion-var-split S P T)
insertion-var-split-compat (Join S₁ S₂) PHere T i with connect-var-split (tree-size T) (tree-size S₂) (idSub≃-func (connect-tree-to-ctx T S₂) i) | connect-var-split-compat (tree-last-var T) (tree-size S₂) (idSub≃-func (connect-tree-to-ctx T S₂) i)
... | inj₁ j | p = let
  instance _ = idSub≃-var-to-var (connect-tree-to-ctx T S₂)
  in begin
  < Var j [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
          ∘ connect-inc-left (tree-last-var T) _ ]tm >tm
    ≈⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (connect-inc-left (tree-last-var T) _) (Var j) ⟩
  < Var j [ connect-inc-left (tree-last-var T) _ ]tm
          [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < Var (varToVarFunction (idSub≃ (connect-tree-to-ctx T S₂)) i)
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (idSub≃ (connect-tree-to-ctx T S₂)) i) refl≃s ⟩
  < Var i [ idSub≃ (connect-tree-to-ctx T S₂) ]tm
          [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var i) ⟩
  < Var i [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ idSub≃ (connect-tree-to-ctx T S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var i}) (idSub≃-functorial (connect-tree-to-ctx T S₂) (sym≃c (connect-tree-to-ctx T S₂))) ⟩
  < Var i [ idSub≃ (trans≃c (connect-tree-to-ctx T S₂) (sym≃c (connect-tree-to-ctx T S₂))) ]tm >tm
    ≈⟨ idSub≃-on-tm (trans≃c (connect-tree-to-ctx T S₂) (sym≃c (connect-tree-to-ctx T S₂))) (Var i) ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ j | p = let
  instance _ = connect-susp-inc-right-var-to-var (tree-size S₁) (tree-size S₂)
           _ = idSub≃-var-to-var (connect-tree-to-ctx T S₂)
  in begin
  < Var (varToVarFunction (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) j) [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) j) refl≃s ⟩
  < Var j [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
          [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ exterior-sub (Join S₁ S₂) PHere T
          ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (∘-assoc _ _ (connect-susp-inc-right _ _)) ⟩
  < Var j [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
          ∘ (sub-between-connects (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
                                  ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                                  getSnd
                                  (idSub _)
                                  (tree-last-var T)
          ∘ connect-susp-inc-right _ _) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-action-≃-sub (sub-between-connects-inc-right (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
                                  ∘ idSub≃ (linear-tree-compat (suspTree S₁))) getSnd (idSub _) (tree-last-var T) lem (id-on-tm (Var (fromℕ _)))) refl≃s) ⟩
  < Var j [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
          ∘ (connect-inc-right (tree-last-var T) _ ∘ idSub (suc _)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-action-≃-sub (id-right-unit (connect-inc-right (tree-last-var T) _)) refl≃s) ⟩
  < Var j [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
          ∘ connect-inc-right (tree-last-var T) _ ]tm >tm
    ≈⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ connect-inc-right (tree-last-var T) _ ]tm
          [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < Var (varToVarFunction (idSub≃ (connect-tree-to-ctx T S₂)) i)
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (idSub≃ (connect-tree-to-ctx T S₂)) i) refl≃s ⟩
  < Var i [ idSub≃ (connect-tree-to-ctx T S₂) ]tm
          [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var i) ⟩
  < Var i [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
          ∘ idSub≃ (connect-tree-to-ctx T S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var i}) (idSub≃-functorial (connect-tree-to-ctx T S₂) (sym≃c (connect-tree-to-ctx T S₂))) ⟩
  < Var i [ idSub≃ (trans≃c (connect-tree-to-ctx T S₂) (sym≃c (connect-tree-to-ctx T S₂))) ]tm >tm
    ≈⟨ idSub≃-on-tm (trans≃c (connect-tree-to-ctx T S₂)
                      (sym≃c (connect-tree-to-ctx T S₂))) (Var i) ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
    lem : getSnd [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
             ∘ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm
          ≃tm tree-last-var T
    lem = begin
      < getSnd [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
               ∘ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm >tm
        ≈⟨ assoc-tm _ (idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁)))) getSnd ⟩
      < getSnd [ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm
               [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))) ]tm >tm
        ≈⟨ sub-action-≃-tm {t = getSnd} (idSub≃-snd-var (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁)))) refl≃s ⟩
      < getSnd [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))]tm >tm
        ≈⟨ unbiased-type-disc-lem-2 (tree-dim S₁) T (sym it) ⟩
      < tree-last-var T >tm ∎

insertion-var-split-compat (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p′ ⦄ i with connect-var-split (2 + insertion-tree-size S₁ P T) (tree-size S₂) i | connect-var-split-compat getSnd (tree-size S₂) i
... | inj₂ j | p = let
  instance _ = connect-susp-inc-right-var-to-var (tree-size S₁) (tree-size S₂)
           .x : _
           x = cong pred p′
  in begin
  < Var (varToVarFunction (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) j)
        [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) j) refl≃s ⟩
  < Var j [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
          [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub (suc _))
          ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-between-connect-susps-inc-right (exterior-sub S₁ P T) (idSub _) (id-on-tm (Var (fromℕ _)))) ⟩
  < Var j [ connect-susp-inc-right (insertion-tree-size S₁ P T) _
          ∘ idSub (suc _) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ idSub _ ]tm
          [ connect-susp-inc-right (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (id-on-tm (Var j)) refl≃s ⟩
  < Var j [ connect-susp-inc-right (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₁ j | p with susp-var-split (insertion-var-split S₁ P T) j | susp-var-split-compat (insertion-var-split-compat S₁ P T ⦃ p = cong pred p′ ⦄) j
... | inj₁ k | q = let
  instance _ = connect-susp-inc-left-var-to-var (tree-size S₁) (tree-size S₂)
           .x : _
           x = cong pred p′
  in begin
  < Var (varToVarFunction (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) k)
    [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) k) refl≃s ⟩
  < Var k [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub (suc _)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _)
          ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k}) (sub-between-connect-susps-inc-left (exterior-sub S₁ P T) (idSub _)) ⟩
  < Var k [ connect-susp-inc-left (insertion-tree-size S₁ P T) _
          ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ suspSub (exterior-sub S₁ P T) ]tm
          [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ k | q = begin
  < Var k [ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
          ∘ suspSub (interior-sub S₁ P T) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ suspSub (interior-sub S₁ P T) ]tm
          [ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid

insertion-var-split-compat (Join S₁ S₂) (PShift P) T i with connect-var-split-right getSnd (insertion-tree-size S₂ P T) i | connect-var-split-right-compat getSnd (insertion-tree-size S₂ P T) i
... | inj₁ j | p = let
  instance _ = connect-susp-inc-left-var-to-var (tree-size S₁) (tree-size S₂)
  in begin
  < Var (varToVarFunction (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) j) [ exterior-sub (Join S₁ S₂) (PShift P) T ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) j) refl≃s ⟩
  < Var j [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
          [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T)
          ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-between-connect-susps-inc-left (idSub _) (exterior-sub S₂ P T)) ⟩
  < Var j [ connect-susp-inc-left _ (insertion-tree-size S₂ P T)
          ∘ suspSub (idSub (suc _)) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var j) ⟩
  < Var j [ suspSub (idSub _) ]tm
          [ connect-susp-inc-left _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (sub-action-≃-tm (refl≃tm {s = Var j}) (susp-functorial-id _)) refl≃s ⟩
  < Var j [ idSub _ ]tm
          [ connect-susp-inc-left _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (id-on-tm (Var j)) refl≃s ⟩
  < Var j [ connect-susp-inc-left _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ j | p with insertion-var-split S₂ P T j | insertion-var-split-compat S₂ P T j
... | inj₁ k | q = let
  instance _ = connect-susp-inc-right-var-to-var (tree-size S₁) (tree-size S₂)
  in begin
  < Var (varToVarFunction (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) k)
    [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) k) refl≃s ⟩
  < Var k [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
          [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T)
          ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k}) (sub-between-connect-susps-inc-right (idSub _) (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < Var k [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
          ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ exterior-sub S₂ P T ]tm
          [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ k | q = begin
  < Var k [ connect-inc-right getSnd (insertion-tree-size S₂ P T)
          ∘ interior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ interior-sub S₂ P T ]tm
          [ connect-inc-right getSnd (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-inc-right getSnd (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid

insertion-var-split-fst : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → insertion-var-split (suspTree S) (PExt P) (suspTree T) (fromℕ _) ≡ inj₂ (fromℕ _)
insertion-var-split-fst S P T with susp-var-split (insertion-var-split S P T) (fromℕ _) | susp-var-split-fst (insertion-var-split S P T)
... | inj₂ y | p = p

insertion-var-split-snd : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → insertion-var-split (suspTree S) (PExt P) (suspTree T) (inject₁ (fromℕ _)) ≡ inj₂ (inject₁ (fromℕ _))
insertion-var-split-snd S P T with susp-var-split (insertion-var-split S P T) (inject₁ (fromℕ _)) | susp-var-split-snd (insertion-var-split S P T)
... | inj₂ y | p = p

insertion-var-split-inject : (S : Tree n)
                           → (P : Path S)
                           → .⦃ bp : is-branching-path P ⦄
                           → (T : Tree m)
                           → .⦃ lh : has-linear-height (path-length P) T ⦄
                           → (k : Fin (suc (insertion-tree-size S P T)))
                           → insertion-var-split (suspTree S) (PExt P) (suspTree T) (inject₁ (inject₁ k)) ≡ Data.Sum.map (λ - → inject₁ (inject₁ -)) (λ - → inject₁ (inject₁ -)) (insertion-var-split S P T k)
insertion-var-split-inject {n = n} {m = m} S P T k with susp-var-split (insertion-var-split S P T) (inject₁ (inject₁ k)) | susp-var-split-inject (insertion-var-split S P T) k
... | inj₁ x | p = begin
  inj₁ (varToVarFunction (idSub (suc (suc (suc n)))) ⦃ id-is-var-to-var (suc (suc (suc n))) ⦄ x) ≡⟨ cong inj₁ (varToVarFunction-idSub _ x) ⟩
  inj₁ x ≡⟨ p ⟩
  Data.Sum.map (λ - → inject₁ (inject₁ -)) (λ - → (inject₁ (inject₁ -))) (insertion-var-split S P T k) ∎
  where
    open ≡-Reasoning
... | inj₂ y | p = p


sub-from-insertion-susp : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l)
                        → (τ : Sub (suc m) l)
                        → sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion S P T σ τ)
sub-from-insertion-susp S P T σ τ
  = sub-≃-term-wise (sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ))
                    (suspSub (sub-from-insertion S P T σ τ)) lem
  where
    open Reasoning tm-setoid
    l2 : sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (fromℕ _)
           ≃tm
         getFst
    l2 with insertion-var-split (suspTree S) (PExt P) (suspTree T) (fromℕ _) | insertion-var-split-fst S P T
    ... | inj₂ .(suc (suc (fromℕ _))) | refl = sym≃tm (susp-sub-preserve-getFst τ)

    l3 : sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (inject₁ (fromℕ _))
           ≃tm
         getSnd
    l3 with insertion-var-split (suspTree S) (PExt P) (suspTree T) (inject₁ (fromℕ _)) | insertion-var-split-snd S P T
    ... | inj₂ .(suc (inject₁ (fromℕ _))) | refl = sym≃tm (susp-sub-preserve-getSnd τ)

    l4 : (k : Fin (suc (insertion-tree-size S P T)))
       →  sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (inject₁ (inject₁ k))
            ≃tm
          suspTm (sub-from-insertion-func S P T σ τ k)
    l4 k with insertion-var-split (suspTree S) (PExt P) (suspTree T) (inject₁ (inject₁ k)) | insertion-var-split S P T k | insertion-var-split-inject S P T k
    ... | inj₁ .(inject₁ (inject₁ y)) | inj₁ y | refl = inject-susp-sub σ y
    ... | inj₂ .(inject₁ (inject₁ y)) | inj₂ y | refl = inject-susp-sub τ y

    lem : (i : Fin (suc (insertion-tree-size (suspTree S) (PExt P) (suspTree T))))
        → Var i [ sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ]tm
            ≃tm
          Var i [ suspSub (sub-from-insertion S P T σ τ) ]tm
    lem i with suspension-vars i
    ... | inj₁ (inj₁ refl) = begin
      < getFst [ sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ)) (fromℕ _) ⟩
      < sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (fromℕ _) >tm ≈⟨ l2 ⟩
      < getFst >tm ≈⟨ susp-sub-preserve-getFst (sub-from-insertion S P T σ τ) ⟩
      < getFst [ suspSub (sub-from-insertion S P T σ τ) ]tm >tm ∎
    ... | inj₁ (inj₂ refl) = begin
      < getSnd [ sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ)) (inject₁ (fromℕ _)) ⟩
      < sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (inject₁ (fromℕ _)) >tm ≈⟨ l3 ⟩
      < getSnd >tm ≈⟨ susp-sub-preserve-getSnd (sub-from-insertion S P T σ τ) ⟩
      < getSnd [ suspSub (sub-from-insertion S P T σ τ) ]tm >tm ∎
    ... | inj₂ (k ,, refl) = begin
      < Var (inject₁ (inject₁ k)) [ sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ)) (inject₁ (inject₁ k)) ⟩
      < sub-from-insertion-func (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) (inject₁ (inject₁ k)) >tm
        ≈⟨ l4 k ⟩
      < suspTm (sub-from-insertion-func S P T σ τ k) >tm ≈˘⟨ susp-tm-≃ (sub-from-function-prop (sub-from-insertion-func S P T σ τ) k) ⟩
      < suspTm (Var k [ sub-from-insertion S P T σ τ ]tm) >tm ≈˘⟨ inject-susp-sub (sub-from-insertion S P T σ τ) k ⟩
      < Var (inject₁ (inject₁ k)) [ suspSub (sub-from-insertion S P T σ τ) ]tm >tm ∎

sub-from-insertion-sub : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l)
                        → (τ : Sub (suc m) l)
                        → (μ : Sub l l′)
                        → sub-from-insertion S P T (μ ∘ σ) (μ ∘ τ) ≃s μ ∘ sub-from-insertion S P T σ τ
sub-from-insertion-sub S P T σ τ μ = sub-≃-term-wise (sub-from-insertion S P T (μ ∘ σ) (μ ∘ τ)) (μ ∘ sub-from-insertion S P T σ τ) λ i → begin
  < Var i [ sub-from-insertion S P T (μ ∘ σ) (μ ∘ τ) ]tm >tm ≈⟨ sub-from-function-prop (sub-from-insertion-func S P T (μ ∘ σ) (μ ∘ τ)) i ⟩
  < sub-from-insertion-func S P T (μ ∘ σ) (μ ∘ τ) i >tm ≈⟨ lem i ⟩
  < sub-from-insertion-func S P T σ τ i [ μ ]tm >tm ≈˘⟨ sub-action-≃-tm (sub-from-function-prop (sub-from-insertion-func S P T σ τ) i) refl≃s ⟩
  < Var i [ sub-from-insertion S P T σ τ ]tm
          [ μ ]tm >tm
    ≈˘⟨ assoc-tm μ (sub-from-insertion S P T σ τ) (Var i) ⟩
  < Var i [ μ ∘ sub-from-insertion S P T σ τ ]tm >tm ∎
  where
    open Reasoning tm-setoid

    lem : (i : Fin (suc (insertion-tree-size S P T)))
        → sub-from-insertion-func S P T (μ ∘ σ) (μ ∘ τ) i
            ≃tm
          sub-from-insertion-func S P T σ τ i [ μ ]tm
    lem i with insertion-var-split S P T i
    ... | inj₁ j = assoc-tm μ σ (Var j)
    ... | inj₂ j = assoc-tm μ τ (Var j)

interior-sub-var-to-var : (S : Tree n)
                        → (P : Path S)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → varToVar (interior-sub S P T)
interior-sub-var-to-var (Join S₁ S₂) PHere T = var-to-var-comp-sub (connect-inc-left (tree-last-var T) _) ⦃ connect-inc-left-var-to-var (tree-last-var T) (tree-size S₂) ⦄ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⦃ idSub≃-var-to-var (sym≃c (connect-tree-to-ctx T S₂)) ⦄
interior-sub-var-to-var (Join S₁ S₂) (PExt P) (Join T Sing) = var-to-var-comp-sub (suspSub (interior-sub S₁ P T)) ⦃ suspSub-var-to-var (interior-sub S₁ P T) ⦃ interior-sub-var-to-var S₁ P T ⦄ ⦄ (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)) ⦃ connect-susp-inc-left-var-to-var (insertion-tree-size S₁ P T) (tree-size S₂) ⦄
interior-sub-var-to-var (Join S₁ S₂) (PShift P) T = var-to-var-comp-sub (interior-sub S₂ P T) ⦃ interior-sub-var-to-var S₂ P T ⦄ (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S₁) (insertion-tree-size S₂ P T) ⦄

insertion-var-split-full : (S : Tree n)
                         → (P : Path S)
                         → .⦃ bp : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ lh : has-linear-height (path-length P) T ⦄
                         → VarSplitFull₂ (interior-sub S P T) ⦃ interior-sub-var-to-var S P T ⦄ (insertion-var-split S P T)
insertion-var-split-full (Join S₁ S₂) PHere T i = γ
  where
    instance _ = connect-inc-left-var-to-var (tree-last-var T) (tree-size S₂)
    instance _ = interior-sub-var-to-var (Join S₁ S₂) PHere T
    instance _ = idSub≃-var-to-var (sym≃c (connect-tree-to-ctx T S₂))
    instance _ = idSub≃-var-to-var (connect-tree-to-ctx T S₂)
    l2 : idSub≃-func (connect-tree-to-ctx T S₂)
           (varToVarFunction
            (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
             connect-inc-left (tree-last-var T) (tree-size S₂))
            i)
           ≡ varToVarFunction (connect-inc-left (tree-last-var T) (tree-size S₂)) i
    l2 = begin
      idSub≃-func (connect-tree-to-ctx T S₂)
        (varToVarFunction (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
                          ∘ connect-inc-left (tree-last-var T) (tree-size S₂)) i)
        ≡⟨ cong (idSub≃-func (connect-tree-to-ctx T S₂)) (varToVarFunc-comp-sub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (connect-inc-left (tree-last-var T) (tree-size S₂)) i) ⟩
      idSub≃-func (connect-tree-to-ctx T S₂)
        (varToVarFunction (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
         (varToVarFunction
          (connect-inc-left (tree-last-var T) (tree-size S₂)) i))
        ≡˘⟨ varToVarFunc-comp-sub (idSub≃ (connect-tree-to-ctx T S₂)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (varToVarFunction
          (connect-inc-left (tree-last-var T) (tree-size S₂)) i) ⟩
      varToVarFunction
        (idSub≃ (connect-tree-to-ctx T S₂) ∘
         idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⦃ var-to-var-comp-sub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (idSub≃ (connect-tree-to-ctx T S₂)) ⦄
        (varToVarFunction
         (connect-inc-left (tree-last-var T) (tree-size S₂)) i)
        ≡⟨ varToVarFunction-≃ (idSub≃-functorial (sym≃c (connect-tree-to-ctx T S₂)) (connect-tree-to-ctx T S₂)) ⦃ var-to-var-comp-sub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (idSub≃ (connect-tree-to-ctx T S₂)) ⦄ (varToVarFunction
         (connect-inc-left (tree-last-var T) (tree-size S₂)) i) ⟩
      idSub≃-func
         (trans≃c (sym≃c (connect-tree-to-ctx T S₂))
          (connect-tree-to-ctx T S₂))
        (varToVarFunction
         (connect-inc-left (tree-last-var T) (tree-size S₂)) i)
        ≡⟨ varToVarFunction-idSub≃ (trans≃c (sym≃c (connect-tree-to-ctx T S₂))
          (connect-tree-to-ctx T S₂)) (varToVarFunction
         (connect-inc-left (tree-last-var T) (tree-size S₂)) i) ⟩
      varToVarFunction
        (connect-inc-left (tree-last-var T) (tree-size S₂)) i ∎
      where
        open ≡-Reasoning

    lem : connect-var-split (tree-size T) (tree-size S₂)
         (idSub≃-func (connect-tree-to-ctx T S₂)
          (varToVarFunction
           (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
            connect-inc-left (tree-last-var T) (tree-size S₂))
           i)) ≡ inj₁ i
    lem = trans (cong (connect-var-split (tree-size T) (tree-size S₂)) l2) (connect-var-split-full (tree-last-var T) (tree-size S₂) i)

    γ : insertion-var-split (Join S₁ S₂) PHere T
          (varToVarFunction (interior-sub (Join S₁ S₂) PHere T) i)
          ≡ inj₂ i
    γ with connect-var-split (tree-size T) (tree-size S₂)
         (idSub≃-func (connect-tree-to-ctx T S₂)
          (varToVarFunction
           (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
            connect-inc-left (tree-last-var T) (tree-size S₂))
           i)) | lem
    ... | inj₁ x | refl = refl
insertion-var-split-full (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ lh ⦄ i = γ
  where
    instance _ = interior-sub-var-to-var (Join S₁ S₂) (PExt P) (Join T Sing)
    instance _ = connect-susp-inc-left-var-to-var (insertion-tree-size S₁ P T ⦃ lh ⦄) (tree-size S₂)
    instance _ = interior-sub-var-to-var S₁ P T ⦃ lh ⦄
    instance _ = suspSub-var-to-var (interior-sub S₁ P T ⦃ lh ⦄)
    lem1 : connect-var-split (suc (suc (insertion-tree-size S₁ P T)))
         (tree-size S₂)
         (varToVarFunction
          (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
           ∘ suspSub (interior-sub S₁ P T))
          i) ≡ inj₁ (varToVarFunction (suspSub (interior-sub S₁ P T)) i)
    lem1 = trans (cong
                   (connect-var-split (suc (suc (insertion-tree-size S₁ P T)))
                    (tree-size S₂))
                   (varToVarFunc-comp-sub (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)) (suspSub (interior-sub S₁ P T)) i)) (connect-var-split-full getSnd (tree-size S₂) (varToVarFunction (suspSub (interior-sub S₁ P T)) i))

    lem2 : susp-var-split (insertion-var-split S₁ P T)
         (varToVarFunction (suspSub (interior-sub S₁ P T)) i) ≡ inj₂ i
    lem2 = susp-var-split-full (interior-sub S₁ P T) (insertion-var-split S₁ P T) (insertion-var-split-full S₁ P T) i

    γ : insertion-var-split (Join S₁ S₂) (PExt P) (Join T Sing)
          (varToVarFunction
           (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) i)
          ≡ inj₂ i
    γ with connect-var-split (suc (suc (insertion-tree-size S₁ P T)))
         (tree-size S₂)
         (varToVarFunction
          (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
           ∘ suspSub (interior-sub S₁ P T))
          i) | lem1
    ... | inj₁ .(varToVarFunction (suspSub (interior-sub S₁ P T)) i) | refl with susp-var-split (insertion-var-split S₁ P T)
         (varToVarFunction (suspSub (interior-sub S₁ P T)) i) | lem2
    ... | inj₂ y | refl = refl

insertion-var-split-full (Join S₁ S₂) (PShift P) T ⦃ lh ⦄ i = γ
  where
    instance _ = interior-sub-var-to-var (Join S₁ S₂) (PShift P) T
    instance _ = interior-sub-var-to-var S₂ P T
    instance _ = connect-susp-inc-right-var-to-var (tree-size S₁) (insertion-tree-size S₂ P T ⦃ lh ⦄)
    lem1 : connect-var-split-right getSnd (insertion-tree-size S₂ P T)
         (varToVarFunction
          (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)
           ∘ interior-sub S₂ P T)
          i) ≡ inj₂ (varToVarFunction (interior-sub S₂ P T) i)
    lem1 = trans (cong (connect-var-split-right getSnd (insertion-tree-size S₂ P T))
                   (varToVarFunc-comp-sub (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)) (interior-sub S₂ P T) i)) (connect-var-split-right-full getSnd (insertion-tree-size S₂ P T) (varToVarFunction (interior-sub S₂ P T) i))

    lem2 : insertion-var-split S₂ P T
         (varToVarFunction (interior-sub S₂ P T) i) ≡ inj₂ i
    lem2 = insertion-var-split-full S₂ P T i

    γ : insertion-var-split (Join S₁ S₂) (PShift P) T
          (varToVarFunction (interior-sub (Join S₁ S₂) (PShift P) T) i)
          ≡ inj₂ i
    γ with connect-var-split-right getSnd (insertion-tree-size S₂ P T)
         (varToVarFunction
          (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)
           ∘ interior-sub S₂ P T)
          i) | lem1
    ... | inj₂ .(varToVarFunction (interior-sub S₂ P T) i) | refl with insertion-var-split S₂ P T
         (varToVarFunction (interior-sub S₂ P T) i) | lem2
    ... | inj₂ y | refl = refl

interior-sub-comm : (S : Tree n)
                  → (P : Path S)
                  → .⦃ bp : is-branching-path P ⦄
                  → (T : Tree m)
                  → .⦃ lh : has-linear-height (path-length P) T ⦄
                  → (σ : Sub (suc n) l)
                  → (τ : Sub (suc m) l)
                  → sub-from-insertion S P T σ τ ∘ interior-sub S P T ≃s τ
interior-sub-comm S P T σ τ = sub-≃-term-wise (sub-from-insertion S P T σ τ ∘ interior-sub S P T) τ λ i →
  let
    instance _ = interior-sub-var-to-var S P T
  in begin
    < Var i [ sub-from-insertion S P T σ τ ∘ interior-sub S P T ]tm >tm
      ≈⟨ assoc-tm _ _ (Var i) ⟩
    < Var i [ interior-sub S P T ]tm
            [ sub-from-insertion S P T σ τ ]tm >tm
      ≈˘⟨ sub-action-≃-tm (varToVarFunctionProp (interior-sub S P T) i) refl≃s ⟩
    < Var (varToVarFunction (interior-sub S P T) i)
      [ sub-from-insertion S P T σ τ ]tm >tm
      ≈⟨ sub-from-function-prop (sub-from-insertion-func S P T σ τ) (varToVarFunction (interior-sub S P T) i) ⟩
    < sub-from-insertion-func S P T σ τ (varToVarFunction (interior-sub S P T) i) >tm
      ≈⟨ lem i ⟩
    < Var i [ τ ]tm >tm ∎
  where
    open Reasoning tm-setoid
    instance _ = interior-sub-var-to-var S P T
    lem : (i : Fin (suc _)) → sub-from-insertion-func S P T σ τ
          (varToVarFunction (interior-sub S P T) i) ≃tm Var i [ τ ]tm
    lem i with insertion-var-split S P T
         (varToVarFunction (interior-sub S P T) i) | insertion-var-split-full S P T i
    ... | inj₂ .i | refl = refl≃tm

-- interior-sub-comm′ : (S : Tree n)
--                    → (P : Path S)
--                    → .⦃ bp : is-branching-path P ⦄
--                    → (T : Tree m)
--                    → .⦃ lh : has-linear-height (path-length P) T ⦄
--                    → (σ : Sub (suc n) l)
--                    → (τ : Sub (suc m) l)
--                    → (A : Ty l d)
--                    → sub-from-insertion′ S P T σ τ A ∘⟨ A ⟩ interior-sub S P T ≃s τ
-- interior-sub-comm′ (Join S₁ S₂) PHere T σ τ A = begin
--   < sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
--     ∘⟨ A ⟩ idSub≃ (connect-tree-to-ctx T S₂)
--     ∘⟨ A ⟩ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) (tree-size S₂)) >s
--     ≈˘⟨ ∘⟨⟩-assoc A (sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) (idSub≃ (connect-tree-to-ctx T S₂)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _) ⟩
--   < sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
--     ∘⟨ A ⟩ (idSub≃ (connect-tree-to-ctx T S₂)
--            ∘ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
--            ∘ connect-inc-left (tree-last-var T) _)) >s
--     ≈⟨ sub-⟨⟩-action-≃-sub refl≃s refl≃ty (trans≃s (idSub≃-on-sub (connect-tree-to-ctx T S₂) ((idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
--            ∘ connect-inc-left (tree-last-var T) _))) (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _))) ⟩
--   < sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
--     ∘⟨ A ⟩ connect-inc-left (tree-last-var T) _ >s
--     ≈⟨ ⟨⟩-var-to-var (sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) A (connect-inc-left (tree-last-var T) _) ⦃ connect-inc-left-var-to-var (tree-last-var T) (tree-size S₂) ⦄ ⟩
--   < sub-from-connect τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
--     ∘ connect-inc-left (tree-last-var T) _
--     >s
--     ≈⟨ sub-from-connect-inc-left τ (tree-last-var T) (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
--   < τ >s ∎
--   where
--     open Reasoning sub-setoid
-- interior-sub-comm′ (Join S₁ S₂) (PExt P) (Join T Sing) σ τ A = begin
--   < sub-from-insertion′ (Join S₁ S₂) (PExt P) (Join T Sing) σ τ A
--     ∘⟨ A ⟩ interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) >s
--     ≈⟨ ∘⟨⟩-assoc A _ _ _ ⟩
--   < sub-from-insertion′ (Join S₁ S₂) (PExt P) (Join T Sing) σ τ A
--     ∘⟨ A ⟩ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
--     ∘⟨ A ⟩ suspSub (interior-sub S₁ P T) >s
--     ≈⟨ sub-⟨⟩-action-≃-sub (⟨⟩-var-to-var _ _ _ ⦃ connect-susp-inc-left-var-to-var (insertion-tree-size S₁ P T) (tree-size S₂) ⦄) refl≃ty refl≃s ⟩
--   < sub-from-insertion′ (Join S₁ S₂) (PExt P) (Join T Sing) σ τ A
--     ∘ connect-inc-left getSnd (tree-size S₂)
--     ∘⟨ A ⟩ suspSub (interior-sub S₁ P T) >s
--     ≈⟨ sub-⟨⟩-action-≃-sub (sub-from-connect-inc-left _ getSnd (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) refl≃ty refl≃s ⟩
--   < unrestrict (sub-from-insertion′ S₁ P T (restrict (σ ∘⟨ A ⟩ connect-susp-inc-left (tree-size S₁) (tree-size S₂))) (restrict τ) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm))) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm))
--     ∘⟨ A ⟩ suspSub (interior-sub S₁ P T) >s
--     ≈˘⟨ unrestrict-comp _ _ _ ⟩
--   < unrestrict
--     (sub-from-insertion′ S₁ P T (restrict (σ ∘⟨ A ⟩ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
--      (restrict τ) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm))
--      ∘⟨ (getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm) ⟩
--      interior-sub S₁ P T)
--     ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm))
--     >s
--     ≈⟨ unrestrict-≃ (interior-sub-comm′ S₁ P T (restrict
--                                                  (σ ∘⟨ A ⟩ connect-susp-inc-left (tree-size S₁) (tree-size S₂))) (restrict τ) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm))) refl≃ty ⟩
--   < unrestrict (restrict τ) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm)) >s
--     ≈⟨ unrestrict-restrict τ A ⟩
--   < τ >s ∎
--   where
--     open Reasoning sub-setoid
-- interior-sub-comm′ (Join S₁ S₂) (PShift P) T σ τ A = begin
--   < sub-from-insertion′ (Join S₁ S₂) (PShift P) T σ τ A
--     ∘⟨ A ⟩ interior-sub (Join S₁ S₂) (PShift P) T >s
--     ≈⟨ ∘⟨⟩-assoc A _ _ _ ⟩
--   < sub-from-insertion′ (Join S₁ S₂) (PShift P) T σ τ A
--     ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)
--     ∘⟨ A ⟩ interior-sub S₂ P T >s
--     ≈⟨ sub-⟨⟩-action-≃-sub (⟨⟩-var-to-var _ _ _ ⦃ connect-susp-inc-right-var-to-var (tree-size S₁) (insertion-tree-size S₂ P T) ⦄) refl≃ty refl≃s ⟩
--   < sub-from-insertion′ (Join S₁ S₂) (PShift P) T σ τ A
--     ∘ connect-inc-right getSnd (insertion-tree-size S₂ P T)
--     ∘⟨ A ⟩ interior-sub S₂ P T >s
--     ≈⟨ sub-⟨⟩-action-≃-sub (sub-from-connect-inc-right (σ ∘⟨ A ⟩ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd (sub-from-insertion′ S₂ P T (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ A) {!!}) refl≃ty refl≃s ⟩
--   < sub-from-insertion′ S₂ P T (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ A
--     ∘⟨ A ⟩ interior-sub S₂ P T >s
--     ≈⟨ interior-sub-comm′ S₂ P T (σ ∘⟨ A ⟩ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ A ⟩
--   < τ >s ∎
--   where
--     open Reasoning sub-setoid
-}

sub-from-insertion-≃ : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → σ ≃s σ′ → τ ≃s τ′
                     → sub-from-insertion S P T σ τ ≃s sub-from-insertion S P T σ′ τ′
sub-from-insertion-≃ (Join S₁ S₂) PHere T p q = sub-action-≃-sub refl≃s (sub-from-connect-≃ q (sub-action-≃-sub refl≃s p))
sub-from-insertion-≃ (Join S₁ S₂) (PExt P) (Join T Sing) p q = sub-from-connect-≃ (unrestrict-≃ (sub-from-insertion-≃ S₁ P T (restrict-≃ (sub-action-≃-sub refl≃s p) (sub-action-≃-tm (refl≃tm {s = getFst}) q) (sub-action-≃-tm (refl≃tm {s = getSnd}) q)) (restrict-≃ q (sub-action-≃-tm (refl≃tm {s = getFst}) q) (sub-action-≃-tm (refl≃tm {s = getSnd}) q)))) (sub-action-≃-sub refl≃s p)
sub-from-insertion-≃ (Join S₁ S₂) (PShift P) T p q = sub-from-connect-≃ (sub-action-≃-sub refl≃s p) (sub-from-insertion-≃ S₂ P T (sub-action-≃-sub refl≃s p) q)

lift-sub-from-insertion : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l A)
                        → (τ : Sub (suc m) l A)
                        → liftSub (sub-from-insertion S P T σ τ) ≃s sub-from-insertion S P T (liftSub σ) (liftSub τ)
lift-sub-from-insertion (Join S₁ S₂) PHere T σ τ = begin
  < liftSub (sub-from-connect τ
                              (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s
    ≈˘⟨ apply-lifted-sub-sub-≃ _ _ ⟩
  < liftSub (sub-from-connect τ
                              (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-lift τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < sub-from-connect (liftSub τ)
                     (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (apply-lifted-sub-sub-≃ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) σ)) ⟩
  < sub-from-connect (liftSub τ)
                     (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s ∎
  where
    open Reasoning sub-setoid

lift-sub-from-insertion (Join S₁ S₂) (PExt P) (Join T Sing) σ τ = begin
  < liftSub (sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈⟨ sub-from-connect-lift _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < sub-from-connect
      (liftSub (unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))))
      (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-≃ lem (apply-lifted-sub-sub-≃ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) σ) ⟩
  < sub-from-connect
      (unrestrict
        (sub-from-insertion S₁ P T
          (restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ liftSub τ ]tm)
                    (getSnd [ liftSub τ ]tm))
          (restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))))
      (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ liftSub τ ]tm)
                  (getSnd [ liftSub τ ]tm)
         ≃s
         liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                           (getFst [ τ ]tm)
                           (getSnd [ τ ]tm))
    l1 = begin
      < restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ liftSub τ ]tm)
                 (getSnd [ liftSub τ ]tm) >s
        ≈⟨ restrict-≃ (apply-lifted-sub-sub-≃ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) σ) (apply-lifted-sub-tm-≃ getFst τ) (apply-lifted-sub-tm-≃ getSnd τ) ⟩
      < restrict (liftSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                 (liftTerm (getFst [ τ ]tm))
                 (liftTerm (getSnd [ τ ]tm)) >s
        ≈⟨ restrict-lift _ _ _ ⟩
      < liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                          (getFst [ τ ]tm)
                          (getSnd [ τ ]tm)) >s ∎

    l2 : restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm)
         ≃s liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l2 = begin
      < restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm) >s
        ≈⟨ restrict-≃ refl≃s (apply-lifted-sub-tm-≃ getFst τ) (apply-lifted-sub-tm-≃ getSnd τ) ⟩
      < restrict (liftSub τ) (liftTerm (getFst [ τ ]tm)) (liftTerm (getSnd [ τ ]tm)) >s
        ≈⟨ restrict-lift τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s ∎

    lem : unrestrict (sub-from-insertion S₁ P T
            (restrict
              (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))
            (restrict (liftSub τ) (getFst [ liftSub τ ]tm)
              (getSnd [ liftSub τ ]tm)))
          ≃s
          liftSub (unrestrict (sub-from-insertion S₁ P T
            (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                      (getFst [ τ ]tm)
                      (getSnd [ τ ]tm))
            (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    lem = begin
      < unrestrict (sub-from-insertion S₁ P T
        (restrict
          (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))
        (restrict (liftSub τ) (getFst [ liftSub τ ]tm)
          (getSnd [ liftSub τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l1 l2) ⟩
      < unrestrict (sub-from-insertion S₁ P T
         (liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                            (getFst [ τ ]tm)
                            (getSnd [ τ ]tm)))
         (liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈˘⟨ unrestrict-≃ (lift-sub-from-insertion S₁ P T _ _) ⟩
      < unrestrict (liftSub (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈⟨ unrestrict-lift _ ⟩
      < liftSub (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s ∎

lift-sub-from-insertion (Join S₁ S₂) (PShift P) T σ τ = begin
  < liftSub (sub-from-connect
       (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈⟨ sub-from-connect-lift (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) ⟩
  < sub-from-connect
      (liftSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
      (liftSub (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈˘⟨ sub-from-connect-≃ (apply-lifted-sub-sub-≃ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) σ) lem ⟩
  < sub-from-connect
      (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T
                          (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                          (liftSub τ)) >s ∎
  where
    open Reasoning sub-setoid

    lem : sub-from-insertion S₂ P T
            (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            (liftSub τ)
          ≃s
          liftSub (sub-from-insertion S₂ P T
                  (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    lem = begin
      < sub-from-insertion S₂ P T
          (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
          (liftSub τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (apply-lifted-sub-sub-≃ (connect-susp-inc-right _ _) σ) refl≃s ⟩
      < sub-from-insertion S₂ P T
          (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
          (liftSub τ) >s
        ≈˘⟨ lift-sub-from-insertion S₂ P T _ _ ⟩
      < liftSub (sub-from-insertion S₂ P T
                (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s ∎

sub-from-insertion-susp-res : (S : Tree n)
                            → (P : Path S)
                            → .⦃ bp : is-branching-path P ⦄
                            → (T : Tree m)
                            → .⦃ lh : has-linear-height (path-length P) T ⦄
                            → (σ : Sub (suc n) l A)
                            → (τ : Sub (suc m) l A)
                            → sub-from-insertion S P T (suspSubRes σ) (suspSubRes τ) ≃s suspSubRes (sub-from-insertion S P T σ τ)
sub-from-insertion-susp-res (Join S₁ S₂) PHere T σ τ = begin
  < sub-from-connect (suspSubRes τ) (suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect (suspSubRes τ) (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-susp-res τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < suspSubRes (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ susp-res-comp-sub _ _ ⟩
  < suspSubRes (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s ∎
  where
    open Reasoning sub-setoid

sub-from-insertion-susp-res (Join S₁ S₂) (PExt P) (Join T Sing) σ τ = begin
  < sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ suspSubRes τ ]tm)
                  (getSnd [ suspSubRes τ ]tm))
        (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm))))
      (suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect
      (suspSubRes (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))))
      (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-susp-res _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < suspSubRes (sub-from-connect
      (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s ∎
  where
    open Reasoning sub-setoid

    l3 : restrict
           (suspSubRes σ ∘
            connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm)
           ≃s
           suspSubRes
           (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
            (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l3 = begin
      < restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ suspSubRes τ ]tm)
                 (getSnd [ suspSubRes τ ]tm) >s
        ≈˘⟨ restrict-≃ (susp-res-comp-sub σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                       (susp-res-comp-tm getFst τ)
                       (susp-res-comp-tm getSnd τ) ⟩
      < restrict (suspSubRes (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                 (suspTm (getFst [ τ ]tm))
                 (suspTm (getSnd [ τ ]tm)) >s
        ≈˘⟨ susp-res-restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                              (getFst [ τ ]tm)
                              (getSnd [ τ ]tm) ⟩
      < suspSubRes (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                             (getFst [ τ ]tm)
                             (getSnd [ τ ]tm)) >s ∎

    l4 : restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm)
                                 (getSnd [ suspSubRes τ ]tm)
         ≃s suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l4 = begin
      < restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm) >s
        ≈˘⟨ restrict-≃ refl≃s (susp-res-comp-tm getFst τ) (susp-res-comp-tm getSnd τ) ⟩
      < restrict (suspSubRes τ) (suspTm (getFst [ τ ]tm)) (suspTm (getSnd [ τ ]tm)) >s
        ≈˘⟨ susp-res-restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s ∎

    l1 : unrestrict (sub-from-insertion S₁ P T
           (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ suspSubRes τ ]tm)
                     (getSnd [ suspSubRes τ ]tm))
           (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm)))
      ≃s suspSubRes (unrestrict (sub-from-insertion S₁ P T
           (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ τ ]tm)
                     (getSnd [ τ ]tm))
           (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    l1 = begin
      < unrestrict (sub-from-insertion S₁ P T
          (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ suspSubRes τ ]tm)
                    (getSnd [ suspSubRes τ ]tm))
          (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l3 l4) ⟩
      < unrestrict (sub-from-insertion S₁ P T
          (suspSubRes (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                                (getFst [ τ ]tm)
                                (getSnd [ τ ]tm)))
          (suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-susp-res S₁ P T _ _) ⟩
      < unrestrict (suspSubRes (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈˘⟨ sub-res-unrestrict-comm _ ⟩
      < suspSubRes (unrestrict (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s ∎

    l2 : suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)
      ≃s suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    l2 = sym≃s (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))

sub-from-insertion-susp-res (Join S₁ S₂) (PShift P) T σ τ = begin
  < sub-from-connect
      (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (suspSubRes σ
                                 ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                 (suspSubRes τ)) >s
    ≈˘⟨ sub-from-connect-≃ (susp-res-comp-sub σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                           lem ⟩
  < sub-from-connect
      (suspSubRes (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
      (suspSubRes (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈˘⟨ sub-from-connect-susp-res (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) _ ⟩
  < suspSubRes (sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s ∎
  where
    open Reasoning sub-setoid

    lem : suspSubRes (sub-from-insertion S₂ P T
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
       ≃s sub-from-insertion S₂ P T (suspSubRes σ
                                    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                    (suspSubRes τ)
    lem = begin
      < suspSubRes (sub-from-insertion S₂ P T
                   (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s
        ≈˘⟨ sub-from-insertion-susp-res S₂ P T _ _ ⟩
      < sub-from-insertion S₂ P T (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
                                  (suspSubRes τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂))) refl≃s ⟩
      < sub-from-insertion S₂ P T (suspSubRes σ
                                  ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                  (suspSubRes τ) >s ∎

sub-from-insertion-susp : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l ⋆)
                        → (τ : Sub (suc m) l ⋆)
                        → sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion S P T σ τ)
sub-from-insertion-susp S P T σ τ = begin
  < sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) >s ≡⟨⟩
  < (unrestrict (sub-from-insertion S P T
                (restrict (suspSub σ ∘ idSub)
                          (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm))
                (restrict (suspSub τ) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm)))) >s
    ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S P T l1 l2) ⟩
  < unrestrict (sub-from-insertion S P T (suspSubRes σ) (suspSubRes τ)) >s
    ≈⟨ unrestrict-≃ (sub-from-insertion-susp-res S P T σ τ) ⟩
  < unrestrict (suspSubRes (sub-from-insertion S P T σ τ)) >s ≡⟨⟩
  < suspSub (sub-from-insertion S P T σ τ) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict (suspSub σ ∘ idSub) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm)
         ≃s suspSubRes σ
    l1 = begin
      < restrict (suspSub σ ∘ idSub) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm) >s
        ≈⟨ restrict-≃ (id-right-unit (suspSub σ)) (sym≃tm (susp-sub-preserve-getFst τ)) (sym≃tm (susp-sub-preserve-getSnd τ)) ⟩
      < restrict (suspSub σ) getFst getSnd >s
        ≈⟨ restrict-unrestrict (suspSubRes σ) ⟩
      < suspSubRes σ >s ∎

    l2 : restrict (suspSub τ) (getFst [ suspSub τ ]tm)
           (getSnd [ suspSub τ ]tm)
           ≃s suspSubRes τ
    l2 = begin
      < restrict (suspSub τ) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm) >s
        ≈˘⟨ restrict-≃ refl≃s (susp-sub-preserve-getFst τ) (susp-sub-preserve-getSnd τ) ⟩
      < restrict (suspSub τ) getFst getSnd >s
        ≈⟨ restrict-unrestrict (suspSubRes τ) ⟩
      < suspSubRes τ >s ∎

sub-from-insertion-sub : (S : Tree n)
                       → (P : Path S)
                       → .⦃ bp : is-branching-path P ⦄
                       → (T : Tree m)
                       → .⦃ lh : has-linear-height (path-length P) T ⦄
                       → (σ : Sub (suc n) l A)
                       → (τ : Sub (suc m) l A)
                       → (μ : Sub l l′ B)
                       → sub-from-insertion S P T (μ ∘ σ) (μ ∘ τ) ≃s μ ∘ sub-from-insertion S P T σ τ
sub-from-insertion-sub (Join S₁ S₂) PHere T σ τ μ = begin
  < sub-from-connect (μ ∘ τ) (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (∘-assoc μ σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect (μ ∘ τ) (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-sub τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) μ) ⟩
  < μ
    ∘ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ ∘-assoc μ _ _ ⟩
  < μ
    ∘ (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s ∎
  where
    open Reasoning sub-setoid

sub-from-insertion-sub (Join S₁ S₂) (PExt P) (Join T Sing) σ τ μ = begin
  < sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ μ ∘ τ ]tm)
                  (getSnd [ μ ∘ τ ]tm))
        (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm))))
      (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s
    ≈⟨ sub-from-connect-≃ lem (∘-assoc μ σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < sub-from-connect
      (μ ∘ unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-sub _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) μ ⟩
  < μ ∘ sub-from-connect
       (unrestrict (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                   (getFst [ τ ]tm)
                   (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict
           (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)
           ≃s
           (μ ∘
            restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
            (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l1 = begin
      < restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ μ ∘ τ ]tm)
                 (getSnd [ μ ∘ τ ]tm) >s
        ≈⟨ restrict-≃ (∘-assoc μ σ _) (assoc-tm μ τ getFst) (assoc-tm μ τ getSnd) ⟩
      < restrict (μ ∘ (σ ∘ connect-susp-inc-left _ _))
                 (getFst [ τ ]tm [ μ ]tm)
                 (getSnd [ τ ]tm [ μ ]tm)
        >s
        ≈˘⟨ restrict-comp-sub μ (σ ∘ connect-susp-inc-left _ _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < μ ∘ restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ τ ]tm)
                     (getSnd [ τ ]tm) >s ∎

    l2 : restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)
      ≃s (μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l2 = begin
      < restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm) >s
        ≈⟨ restrict-≃ refl≃s (assoc-tm μ τ getFst) (assoc-tm μ τ getSnd) ⟩
      < restrict (μ ∘ τ) (getFst [ τ ]tm [ μ ]tm) (getSnd [ τ ]tm [ μ ]tm) >s
        ≈˘⟨ restrict-comp-sub μ τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) >s ∎

    lem : unrestrict (sub-from-insertion S₁ P T
            (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                      (getFst [ μ ∘ τ ]tm)
                      (getSnd [ μ ∘ τ ]tm))
            (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)))
          ≃s
          (μ ∘ unrestrict (sub-from-insertion S₁ P T
              (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                        (getFst [ τ ]tm)
                        (getSnd [ τ ]tm))
              (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    lem = begin
      < unrestrict (sub-from-insertion S₁ P T
          (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ μ ∘ τ ]tm)
                    (getSnd [ μ ∘ τ ]tm))
          (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l1 l2) ⟩
      < unrestrict (sub-from-insertion S₁ P T
          (μ ∘ restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                        (getFst [ τ ]tm)
                        (getSnd [ τ ]tm))
          (μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-sub S₁ P T _ _ μ) ⟩
      < unrestrict (μ ∘ sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s
        ≈⟨ unrestrict-comp-higher μ _ ⟩
      < μ ∘ unrestrict (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s ∎

sub-from-insertion-sub (Join S₁ S₂) (PShift P) T σ τ μ = begin
  < sub-from-connect
      (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T
        (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
        (μ ∘ τ)) >s
    ≈⟨ sub-from-connect-≃ (∘-assoc μ σ (connect-susp-inc-left _ _)) lem ⟩
  < sub-from-connect
      (μ ∘ (σ ∘ connect-susp-inc-left _ _))
      (μ ∘ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s
    ≈˘⟨ sub-from-connect-sub (σ ∘ connect-susp-inc-left _ _) (sub-from-insertion S₂ P T _ τ) μ ⟩
  < μ ∘ sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s ∎
  where
    open Reasoning sub-setoid

    lem : sub-from-insertion S₂ P T
            (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            (μ ∘ τ)
       ≃s μ ∘ sub-from-insertion S₂ P T
            (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ
    lem = begin
      < sub-from-insertion S₂ P T
          (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
          (μ ∘ τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (∘-assoc μ σ (connect-susp-inc-right _ _)) refl≃s ⟩
      < sub-from-insertion S₂ P T
          (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
          (μ ∘ τ) >s
        ≈⟨ sub-from-insertion-sub S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ μ ⟩
      < μ ∘ sub-from-insertion S₂ P T
          (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ >s ∎
