{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Pasting.Insertion.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Insertion
open import Catt.Connection
open import Catt.Connection.Typing index rule props
open import Catt.Suspension
open import Catt.Suspension.Typing index rule props
open import Catt.Discs
open import Catt.Discs.Typing index rule props
open import Data.Product
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Pasting.Insertion.Properties
open import Catt.Connection.Properties
open import Catt.Suspension.Properties
open import Catt.Unsuspension

interior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T)) (interior-sub S P T)
interior-sub-Ty S (PHere .S) T = id-Ty
interior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing)
  = apply-sub-sub-typing (suspSubTy (interior-sub-Ty S₁ P T))
                         (connect-pd-inc-left-Ty (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-to-ctx S₂))
interior-sub-Ty (Join S₁ S₂) (PShift P) T
  = apply-sub-sub-typing (interior-sub-Ty S₂ P T)
                         (connect-pd-inc-right-Ty (susp-pd (tree-to-pd S₁)) (tree-to-ctx (insertion-tree S₂ P T)))

exterior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → .⦃ _ : is-branching-path P ⦄
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → (A : Ty (suc m) (height-of-branching P))
                → .⦃ _ : type-has-linear-height (path-length P) T A ⦄
                → Typing-Ty (tree-to-ctx T) A
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T)) (exterior-sub S P T A)
exterior-sub-Ty S (PHere .S) T A Aty = apply-sub-sub-typing (idSub≃-Ty (linear-tree-compat S)) (sub-from-disc-Ty {!!} {!!})
exterior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing) A ⦃ tlh ⦄ Aty
  = sub-from-connect-pd-Ty (susp-pd (tree-to-pd S₁))
                           (apply-sub-sub-typing (suspSubTy (exterior-sub-Ty S₁ P T (unsuspend-ty A ⦃ proj₁ tlh ⦄) ⦃ proj₂ tlh ⦄ {!!}))
                                                 (connect-pd-inc-left-Ty (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-to-ctx S₂)))
                           (connect-pd-inc-right-Ty (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-to-ctx S₂))
                           (reflexive≈tm lem)
  where
    open Reasoning tm-setoid
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
             ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A ⦃ proj₁ tlh ⦄) ⦃ proj₂ tlh ⦄)
             ]tm
            ≃tm
          Var (fromℕ _)
            [ connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm
    lem = let
      instance .tlh₁ : is-unsuspendable-ty A
               tlh₁ = proj₁ tlh
      instance .tlh₂ : type-has-linear-height (path-length P) T
                         (unsuspend-ty A)
               tlh₂ = proj₂ tlh
      in begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
          ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm >tm
        ≈⟨ assoc-tm _ _ (pd-focus-tm (susp-pd (tree-to-pd S₁))) ⟩
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
        ≈⟨ sub-action-≃-tm (suspSub-preserve-focus-tm (tree-to-pd S₁) (tree-to-pd (insertion-tree S₁ P T)) (exterior-sub S₁ P T (unsuspend-ty A))) refl≃s ⟩
      < pd-focus-tm (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
        [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm ∎

exterior-sub-Ty (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T A Aty
  = sub-from-connect-pd-Ty (susp-pd (tree-to-pd S₁))
                           (connect-pd-inc-left-Ty (susp-pd (tree-to-pd S₁)) (tree-to-ctx (insertion-tree S₂ P T)))
                           (apply-sub-sub-typing (exterior-sub-Ty S₂ P ⦃ proj₁ bp ⦄ T A Aty)
                                                 (connect-pd-inc-right-Ty (susp-pd (tree-to-pd S₁)) (tree-to-ctx (insertion-tree S₂ P T))))
                           (reflexive≈tm lem)
  where
    open Reasoning tm-setoid
    -- Deduplicate this?
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
          ≃tm
          (Var (fromℕ _)
            [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
              ∘ exterior-sub S₂ P ⦃ proj₁ bp ⦄ T A ]tm)
    lem = let
      instance .l : is-branching-path P
               l = proj₁ bp
      instance .ne : is-non-empty-path P
               ne = proj₂ bp
      in begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd S₁))
                                  (insertion-tree-size S₂ P T) ⟩
      < Var (fromℕ _) [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                             (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ sub-action-≃-tm (exterior-sub-fst-var S₂ P T A) refl≃s ⟩
      < Var (fromℕ _)
          [ exterior-sub S₂ P T A ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
        ≈˘⟨ assoc-tm _ (exterior-sub S₂ P T A) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
            ∘ exterior-sub S₂ P T A ]tm >tm ∎
