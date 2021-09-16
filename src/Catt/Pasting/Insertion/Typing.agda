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
open import Catt.Pasting.Properties
open import Catt.Pasting.Tree
open import Catt.Pasting.Insertion
open import Catt.Connection
open import Catt.Connection.Typing index rule props
open import Catt.Suspension
open import Catt.Suspension.Typing index rule props
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Discs.Typing index rule props
open import Data.Product
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Pasting.Insertion.Properties
open import Catt.Connection.Properties
open import Catt.Suspension.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Pasting.Unbiased
open import Catt.Pasting.Unbiased.Properties

interior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T)) (interior-sub S P T)
interior-sub-Ty (Join S₁ S₂) PHere T = apply-sub-sub-typing (connect-pd-inc-left-Ty (tree-to-pd T) (tree-to-ctx S₂)) (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)))
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
                → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T)) (exterior-sub S P T)
exterior-sub-Ty (Join S₁ S₂) PHere T ⦃ p = p ⦄
  = apply-sub-sub-typing (sub-from-connect-pd-Ty (susp-pd (tree-to-pd S₁)) (apply-sub-sub-typing (idSub≃-Ty (trans≃c (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (height-of-linear S₁))) (disc-≡ _))) (apply-sub-sub-typing (sub-from-disc-Ty {t = Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _)} {!!} {!!}) (connect-pd-inc-left-Ty (tree-to-pd T) (tree-to-ctx S₂)))) (connect-pd-inc-right-Ty (tree-to-pd T) (tree-to-ctx S₂)) (reflexive≈tm lem)) (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)))
  where
    open Reasoning tm-setoid
    lemnz : .(suc l ≡ n) → NonZero′ n
    lemnz {n = suc n} p = it
    instance .x : NonZero′ (tree-to-pd-dim T)
             x = lemnz p
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (tree-to-pd T) _
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
          ∘ idSub≃ (trans≃c (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (height-of-linear S₁))) (disc-≡ _)) ]tm
            ≃tm
          Var (fromℕ _) [ connect-pd-inc-right (tree-to-pd T) _ ]tm
    lem = begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (tree-to-pd T) _
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
          ∘ idSub≃ (trans≃c (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (height-of-linear S₁))) (disc-≡ _)) ]tm >tm
        ≈⟨ assoc-tm _ _ (pd-focus-tm (susp-pd (tree-to-pd S₁))) ⟩
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
        [ idSub≃ (trans≃c (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (height-of-linear S₁))) (disc-≡ _)) ]tm
        [ connect-pd-inc-left (tree-to-pd T) _
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm
        ≈⟨ sub-action-≃-tm (idSub≃-pd-focus-tm (susp-pd (tree-to-pd S₁)) (Disc-pd (tree-to-pd-dim T)) (trans≃c (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (height-of-linear S₁))) (disc-≡ _))) refl≃s ⟩
      < pd-focus-tm (Disc-pd (tree-to-pd-dim T))
        [ connect-pd-inc-left (tree-to-pd T) _
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm
        ≈⟨ assoc-tm _ _ (pd-focus-tm (Disc-pd (tree-to-pd-dim T))) ⟩
      < pd-focus-tm (Disc-pd (tree-to-pd-dim T))
        [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm
        [ connect-pd-inc-left (tree-to-pd T) _ ]tm
        >tm
        ≈⟨ sub-action-≃-tm (unbiased-type-disc-foc-lem (tree-to-pd T)) refl≃s ⟩
      < pd-focus-tm (tree-to-pd T) [ connect-pd-inc-left (tree-to-pd T) _ ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (tree-to-pd T) _ ⟩
      < Var (fromℕ _) [ connect-pd-inc-right (tree-to-pd T) _ ]tm >tm ∎


exterior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = let
  instance .x : _
           x = cong pred p
  in sub-from-connect-pd-Ty (susp-pd (tree-to-pd S₁))
                           (apply-sub-sub-typing (suspSubTy (exterior-sub-Ty S₁ P T))
                                                 (connect-pd-inc-left-Ty (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-to-ctx S₂)))
                           (connect-pd-inc-right-Ty (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-to-ctx S₂))
                           (reflexive≈tm lem)
  where
    open Reasoning tm-setoid
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
             ∘ suspSub (exterior-sub S₁ P T ⦃ p = cong pred p ⦄)
             ]tm
            ≃tm
          Var (fromℕ _)
            [ connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm
    lem = let
      instance .x : _
               x = cong pred p
      in begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
          ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
        ≈⟨ assoc-tm _ _ (pd-focus-tm (susp-pd (tree-to-pd S₁))) ⟩
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ suspSub (exterior-sub S₁ P T) ]tm
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
        ≈⟨ sub-action-≃-tm (suspSub-preserve-focus-tm (tree-to-pd S₁) (tree-to-pd (insertion-tree S₁ P T)) (exterior-sub S₁ P T)) refl≃s ⟩
      < pd-focus-tm (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
        [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm ∎

exterior-sub-Ty (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T
  = sub-from-connect-pd-Ty (susp-pd (tree-to-pd S₁))
                           (connect-pd-inc-left-Ty (susp-pd (tree-to-pd S₁)) (tree-to-ctx (insertion-tree S₂ P T)))
                           (apply-sub-sub-typing (exterior-sub-Ty S₂ P T)
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
              ∘ exterior-sub S₂ P T ]tm)
    lem = begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd S₁))
                                  (insertion-tree-size S₂ P T) ⟩
      < Var (fromℕ _) [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                             (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ sub-action-≃-tm (exterior-sub-fst-var S₂ P T) refl≃s ⟩
      < Var (fromℕ _)
          [ exterior-sub S₂ P T ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
        ≈˘⟨ assoc-tm _ (exterior-sub S₂ P T) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
            ∘ exterior-sub S₂ P T ]tm >tm ∎
