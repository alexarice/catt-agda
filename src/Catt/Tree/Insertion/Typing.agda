{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Tree.Insertion.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Discs.Typing index rule lift-rule
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Unbiased.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning

interior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T)) (interior-sub S P T)
interior-sub-Ty (Join S₁ S₂) PHere T = apply-sub-sub-typing (connect-inc-left-Ty (tree-last-var-Ty T) (tree-to-ctx S₂)) (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)))
interior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing) = apply-sub-sub-typing (suspSubTy (interior-sub-Ty S₁ P T)) (connect-susp-inc-left-Ty (tree-to-ctx (insertion-tree S₁ P T)) (tree-to-ctx S₂))
interior-sub-Ty (Join S₁ S₂) (PShift P) T = apply-sub-sub-typing (interior-sub-Ty S₂ P T) (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx (insertion-tree S₂ P T)))

exterior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → .⦃ _ : is-branching-path P ⦄
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T)) (exterior-sub S P T)
exterior-sub-Ty (Join S₁ S₂) PHere T
  = apply-sub-sub-typing
      (sub-between-connects-Ty
        (apply-sub-sub-typing
          (idSub≃-Ty (linear-tree-compat (suspTree S₁)))
          (sub-from-disc-unbiased-Ty (suc (tree-dim S₁)) T it))
        id-Ty
        (tree-last-var-Ty T)
        (reflexive≈tm lem)
        (reflexive≈tm (id-on-tm (Var (fromℕ _)))))
      (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)))
  where
    lem : getSnd [ sub-from-disc-unbiased (suc (tree-dim S₁)) T
             ∘ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm
          ≃tm tree-last-var T
    lem = begin
      < getSnd [ sub-from-disc-unbiased (suc (tree-dim S₁)) T
               ∘ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm >tm
        ≈⟨ assoc-tm _ (idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁)))) getSnd ⟩
      < getSnd [ idSub≃ (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁))) ]tm
               [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ sub-action-≃-tm {t = getSnd} (idSub≃-snd-var (trans≃c (susp-ctx-≃ (linear-tree-compat S₁)) (disc-susp (tree-dim S₁)))) refl≃s ⟩
      < getSnd [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ unbiased-type-disc-lem-2 (tree-dim S₁) T (sym it) ⟩
      < tree-last-var T >tm ∎
      where
        open Reasoning tm-setoid
exterior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing) = sub-between-connect-susps-Ty (exterior-sub-Ty S₁ P T ⦃ p = cong pred it ⦄) id-Ty (reflexive≈tm (id-on-tm (Var (fromℕ _))))
exterior-sub-Ty (Join S₁ S₂) (PShift P) T = sub-between-connect-susps-Ty id-Ty (exterior-sub-Ty S₂ P T) (reflexive≈tm (sym≃tm (exterior-sub-fst-var S₂ P T)))
