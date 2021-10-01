{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Insertion.Support where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Connection.Support
open import Catt.Connection.Properties
open import Catt.Suspension.Support
open import Data.Bool
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Connection
open import Catt.Suspension
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Discs.Properties
open import Data.Fin using (fromℕ)
open import Catt.Discs.Support
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Tree.Unbiased.Properties
open import Catt.Variables

insertion-tree-dim : (S : Tree n)
                   → (P : Path S)
                   → .⦃ _ : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ _ : has-linear-height (path-length P) T ⦄
                   → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                   → tree-dim S ≡ tree-dim (insertion-tree S P T)
insertion-tree-dim (Join S₁ S₂) PHere T ⦃ p = p ⦄ = begin
  suc (tree-dim S₁) ⊔ tree-dim S₂
    ≡⟨ cong (_⊔ tree-dim S₂) p ⟩
  tree-dim T ⊔ tree-dim S₂
    ≡˘⟨ connect-tree-dim T S₂ ⟩
  tree-dim (connect-tree T S₂) ∎
  where
    open ≡-Reasoning
insertion-tree-dim (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = cong (λ - → suc - ⊔ tree-dim S₂) (insertion-tree-dim S₁ P T ⦃ p = cong pred p ⦄)
insertion-tree-dim (Join S₁ S₂) (PShift P) T ⦃ p = p ⦄ = cong (suc (tree-dim S₁) ⊔_) (insertion-tree-dim S₂ P T)

exterior-sub-supp-full : (S : Tree n)
                       → (P : Path S)
                       → .⦃ _ : is-branching-path P ⦄
                       → (T : Tree m)
                       → .⦃ _ : has-linear-height (path-length P) T ⦄
                       → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                       → FVSub (exterior-sub S P T) ≡ full
exterior-sub-supp-full (Join S₁ S₂) PHere T = begin
  FVSub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                           ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           (idSub _) (tree-last-var T))
    ≡˘⟨ TransportVarSet-sub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                           ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           (idSub _) (tree-last-var T)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⟩
  TransportVarSet (FVSub (sub-between-connects
      (sub-from-disc-unbiased (suc (tree-dim S₁)) T
        ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
      (idSub (suc _)) (tree-last-var T)))
    (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
    ≡⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))) lem ⟩
  TransportVarSet full (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
    ≡⟨ TransportVarSet-full (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⟩
  FVSub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
    ≡⟨ idSub≃-supp (sym≃c (connect-tree-to-ctx T S₂)) ⟩
  full ∎
  where
    open ≡-Reasoning

    l2 : FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁))) ≡ full
    l2 = begin
      FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
        ≡˘⟨ TransportVarSet-sub (idSub≃ (linear-tree-compat (suspTree S₁))) (sub-from-disc-unbiased (suc (tree-dim S₁)) T) ⟩
      TransportVarSet (FVSub (idSub≃ (linear-tree-compat (suspTree S₁))))
        (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
        ≡⟨ cong (λ - → TransportVarSet - (sub-from-disc-unbiased (suc (tree-dim S₁)) T))
             (idSub≃-supp (linear-tree-compat (suspTree S₁))) ⟩
      TransportVarSet full (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
        ≡⟨ TransportVarSet-full (sub-from-disc-unbiased (suc (tree-dim S₁)) T) ⟩
      FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
        ≡⟨ sub-from-disc-supp (suc (tree-dim S₁)) (unbiased-type (suc (tree-dim S₁)) T) (unbiased-type-dim (suc (tree-dim S₁)) T) (unbiased-comp (suc (tree-dim S₁)) T (idSub _)) ⟩
      FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪
        FVTm (unbiased-comp (suc (tree-dim S₁)) T (idSub (suc _))) ≡⟨⟩
      FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪
        FVSub (idSub _)
        ≡⟨ cong (FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪_) (idSub-supp (suc _)) ⟩
      FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪ full
        ≡⟨ ∪-right-zero (FVTy (unbiased-type (suc (tree-dim S₁)) T)) ⟩
      full ∎

    lem : FVSub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                                      ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                                      (idSub (suc _))
                                      (tree-last-var T))
          ≡ full
    lem = begin
      FVSub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                                  ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                                  (idSub (suc _))
                                  (tree-last-var T))
        ≡⟨ sub-between-connect-supp (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                                  ∘ idSub≃ (linear-tree-compat (suspTree S₁))) (idSub _) (tree-last-var T) {!!} {!!} ⟩
      connect-supp (FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁))))
                   (FVSub (idSub (suc _)))
        ≡⟨ cong₂ connect-supp l2 (idSub-supp _) ⟩
      connect-supp full full
        ≡⟨ connect-supp-full _ _ ⟩
      full ∎

exterior-sub-supp-full (Join S₁ S₂) (PExt P) (Join T Sing) = begin
  FVSub (sub-between-connect-susps (exterior-sub S₁ P T) (idSub _))
    ≡⟨ sub-between-connect-susps-supp (exterior-sub S₁ P T) (idSub _) (id-on-tm (Var (fromℕ _))) ⟩
  connect-supp (suspSupp (FVSub (exterior-sub S₁ P T))) (FVSub (idSub (suc _)))
    ≡⟨ cong₂ connect-supp (trans (cong suspSupp (exterior-sub-supp-full S₁ P T ⦃ p = cong pred it ⦄)) suspSuppFull) (idSub-supp _) ⟩
  connect-supp full full
    ≡⟨ connect-supp-full (suc (suc (insertion-tree-size S₁ P T))) _ ⟩
  full ∎
  where
    open ≡-Reasoning
exterior-sub-supp-full (Join S₁ S₂) (PShift P) T = begin
  FVSub (sub-between-connect-susps (idSub _) (exterior-sub S₂ P T))
    ≡⟨ sub-between-connect-susps-supp (idSub _) (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T)) ⟩
  connect-supp (suspSupp (FVSub (idSub (suc _)))) (FVSub (exterior-sub S₂ P T))
    ≡⟨ cong₂ connect-supp (trans (cong suspSupp (idSub-supp _)) suspSuppFull) (exterior-sub-supp-full S₂ P T) ⟩
  connect-supp full full
    ≡⟨ connect-supp-full (suc (suc _)) (insertion-tree-size S₂ P T) ⟩
  full ∎
  where
    open ≡-Reasoning

exterior-sub-preserve-bd : (S : Tree n)
                         → (P : Path S)
                         → .⦃ _ : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                         → (b : Bool)
                         → TransportVarSet (supp-bd (pred (tree-dim S)) S b) (exterior-sub S P T)
                         ≡ supp-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) b
exterior-sub-preserve-bd (Join S₁ S₂) PHere T b = begin
  TransportVarSet
    (supp-bd (pred (tree-dim (Join S₁ S₂))) (Join S₁ S₂) b)
    (exterior-sub (Join S₁ S₂) PHere T)
    ≡⟨ lem (pred (tree-dim (Join S₁ S₂))) b ⟩
  supp-bd (pred (tree-dim (Join S₁ S₂))) (connect-tree T S₂) b
    ≡⟨ cong (λ - → supp-bd (pred -) (connect-tree T S₂) b) (insertion-tree-dim (Join S₁ S₂) PHere T) ⟩
  supp-bd (pred (tree-dim (insertion-tree (Join S₁ S₂) PHere T)))
    (connect-tree T S₂) b ∎
  where

    l2 : Var (fromℕ _)
            [ sub-from-disc-unbiased (suc (tree-dim S₁)) T
             ∘ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm
            ≃tm Var (fromℕ _)
    l2 = begin
      < Var (fromℕ _)
          [ sub-from-disc-unbiased (suc (tree-dim S₁)) T
            ∘ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm >tm
        ≈⟨ assoc-tm _ (idSub≃ (linear-tree-compat (suspTree S₁))) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm
          [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ sub-action-≃-tm (idSub≃-fst-var (linear-tree-compat (suspTree S₁))) refl≃s ⟩
      < Var (fromℕ _)
          [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ unbiased-type-disc-lem (suc (tree-dim S₁)) T (sym it) ⟩
      < Var (fromℕ (tree-size T)) >tm ∎
      where
        open Reasoning tm-setoid

    l1 : (Var (fromℕ _) [
         idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T)
         ]tm) ≃tm Var (fromℕ (connect-tree-length T S₂))
    l1 = begin
      < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
        ∘ sub-between-connects
        (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
         idSub≃ (linear-tree-compat (suspTree S₁)))
        (idSub (suc _)) (tree-last-var T) ]tm >tm
        ≈⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects
        (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
         idSub≃ (linear-tree-compat (suspTree S₁)))
        (idSub (suc _)) (tree-last-var T)) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
        [ sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                               idSub≃ (linear-tree-compat (suspTree S₁)))
                               (idSub (suc _)) (tree-last-var T) ]tm
        [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
        ≈⟨ sub-action-≃-tm (sub-between-connects-fst-var (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                               idSub≃ (linear-tree-compat (suspTree S₁))) (idSub _) (tree-last-var T) l2) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))}) ⟩
      < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
        ≈⟨ idSub≃-fst-var (sym≃c (connect-tree-to-ctx T S₂)) ⟩
      < Var (fromℕ (connect-tree-length T S₂)) >tm ∎
      where
        open Reasoning tm-setoid

    l4 : (getSnd [
            sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
            idSub≃ (linear-tree-compat (suspTree S₁))
            ]tm)
           ≃tm tree-last-var T
    l4 = begin
      < getSnd [ sub-from-disc-unbiased (suc (tree-dim S₁)) T
               ∘ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm >tm
        ≈⟨ assoc-tm (sub-from-disc-unbiased (suc (tree-dim S₁)) T) (idSub≃ (linear-tree-compat (suspTree S₁))) getSnd ⟩
      < getSnd [ idSub≃ (linear-tree-compat (suspTree S₁)) ]tm
               [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ sub-action-≃-tm (idSub≃-snd-var (linear-tree-compat (suspTree S₁))) refl≃s ⟩
      < getSnd [ sub-from-disc-unbiased (suc (tree-dim S₁)) T ]tm >tm
        ≈⟨ unbiased-type-disc-lem-2 (tree-dim S₁) T (sym it) ⟩
      < tree-last-var T >tm ∎
      where
        open Reasoning tm-setoid

    l3 : tree-last-var (Join S₁ S₂) [
         idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (linear-tree-compat (suspTree S₁)))
         (idSub (suc _)) (tree-last-var T)
         ]tm
         ≃tm tree-last-var (connect-tree T S₂)
    l3 = begin
      < tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
        [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (linear-tree-compat (suspTree S₁)))
         (idSub (suc _)) (tree-last-var T)
         ]tm >tm
        ≈˘⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
      < tree-last-var S₂ [
        idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
        sub-between-connects
        (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
         idSub≃ (linear-tree-compat (suspTree S₁)))
        (idSub (suc _)) (tree-last-var T)
        ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)
        ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (∘-assoc _ _ _) ⟩
      < tree-last-var S₂ [
        idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
        ∘ (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                               ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                               (idSub (suc _)) (tree-last-var T)
        ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (sub-between-connects-inc-right (sub-from-disc-unbiased (suc (tree-dim S₁)) T
                               ∘ idSub≃ (linear-tree-compat (suspTree S₁))) getSnd (idSub _) (tree-last-var T) l4 (id-on-tm (Var (fromℕ _)))) refl≃s) ⟩
      < tree-last-var S₂ [
        idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
        (connect-inc-right (tree-last-var T) _ ∘ idSub (suc _))
        ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (id-right-unit (connect-inc-right (tree-last-var T) _)) refl≃s) ⟩
      <
        tree-last-var S₂ [
        idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
        connect-inc-right (tree-last-var T) (tree-size S₂) ]tm >tm
        ≈˘⟨ connect-tree-last-var T S₂ ⟩
      < tree-last-var (connect-tree T S₂) >tm ∎
      where
        open Reasoning tm-setoid

    open ≡-Reasoning

    lem : (d : ℕ) → (b : Bool) → TransportVarSet
      (supp-bd d (Join S₁ S₂) b)
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       sub-between-connects
       (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
        idSub≃
        (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
         (disc-susp (tree-dim S₁)))) (idSub _) (tree-last-var T))
      ≡
      supp-bd d (connect-tree T S₂) b
    lem zero false = begin
      TransportVarSet (trueAt (fromℕ _))
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       sub-between-connects
       (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
        idSub≃
        (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
         (disc-susp (tree-dim S₁))))
       (idSub _) (tree-last-var T))
        ≡⟨ TransportVarSet-tm (Var (fromℕ _)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       sub-between-connects
       (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
        idSub≃
        (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
         (disc-susp (tree-dim S₁))))
       (idSub _) (tree-last-var T)) ⟩
      FVTm
        (Var (fromℕ _) [
         idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T)
         ]tm)
        ≡⟨ cong FVTm (≃tm-to-≡ l1) ⟩
      FVTm (Var (fromℕ (connect-tree-length T S₂))) ∎

    lem zero true = let
      instance _ = tree-last-var-is-var (Join S₁ S₂)
      instance _ = tree-last-var-is-var (connect-tree T S₂)
      in begin
      TransportVarSet (trueAt (getVarFin (tree-last-var (Join S₁ S₂))))
        (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T))
        ≡˘⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T))) (isVar-supp (tree-last-var (Join S₁ S₂))) ⟩
      TransportVarSet (FVTm (tree-last-var (Join S₁ S₂)))
        (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T))
        ≡⟨ TransportVarSet-tm (tree-last-var (Join S₁ S₂)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T)) ⟩
      FVTm
        (tree-last-var (Join S₁ S₂) [
         idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
          idSub≃
          (trans≃c (susp-ctx-≃ (linear-tree-compat S₁))
           (disc-susp (tree-dim S₁))))
         (idSub (suc _)) (tree-last-var T)
         ]tm)
        ≡⟨ cong FVTm (≃tm-to-≡ l3) ⟩
      FVTm (tree-last-var (connect-tree T S₂))
        ≡⟨ isVar-supp (tree-last-var (connect-tree T S₂)) ⟩
      trueAt (getVarFin (tree-last-var (connect-tree T S₂))) ∎

    lem (suc d) b = begin
      TransportVarSet
      (connect-supp (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b))
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       sub-between-connects
       (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
        idSub≃ (linear-tree-compat (suspTree S₁)))
       (idSub _) (tree-last-var T))
        ≡⟨ TransportVarSet-comp (connect-supp (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects
       (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
        idSub≃ (linear-tree-compat (suspTree S₁)))
       (idSub _) (tree-last-var T)) ⟩
      TransportVarSet
        (TransportVarSet
         (connect-supp (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b))
         (sub-between-connects
          (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
           idSub≃ (linear-tree-compat (suspTree S₁)))
          (idSub (suc _)) (tree-last-var T)))
        (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
        ≡⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))) l5 ⟩
      TransportVarSet
        (connect-supp (supp-bd d T b) (supp-bd (suc d) S₂ b))
        (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
        ≡⟨ {!!} ⟩
      supp-bd (suc d) (connect-tree T S₂) b ∎
        where
          l5 : TransportVarSet
                 (connect-supp (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b))
                 (sub-between-connects
                  (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                   idSub≃ (linear-tree-compat (suspTree S₁)))
                  (idSub (suc _)) (tree-last-var T))
                 ≡ connect-supp (supp-bd d T b) (supp-bd (suc d) S₂ b)
          l5 = begin
            TransportVarSet
              (connect-supp (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b))
              (sub-between-connects
               (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                idSub≃ (linear-tree-compat (suspTree S₁)))
               (idSub (suc _)) (tree-last-var T))
              ≡⟨ sub-between-connect-Transport (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                idSub≃ (linear-tree-compat (suspTree S₁))) (idSub _) (tree-last-var T) (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b) getSnd {!!} {!!} {!!} ⟩
            connect-supp
              (TransportVarSet (suspSupp (supp-bd d S₁ b))
               (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘
                idSub≃ (linear-tree-compat (suspTree S₁))))
              (TransportVarSet (supp-bd (suc d) S₂ b) (idSub (suc _)))
              ≡⟨ {!!} ⟩
            connect-supp (supp-bd d T b) (supp-bd (suc d) S₂ b) ∎


exterior-sub-preserve-bd (Join S₁ S₂) (PExt P) T b = {!!}
exterior-sub-preserve-bd (Join S₁ S₂) (PShift P) T b = {!!}

insertion-supp-condition : (b : Bool)
                         → (A : Ty (suc n))
                         → (S : Tree n)
                         → (P : Path S)
                         → .⦃ _ : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                         → supp-condition b A S
                         → supp-condition b (A [ exterior-sub S P T ]ty) (insertion-tree S P T)
insertion-supp-condition false A S P T sc = begin
  FVTy (A [ exterior-sub S P T ]ty)
    ≡˘⟨ TransportVarSet-ty A (exterior-sub S P T) ⟩
  TransportVarSet (FVTy A) (exterior-sub S P T)
    ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc ⟩
  TransportVarSet full (exterior-sub S P T)
    ≡⟨ TransportVarSet-full (exterior-sub S P T) ⟩
  FVSub (exterior-sub S P T)
    ≡⟨ exterior-sub-supp-full S P T ⟩
  full ∎
  where
    open ≡-Reasoning
insertion-supp-condition true (s ─⟨ A ⟩⟶ t) S P T ⦃ p = p ⦄ (nz ,, sc1 ,, sc2)
  = NonZero′-subst (insertion-tree-dim S P T) nz ,, l1 ,, l2
  where
    open ≡-Reasoning

    l1 : FVTy (A [ exterior-sub S P T ]ty) ∪
           FVTm (s [ exterior-sub S P T ]tm)
           ≡
           supp-bd (pred (tree-dim (insertion-tree S P T)))
           (insertion-tree S P T) false
    l1 = begin
      FVTy (A [ exterior-sub S P T ]ty) ∪
        FVTm (s [ exterior-sub S P T ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm s (exterior-sub S P T)) ⟩
      TransportVarSet (FVTy A) (exterior-sub S P T) ∪
        TransportVarSet (FVTm s) (exterior-sub S P T)
        ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm s) (exterior-sub S P T) ⟩
      TransportVarSet (FVTy A ∪ FVTm s) (exterior-sub S P T)
        ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc1 ⟩
      TransportVarSet (supp-bd (pred (tree-dim S)) S false) (exterior-sub S P T)
        ≡⟨ exterior-sub-preserve-bd S P T false ⟩
      supp-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) false ∎

    l2 : FVTy (A [ exterior-sub S P T ]ty) ∪
           FVTm (t [ exterior-sub S P T ]tm)
           ≡
           supp-bd (pred (tree-dim (insertion-tree S P T)))
           (insertion-tree S P T) true
    l2 = begin
      FVTy (A [ exterior-sub S P T ]ty) ∪
        FVTm (t [ exterior-sub S P T ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm t (exterior-sub S P T)) ⟩
      TransportVarSet (FVTy A) (exterior-sub S P T) ∪
        TransportVarSet (FVTm t) (exterior-sub S P T)
        ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm t) (exterior-sub S P T) ⟩
      TransportVarSet (FVTy A ∪ FVTm t) (exterior-sub S P T)
        ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc2 ⟩
      TransportVarSet (supp-bd (pred (tree-dim S)) S true) (exterior-sub S P T)
        ≡⟨ exterior-sub-preserve-bd S P T true ⟩
      supp-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) true ∎
