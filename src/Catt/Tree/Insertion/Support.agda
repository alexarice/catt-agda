{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Insertion.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Connection.Support
open import Catt.Connection.Properties
open import Catt.Suspension.Support
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Connection
open import Catt.Suspension
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Variables
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Catt.Tree.Pasting

insertion-tree-dim : (S : Tree n)
                   → (P : Path S)
                   → .⦃ _ : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ _ : has-linear-height (path-length P) T ⦄
                   → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                   → tree-dim S ≡ tree-dim (insertion-tree S P T)
insertion-tree-dim (Join S₁ S₂) PHere T ⦃ p = p ⦄ = begin
  max (suc (tree-dim S₁)) (tree-dim S₂)
    ≡⟨ cong (λ - → max - (tree-dim S₂)) p ⟩
  max (tree-dim T) (tree-dim S₂)
    ≡˘⟨ connect-tree-dim T S₂ ⟩
  tree-dim (connect-tree T S₂) ∎
  where
    open ≡-Reasoning
insertion-tree-dim (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = cong (λ - → max (suc -) (tree-dim S₂)) (insertion-tree-dim S₁ P T ⦃ p = trans (cong pred p) (max-lem (tree-dim T)) ⦄)
insertion-tree-dim (Join S₁ S₂) (PShift P) T ⦃ p = p ⦄ = cong (max (suc (tree-dim S₁))) (insertion-tree-dim S₂ P T)

-- exterior-sub-supp-full : (S : Tree n)
--                        → (P : Path S)
--                        → .⦃ _ : is-branching-path P ⦄
--                        → (T : Tree m)
--                        → .⦃ _ : has-linear-height (path-length P) T ⦄
--                        → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
--                        → FVSub (exterior-sub S P T) ≡ full
-- exterior-sub-supp-full (Join S₁ S₂) PHere T = begin
--   FVSub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
--     ∘ sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--                            ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--                            (idSub _) (tree-last-var T))
--     ≡˘⟨ TransportVarSet-sub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--                            ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--                            (idSub _) (tree-last-var T)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⟩
--   TransportVarSet (FVSub (sub-between-connects
--       (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--         ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--       (idSub (suc _)) (tree-last-var T)))
--     (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
--     ≡⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))) lem ⟩
--   TransportVarSet full (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
--     ≡⟨ TransportVarSet-full (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) ⟩
--   FVSub (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
--     ≡⟨ idSub≃-supp (sym≃c (connect-tree-to-ctx T S₂)) ⟩
--   full ∎
--   where
--     open ≡-Reasoning

--     l2 : FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁))) ≡ full
--     l2 = begin
--       FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--         ≡˘⟨ TransportVarSet-sub (idSub≃ (linear-tree-compat (suspTree S₁))) (sub-from-disc-unbiased (suc (tree-dim S₁)) T) ⟩
--       TransportVarSet (FVSub (idSub≃ (linear-tree-compat (suspTree S₁))))
--         (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
--         ≡⟨ cong (λ - → TransportVarSet - (sub-from-disc-unbiased (suc (tree-dim S₁)) T))
--              (idSub≃-supp (linear-tree-compat (suspTree S₁))) ⟩
--       TransportVarSet full (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
--         ≡⟨ TransportVarSet-full (sub-from-disc-unbiased (suc (tree-dim S₁)) T) ⟩
--       FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T)
--         ≡⟨ sub-from-disc-supp (suc (tree-dim S₁)) (unbiased-type (suc (tree-dim S₁)) T) (unbiased-type-dim (suc (tree-dim S₁)) T) (unbiased-comp (suc (tree-dim S₁)) T (idSub _)) ⟩
--       FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪
--         FVTm (unbiased-comp (suc (tree-dim S₁)) T (idSub (suc _))) ≡⟨⟩
--       FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪
--         FVSub (idSub _)
--         ≡⟨ cong (FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪_) (idSub-supp (suc _)) ⟩
--       FVTy (unbiased-type (suc (tree-dim S₁)) T) ∪ full
--         ≡⟨ ∪-right-zero (FVTy (unbiased-type (suc (tree-dim S₁)) T)) ⟩
--       full ∎

--     lem : FVSub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--                                       ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--                                       (idSub (suc _))
--                                       (tree-last-var T))
--           ≡ full
--     lem = begin
--       FVSub (sub-between-connects (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--                                   ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
--                                   (idSub (suc _))
--                                   (tree-last-var T))
--         ≡⟨ sub-between-connect-supp (sub-from-disc-unbiased (suc (tree-dim S₁)) T
--                                   ∘ idSub≃ (linear-tree-compat (suspTree S₁))) (idSub _) (tree-last-var T) {!!} {!!} ⟩
--       connect-supp (FVSub (sub-from-disc-unbiased (suc (tree-dim S₁)) T ∘ idSub≃ (linear-tree-compat (suspTree S₁))))
--                    (FVSub (idSub (suc _)))
--         ≡⟨ cong₂ connect-supp l2 (idSub-supp _) ⟩
--       connect-supp full full
--         ≡⟨ connect-supp-full _ _ ⟩
--       full ∎

-- exterior-sub-supp-full (Join S₁ S₂) (PExt P) (Join T Sing) = begin
--   FVSub (sub-between-connect-susps (exterior-sub S₁ P T) (idSub _))
--     ≡⟨ sub-between-connect-susps-supp (exterior-sub S₁ P T) (idSub _) (id-on-tm (Var (fromℕ _))) ⟩
--   connect-supp (suspSupp (FVSub (exterior-sub S₁ P T))) (FVSub (idSub (suc _)))
--     ≡⟨ cong₂ connect-supp (trans (cong suspSupp (exterior-sub-supp-full S₁ P T ⦃ p = cong pred it ⦄)) suspSuppFull) (idSub-supp _) ⟩
--   connect-supp full full
--     ≡⟨ connect-supp-full (suc (suc (insertion-tree-size S₁ P T))) _ ⟩
--   full ∎
--   where
--     open ≡-Reasoning
-- exterior-sub-supp-full (Join S₁ S₂) (PShift P) T = begin
--   FVSub (sub-between-connect-susps (idSub _) (exterior-sub S₂ P T))
--     ≡⟨ sub-between-connect-susps-supp (idSub _) (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T)) ⟩
--   connect-supp (suspSupp (FVSub (idSub (suc _)))) (FVSub (exterior-sub S₂ P T))
--     ≡⟨ cong₂ connect-supp (trans (cong suspSupp (idSub-supp _)) suspSuppFull) (exterior-sub-supp-full S₂ P T) ⟩
--   connect-supp full full
--     ≡⟨ connect-supp-full (suc (suc _)) (insertion-tree-size S₂ P T) ⟩
--   full ∎
--   where
--     open ≡-Reasoning

exterior-sub-preserve-bd : (d : ℕ)
                         → (S : Tree n)
                         → (P : Path S)
                         → .⦃ _ : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                         → (b : Bool)
                         → TransportVarSet (supp-tree-bd d S b) (exterior-sub S P T)
                         ≡ supp-tree-bd d (insertion-tree S P T) b
exterior-sub-preserve-bd zero S P T false = begin
  TransportVarSet (FVTm (Var (fromℕ _))) (exterior-sub S P T)
    ≡⟨ TransportVarSet-tm (Var (fromℕ _)) (exterior-sub S P T) ⟩
  FVTm (Var (fromℕ _) [ exterior-sub S P T ]tm)
       ≡˘⟨ cong FVTm (≃tm-to-≡ (exterior-sub-fst-var S P T)) ⟩
  FVTm (Var (fromℕ _))
    ≡⟨⟩
  trueAt (fromℕ (insertion-tree-size S P T)) ∎
  where
    open ≡-Reasoning
exterior-sub-preserve-bd zero S P T true = let
  instance _ = tree-last-var-is-var S
  in begin
  -- TransportVarSet (trueAt (getVarFin (tree-last-var S))) (exterior-sub S P T)
  --   ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (isVar-supp (tree-last-var S)) ⟩
  TransportVarSet (FVTm (tree-last-var S)) (exterior-sub S P T)
    ≡⟨ TransportVarSet-tm (tree-last-var S) (exterior-sub S P T) ⟩
  FVTm (tree-last-var S [ exterior-sub S P T ]tm)
    ≡˘⟨ cong FVTm (≃tm-to-≡ (exterior-sub-last-var S P T)) ⟩
  FVTm (tree-last-var (insertion-tree S P T))
    ≡⟨⟩
    -- ≡⟨ isVar-supp (tree-last-var (insertion-tree S P T)) ⦃ tree-last-var-is-var (insertion-tree S P T) ⦄ ⟩
  supp-tree-bd zero (insertion-tree S P T) true ∎
  where
    open ≡-Reasoning
exterior-sub-preserve-bd (suc d) (Join S₁ S₂) PHere T b = begin
  TransportVarSet (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
    (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
                           idSub
                           (tree-last-var T))
    ≡⟨ TransportVarSet-comp (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
                           idSub
                           (tree-last-var T)) ⟩
  TransportVarSet
    (TransportVarSet
     (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
     (sub-between-connects
      (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
      (tree-last-var T)))
    (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
    ≡⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))))
         lem ⟩
  TransportVarSet
    (connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b))
    (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
    ≡⟨ connect-tree-to-ctx-supp d T S₂ b ⟩
  supp-tree-bd (suc d) (connect-tree T S₂) b ∎
  where
    l1 : Var (fromℕ _) [ connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub ]tm
           ≃tm
         getSnd [ connect-inc-left (tree-last-var T) (tree-size S₂)
                ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
    l1 = begin
      < Var (fromℕ _) [ connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ _)}) (id-right-unit (connect-inc-right (tree-last-var T) (tree-size S₂))) ⟩
      < Var (fromℕ _) [ connect-inc-right (tree-last-var T) _ ]tm >tm
        ≈˘⟨ connect-inc-fst-var (tree-last-var T) (tree-size S₂) ⟩
      < tree-last-var T [ connect-inc-left (tree-last-var T) (tree-size S₂) ]tm >tm
        ≈⟨ sub-action-≃-tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1)) refl≃s ⟩
      < getSnd [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
               [ connect-inc-left (tree-last-var T) (tree-size S₂) ]tm >tm
        ≈˘⟨ assoc-tm (connect-inc-left (tree-last-var T) (tree-size S₂)) (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd ⟩
      < getSnd [ connect-inc-left (tree-last-var T) (tree-size S₂)
               ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : FVTm (tree-last-var T) ⊆
           TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
           (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
    l2 = begin
      FVTm (tree-last-var T)
        ≤⟨ supp-tree-bd-include-last d T b ⟩
      supp-tree-bd (suc d) T b
        ≡˘⟨ sub-from-linear-tree-supp (suc d) (suspTree S₁) b T (sym (trans (max-lem (suc (tree-dim S₁))) it)) ⟩
      TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
        (sub-from-linear-tree-unbiased (suspTree S₁) T 0) ∎
      where
        open PReasoning (⊆-poset (suc _))

    open ≡-Reasoning

    lem : TransportVarSet
     (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
     (sub-between-connects
      (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
      (tree-last-var T)) ≡ connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b)
    lem = begin
      TransportVarSet
        (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
        (sub-between-connects
         (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
         (tree-last-var T))
        ≡⟨ sub-between-connect-Transport (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub (tree-last-var T) (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b) getSnd l1 (suspSuppSndTruth (supp-tree-bd d S₁ b)) l2 ⟩
      connect-supp
        (TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
         (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)))
        (TransportVarSet (supp-tree-bd (suc d) S₂ b) idSub)
        ≡⟨ cong₂ connect-supp (sub-from-linear-tree-supp (suc d) (suspTree S₁) b T (sym (trans (max-lem (suc (tree-dim S₁))) it))) (TransportVarSet-id (supp-tree-bd (suc d) S₂ b)) ⟩
      connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b) ∎

exterior-sub-preserve-bd (suc d) (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ b = begin
  TransportVarSet
      (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
      (sub-between-connect-susps (exterior-sub S₁ P T)
       idSub)
    ≡⟨ sub-between-connect-susps-Transport (exterior-sub S₁ P T) idSub (supp-tree-bd d S₁ b) (supp-tree-bd (suc d) S₂ b) (id-on-tm (Var (fromℕ _))) ⟩
  connect-supp
    (suspSupp (TransportVarSet (supp-tree-bd d S₁ b) (exterior-sub S₁ P T)))
    (TransportVarSet (supp-tree-bd (suc d) S₂ b) idSub)
    ≡⟨ cong₂ (λ a → connect-supp (suspSupp a)) (exterior-sub-preserve-bd d S₁ P T ⦃ p = trans (cong pred p) (max-lem (tree-dim T)) ⦄ b) (TransportVarSet-id (supp-tree-bd (suc d) S₂ b)) ⟩
  connect-supp (suspSupp (supp-tree-bd d (insertion-tree S₁ P T) b))
      (supp-tree-bd (suc d) S₂ b) ∎
  where
    open ≡-Reasoning
exterior-sub-preserve-bd (suc d) (Join S₁ S₂) (PShift P) T b = begin
  TransportVarSet
      (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
      (sub-between-connect-susps
       idSub (exterior-sub S₂ P T))
    ≡⟨ sub-between-connect-susps-Transport idSub (exterior-sub S₂ P T) (supp-tree-bd d S₁ b) (supp-tree-bd (suc d) S₂ b) (sym≃tm (exterior-sub-fst-var S₂ P T)) ⟩
  connect-supp
    (suspSupp (TransportVarSet (supp-tree-bd d S₁ b) idSub))
    (TransportVarSet (supp-tree-bd (suc d) S₂ b) (exterior-sub S₂ P T))
    ≡⟨ cong₂ (λ a → connect-supp (suspSupp a)) (TransportVarSet-id (supp-tree-bd d S₁ b)) (exterior-sub-preserve-bd (suc d) S₂ P T b) ⟩
  connect-supp (suspSupp (supp-tree-bd d S₁ b))
      (supp-tree-bd (suc d) (insertion-tree S₂ P T) b) ∎
  where
    open ≡-Reasoning

exterior-sub-supp-full : (S : Tree n)
                       → (P : Path S)
                       → .⦃ _ : is-branching-path P ⦄
                       → (T : Tree m)
                       → .⦃ _ : has-linear-height (path-length P) T ⦄
                       → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                       → FVSub (exterior-sub S P T) ≡ full
exterior-sub-supp-full S P T = begin
  FVSub (exterior-sub S P T)
    ≡˘⟨ TransportVarSet-full (exterior-sub S P T) ⟩
  TransportVarSet full (exterior-sub S P T)
    ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (supp-tree-bd-full (tree-dim S) S false ≤-refl) ⟩
  TransportVarSet (supp-tree-bd (tree-dim S) S false) (exterior-sub S P T)
    ≡⟨ exterior-sub-preserve-bd (tree-dim S) S P T false ⟩
  supp-tree-bd (tree-dim S) (insertion-tree S P T) false
    ≡⟨ supp-tree-bd-full (tree-dim S) (insertion-tree S P T) false (≤-reflexive (sym (insertion-tree-dim S P T))) ⟩
  full ∎
  where
    open ≡-Reasoning


insertion-supp-condition : (b : Bool)
                         → (A : Ty (suc n))
                         → (S : Tree n)
                         → (P : Path S)
                         → .⦃ _ : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
                         → supp-condition b A (tree-to-ctx S) ⦃ tree-to-pd S ⦄
                         → supp-condition b (A [ exterior-sub S P T ]ty) (tree-to-ctx (insertion-tree S P T)) ⦃ tree-to-pd (insertion-tree S P T) ⦄
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
  = NonZero-subst ? nz ,, l1 ,, l2
  where
    open ≡-Reasoning

    l1 : FVTy (A [ exterior-sub S P T ]ty) ∪
           FVTm (s [ exterior-sub S P T ]tm)
           ≡
           supp-tree-bd (pred (tree-dim (insertion-tree S P T)))
           (insertion-tree S P T) false
    l1 = begin
      FVTy (A [ exterior-sub S P T ]ty) ∪
        FVTm (s [ exterior-sub S P T ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm s (exterior-sub S P T)) ⟩
      TransportVarSet (FVTy A) (exterior-sub S P T) ∪
        TransportVarSet (FVTm s) (exterior-sub S P T)
        ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm s) (exterior-sub S P T) ⟩
      TransportVarSet (FVTy A ∪ FVTm s) (exterior-sub S P T)
        ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) ? ⟩
      TransportVarSet (supp-tree-bd (pred (tree-dim S)) S false) (exterior-sub S P T)
        ≡⟨ exterior-sub-preserve-bd (pred (tree-dim S)) S P T false ⟩
      supp-tree-bd (pred (tree-dim S)) (insertion-tree S P T) false
        ≡⟨ cong (λ - → supp-tree-bd (pred -) (insertion-tree S P T) false) (insertion-tree-dim S P T) ⟩
      supp-tree-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) false ∎

    l2 : FVTy (A [ exterior-sub S P T ]ty) ∪
           FVTm (t [ exterior-sub S P T ]tm)
           ≡
           supp-tree-bd (pred (tree-dim (insertion-tree S P T)))
           (insertion-tree S P T) true
    l2 = begin
      FVTy (A [ exterior-sub S P T ]ty) ∪
        FVTm (t [ exterior-sub S P T ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm t (exterior-sub S P T)) ⟩
      TransportVarSet (FVTy A) (exterior-sub S P T) ∪
        TransportVarSet (FVTm t) (exterior-sub S P T)
        ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm t) (exterior-sub S P T) ⟩
      TransportVarSet (FVTy A ∪ FVTm t) (exterior-sub S P T)
        ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) ? ⟩
      TransportVarSet (supp-tree-bd (pred (tree-dim S)) S true) (exterior-sub S P T)
        ≡⟨ exterior-sub-preserve-bd (pred (tree-dim S)) S P T true ⟩
      supp-tree-bd (pred (tree-dim S)) (insertion-tree S P T) true
        ≡⟨ cong (λ - → supp-tree-bd (pred -) (insertion-tree S P T) true) (insertion-tree-dim S P T) ⟩
      supp-tree-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) true ∎

    l3 : (b : Bool) → (T : Tree n) → supp-tree-bd (pred (tree-dim T)) T ≡
