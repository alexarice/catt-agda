{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Insertion
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
-- open import Catt.Unsuspension
open import Catt.Pasting.Unbiased
open import Catt.Pasting.Unbiased.Properties
open import Catt.Discs
open import Data.Fin using (Fin; zero; suc; fromℕ; inject₁)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Data.Sum
open import Relation.Nullary


exterior-sub-fst-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
                     → Var {suc (insertion-tree-size S P T)} (fromℕ _) ≃tm Var (fromℕ _) [ exterior-sub S P T ]tm
exterior-sub-fst-var (Join S₁ S₂) PHere T ⦃ p = p ⦄ = begin
  < Var (fromℕ (insertion-tree-size (Join S₁ S₂) PHere T)) >tm
    ≈˘⟨ idSub≃-fst-var (sym≃c (connect-tree-to-ctx T S₂)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm lem refl≃s ⟩
  < Var (fromℕ _)
    [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
                            ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
                            ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ p)))
                          (connect-pd-inc-right (tree-to-pd T) (tree-size S₂)) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈˘⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
                            ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
                            ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ p)))
                          (connect-pd-inc-right (tree-to-pd T) (tree-size S₂))) (Var (fromℕ _)) ⟩
  < Var (fromℕ _)
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
                            ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
                            ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ p)))
                          (connect-pd-inc-right (tree-to-pd T) (tree-size S₂)) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm ∎
  where
    open Reasoning tm-setoid

    lem : Var (fromℕ (tree-size S₂ + tree-size T)) ≃tm
          Var (fromℕ _)
            [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
                            ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
                            ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ p)))
                          (connect-pd-inc-right (tree-to-pd T) (tree-size S₂)) ]tm
    lem = begin
      < Var (fromℕ _) >tm
        ≈˘⟨ connect-pd-inc-left-fst-var (tree-to-pd T) (tree-size S₂) ⟩
      < Var (fromℕ _)
        [ connect-pd-inc-left (tree-to-pd T) (tree-size S₂) ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-type-disc-fst-var-lem′ (tree-to-pd T) p) refl≃s ⟩
      < Var (fromℕ _)
        [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm
        [ connect-pd-inc-left (tree-to-pd T) (tree-size S₂) ]tm
        >tm
        ≈˘⟨ assoc-tm _ (sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
        [ connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm
        ≈˘⟨ sub-action-≃-tm (idSub≃-fst-var (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _))) refl≃s ⟩
      < Var (fromℕ _)
          [ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _)) ]tm
          [ connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
            ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm
        ≈˘⟨ assoc-tm _ (idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _))) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
        [ connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
          ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
          ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _)) ]tm >tm
        ≈˘⟨ sub-from-connect-pd-fst-var (susp-pd (tree-to-pd S₁))
            (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
              ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
              ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _)))
            (connect-pd-inc-right (tree-to-pd T) (tree-size S₂)) ⟩
      < Var (fromℕ _)
          [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
            (connect-pd-inc-left (tree-to-pd T) (tree-size S₂)
              ∘ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
              ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ _)))
            (connect-pd-inc-right (tree-to-pd T) (tree-size S₂)) ]tm >tm ∎

exterior-sub-fst-var (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = let
  instance .x : _
           x = cong pred p
  in begin
  < Var (fromℕ _) >tm
    ≈˘⟨ connect-pd-inc-left-fst-var (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ⟩
  < Var (fromℕ _)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-sub-preserve-getFst (exterior-sub S₁ P T)) refl≃s ⟩
  < Var (fromℕ _)
      [ suspSub (exterior-sub S₁ P T) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈˘⟨ assoc-tm (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) (suspSub (exterior-sub S₁ P T)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
    ≈˘⟨ sub-from-connect-pd-fst-var
         (susp-pd (tree-to-pd S₁))
         (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
           ∘ suspSub (exterior-sub S₁ P T))
         (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ⟩
  < Var (fromℕ _)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
                              ∘ suspSub (exterior-sub S₁ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) ]tm >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-fst-var (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T = begin
  < Var (fromℕ _) >tm
    ≈˘⟨ connect-pd-inc-left-fst-var (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ⟩
  < Var (fromℕ _) [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
    ≈˘⟨ sub-from-connect-pd-fst-var (susp-pd (tree-to-pd S₁)) (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)) (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ∘ exterior-sub S₂ P T) ⟩
  < Var (fromℕ _)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                   (insertion-tree-size S₂ P T)
                              ∘ exterior-sub S₂ P T) ]tm >tm
       ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) (PShift P) T ]tm >tm ∎
  where
    open Reasoning tm-setoid

{-
insertion-eq : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
             → branching-path-to-var S P [ exterior-sub S P T ]tm ≃tm Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (interior-sub S P T)
insertion-eq S (PHere .S) T = begin
  < 0V [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
       ∘ idSub≃ (disc-≡ it)
       ∘ idSub≃ (linear-tree-compat S) ]tm >tm
    ≈⟨ assoc-tm _ (idSub≃ (linear-tree-compat S)) 0V ⟩
  < 0V [ idSub≃ (linear-tree-compat S) ]tm
       [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
       ∘ idSub≃ (disc-≡ it) ]tm >tm
    ≈⟨ sub-action-≃-tm (trans≃tm (idSub≃-on-tm (linear-tree-compat S) 0V) (Var≃ (≃c-preserve-length (linear-tree-compat S)) refl)) refl≃s ⟩
  < 0V [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _)))
       ∘ idSub≃ (disc-≡ it) ]tm >tm
    ≈⟨ assoc-tm _ (idSub≃ (disc-≡ it)) 0V ⟩
  < 0V [ idSub≃ (disc-≡ it) ]tm
       [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm
    ≈⟨ sub-action-≃-tm (trans≃tm (idSub≃-on-tm (disc-≡ it) 0V) (Var≃ (≃c-preserve-length (disc-≡ it)) refl)) refl≃s ⟩
  < 0V [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub (suc _))) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (interior-sub S (PHere S) T) >tm ∎
  where open Reasoning tm-setoid
insertion-eq (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = let
  instance .x : _
           x = cong pred p
  in begin
  < branching-path-to-var (Join S₁ S₂) (PExt P)
      [ exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) ]tm >tm ≡⟨⟩
  < suspTm (branching-path-to-var S₁ P)
     [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
     [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                           (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                (tree-size S₂)
                           ∘ suspSub (exterior-sub S₁ P T))
                           (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                 (tree-size S₂))
       ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                 (tree-size S₂)
                            ∘ suspSub (exterior-sub S₁ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                  (tree-size S₂))
      ∘ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P)})
                       (sub-from-connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                     (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                                          (tree-size S₂)
                                                     ∘ suspSub (exterior-sub S₁ P T))
                                                     (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                                           (tree-size S₂))) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                            (tree-size S₂)
      ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
    ≈⟨ assoc-tm _ (suspSub (exterior-sub S₁ P T)) (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ suspSub (exterior-sub S₁ P T) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm lem refl≃s ⟩
  < Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (idSub _)
      [ suspSub (interior-sub S₁ P T) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈˘⟨ assoc-tm _ (suspSub (interior-sub S₁ P T)) (Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (idSub _)) ⟩
  < Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (idSub (suc (0 + (2 + _))))
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (interior-sub S₁ P T) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (interior-sub S₁ P T)
      ∘ idSub (suc (0 + (2 + _)))) >tm
    ≈⟨ Coh≃ refl≃c refl≃ty (id-right-unit _) ⟩
  < Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) >tm ∎
  where
    open Reasoning tm-setoid
    lem : suspTm (branching-path-to-var S₁ P)
            [ suspSub (exterior-sub S₁ P T ⦃ p = cong pred p ⦄) ]tm
          ≃tm
          Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (idSub _)
            [ suspSub (interior-sub S₁ P T) ]tm
    lem = let
      instance .x : _
               x = cong pred p
      in begin
      < suspTm (branching-path-to-var S₁ P)
        [ suspSub (exterior-sub S₁ P T) ]tm >tm
        ≈˘⟨ susp-functorial-tm (exterior-sub S₁ P T) (branching-path-to-var S₁ P) ⟩
      < suspTm (branching-path-to-var S₁ P [ exterior-sub S₁ P T ]tm) >tm
        ≈⟨ susp-tm-≃ (insertion-eq S₁ P T) ⟩
      < Coh (suspCtx (tree-to-ctx T)) (suspTy (unbiased-type (tree-to-pd T))) (suspSub (interior-sub S₁ P T)) >tm
        ≈˘⟨ Coh≃ refl≃c (susp-unbiased-type (tree-to-pd T)) (id-right-unit (suspSub (interior-sub S₁ P T))) ⟩
      < Coh (tree-to-ctx (Join T Sing)) (unbiased-type (tree-to-pd (Join T Sing))) (idSub _)
        [ suspSub (interior-sub S₁ P T) ]tm >tm ∎
insertion-eq (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T = let
  instance .l : is-branching-path P
           l = proj₁ bp
  in begin
  < branching-path-to-var (Join S₁ S₂) (PShift P)
    [ exterior-sub (Join S₁ S₂) (PShift P) T ]tm >tm
    ≡⟨⟩
  < branching-path-to-var S₂ P
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T)
       ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T)
      ∘ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P})
                       (sub-from-connect-pd-inc-right
                         (susp-pd (tree-to-pd S₁))
                         (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                              (insertion-tree-size S₂ P T))
                         (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                               (insertion-tree-size S₂ P T)
                         ∘ exterior-sub S₂ P T)
                         lem) ⟩
  < branching-path-to-var S₂ P
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                             (insertion-tree-size S₂ P T)
      ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ (exterior-sub S₂ P T) (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
      [ exterior-sub S₂ P T ]tm
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
    >tm ≈⟨ sub-action-≃-tm (insertion-eq S₂ P T) refl≃s ⟩
  <
    Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (interior-sub S₂ P T)
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
    >tm ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T))
      (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
       ∘ interior-sub S₂ P T) >tm ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (interior-sub (Join S₁ S₂) (PShift P) T) >tm ∎
  where
    open Reasoning tm-setoid
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
          ≃tm
          (Var (fromℕ _)
            [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
              ∘ exterior-sub S₂ P ⦃ proj₁ bp ⦄ T ]tm)
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
        ≈⟨ sub-action-≃-tm (exterior-sub-fst-var S₂ P T) refl≃s ⟩
      < Var (fromℕ _)
          [ exterior-sub S₂ P T ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
        ≈˘⟨ assoc-tm _ (exterior-sub S₂ P T) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
            ∘ exterior-sub S₂ P T ]tm >tm ∎
-}
lift-sub-from-insertion : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l)
                        → (τ : Sub (suc m) l)
                        → liftSub (sub-from-insertion S P T σ τ) ≃s sub-from-insertion S P T (liftSub σ) (liftSub τ)
lift-sub-from-insertion S P T σ τ = trans≃s (lift-sub-from-function (sub-from-insertion-func S P T σ τ)) (sub-from-function-≃ _ _ γ)
  where
    γ : (i : Fin (suc (insertion-tree-size S P T)))
      → liftTerm (sub-from-insertion-func S P T σ τ i)
        ≃tm sub-from-insertion-func S P T (liftSub σ) (liftSub τ) i
    γ i with insertion-var-split S P T i
    ... | inj₁ j = sym≃tm (apply-lifted-sub-tm-≃ (Var j) σ)
    ... | inj₂ j = sym≃tm (apply-lifted-sub-tm-≃ (Var j) τ)


exterior-sub-susp : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
             → exterior-sub (susp-tree S) (PExt P) (susp-tree T) ⦃ p = cong suc p ⦄ ≃s suspSub (exterior-sub S P T)
exterior-sub-susp S P T = begin
  < exterior-sub (susp-tree S) (PExt P) (susp-tree T) ⦃ p = cong suc it ⦄ >s ≡⟨⟩
  < idSub (2 + suc (insertion-tree-size S P T))
       ∘ suspSub (exterior-sub S P T ⦃ p = it ⦄) >s
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
                           → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
                           → VarSplitCompat (exterior-sub S P T) (interior-sub S P T) (insertion-var-split S P T)
insertion-var-split-compat S (PHere .S) T i = id-on-tm (Var i)
insertion-var-split-compat (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p′ ⦄ i with connect-pd-var-split (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) i | connect-pd-var-split-compat (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) i
... | inj₂ j | p = let
  instance _ = connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂)
  instance .x : _
           x = cong pred p′
  in begin
  < Var (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) j)
    [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ∘ (suspSub (exterior-sub S₁ P T)))
                          (connect-pd-inc-right
                             (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) j) refl≃s ⟩
  < Var j [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
          [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                                (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                     (tree-size S₂)
                                ∘ suspSub (exterior-sub S₁ P T))
                                (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                      (tree-size S₂)) ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) (Var j) ⟩
  < Var j [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                                (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                     (tree-size S₂)
                                ∘ suspSub (exterior-sub S₁ P T))
                                (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                      (tree-size S₂))
            ∘ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
    >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-from-connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                     (tree-size S₂)
                                ∘ suspSub (exterior-sub S₁ P T)) (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                      (tree-size S₂)) lem) ⟩
  < Var j [ connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm
    >tm ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid

    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
             ∘ suspSub (exterior-sub S₁ P T ⦃ p = cong pred p′ ⦄) ]tm
            ≃tm
            Var (fromℕ _) [
             connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm
    lem = let
      instance .x : _
               x = cong pred p′
      in begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
             ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
        ≈⟨ assoc-tm _ _ (pd-focus-tm (susp-pd (tree-to-pd S₁))) ⟩
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ suspSub (exterior-sub S₁ P T) ]tm
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm (suspSub-preserve-focus-tm (tree-to-pd S₁) (tree-to-pd (insertion-tree S₁ P T)) (exterior-sub S₁ P T)) refl≃s ⟩
      < pd-focus-tm (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ⟩
      < Var (fromℕ _) [
             connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm ∎

... | inj₁ j | p with susp-var-split (insertion-var-split S₁ P T) j | susp-var-split-compat (insertion-var-split-compat S₁ P T ⦃ p = cong pred p′ ⦄) j
... | inj₁ k | q = let
  instance _ = connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂)
  instance .x : _
           x = cong pred p′
  in begin
  < Var (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) k)
    [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
                          ∘ suspSub (exterior-sub S₁ P T))
                          (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ]tm >tm
      ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) k) refl≃s ⟩
  < Var k
      [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                 (tree-size S₂)
                            ∘ suspSub (exterior-sub S₁ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                  (tree-size S₂)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                                (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                     (tree-size S₂)
                                ∘ suspSub (exterior-sub S₁ P T))
                                (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                      (tree-size S₂))
            ∘ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k}) (sub-from-connect-pd-inc-left
                       (susp-pd (tree-to-pd S₁))
                       (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                            (tree-size S₂)
                       ∘ suspSub (exterior-sub S₁ P T))
                       (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                             (tree-size S₂))) ⟩
  < Var k [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
          ∘ suspSub (exterior-sub S₁ P T) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ suspSub (exterior-sub S₁ P T) ]tm
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ k | q = let
  instance _ = connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂)
  instance .x : _
           x = cong pred p′
  in begin
  < Var k [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
          ∘ suspSub (interior-sub S₁ P T) ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ suspSub (interior-sub S₁ P T) ]tm
          [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid

insertion-var-split-compat (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T i with connect-pd-var-split-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) i | connect-pd-var-split-right-compat (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) i
... | inj₁ j | p = let
  instance _ = connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂)
  instance .x : _
           x = proj₁ bp
  in begin
  < Var (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) j)
    [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                          (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                               (insertion-tree-size S₂ P T))
                          (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                (insertion-tree-size S₂ P T)
                          ∘ exterior-sub S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) j) refl≃s ⟩
  < Var j
      [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var j) ⟩
  < Var j
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T)
      ∘ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j})
         (sub-from-connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                       (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                            (insertion-tree-size S₂ P T))
                                       (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                             (insertion-tree-size S₂ P T)
                                       ∘ exterior-sub S₂ P T)) ⟩
  < Var j [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
... | inj₂ j | p with insertion-var-split S₂ P ⦃ proj₁ bp ⦄ T j | insertion-var-split-compat S₂ P ⦃ proj₁ bp ⦄ T j
... | inj₁ k | q = let
  instance _ = connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂)
  instance .x : _
           x = proj₁ bp
  in begin
  < Var (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) k)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) k) refl≃s ⟩
  < Var k [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
          [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                                (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                     (insertion-tree-size S₂ P T))
                                (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                      (insertion-tree-size S₂ P T)
                                ∘ exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                                (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                     (insertion-tree-size S₂ P T))
                                (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                      (insertion-tree-size S₂ P T)
                                ∘ exterior-sub S₂ P T)
          ∘ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k})
         (sub-from-connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                        (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                             (insertion-tree-size S₂ P T))
                                        (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                      (insertion-tree-size S₂ P T)
                                        ∘ exterior-sub S₂ P T)
                                        lem) ⟩
  < Var k [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T)
          ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ exterior-sub S₂ P T ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
    lem : pd-focus-tm (susp-pd (tree-to-pd S₁))
            [ connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                  (insertion-tree-size S₂ P T) ]tm
            ≃tm
          Var (fromℕ _)
            [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                   (insertion-tree-size S₂ P T)
             ∘ exterior-sub S₂ P ⦃ proj₁ bp ⦄ T ]tm
    lem = let
      instance .x : _
               x = proj₁ bp
      instance .y : _
               y = proj₂ bp
      in begin
      < pd-focus-tm (susp-pd (tree-to-pd S₁))
          [ connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ connect-pd-inc-fst-var (susp-pd (tree-to-pd S₁))
                                  (insertion-tree-size S₂ P T) ⟩
      < Var (fromℕ (insertion-tree-size S₂ P T))
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
        ≈⟨ sub-action-≃-tm (exterior-sub-fst-var S₂ P T) refl≃s ⟩
      < Var (fromℕ _)
          [ exterior-sub S₂ P T ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
        ≈˘⟨ assoc-tm _ (exterior-sub S₂ P T) (Var (fromℕ _)) ⟩
      < Var (fromℕ _)
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T)
          ∘ exterior-sub S₂ P T ]tm >tm ∎

... | inj₂ k | q = begin
  < Var k
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                             (insertion-tree-size S₂ P T)
      ∘ interior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (Var k) ⟩
  < Var k [ interior-sub S₂ P T ]tm
          [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm q refl≃s ⟩
  < Var j [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                 (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ p ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
-}


insertion-var-split-fst : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (fromℕ _) ≡ inj₂ (fromℕ _)
insertion-var-split-fst S P T with susp-var-split (insertion-var-split S P T) (fromℕ _) | susp-var-split-fst (insertion-var-split S P T)
... | inj₂ y | p = p

insertion-var-split-snd : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (inject₁ (fromℕ _)) ≡ inj₂ (inject₁ (fromℕ _))
insertion-var-split-snd S P T with susp-var-split (insertion-var-split S P T) (inject₁ (fromℕ _)) | susp-var-split-snd (insertion-var-split S P T)
... | inj₂ y | p = p

insertion-var-split-inject : (S : Tree n)
                           → (P : Path S)
                           → .⦃ bp : is-branching-path P ⦄
                           → (T : Tree m)
                           → .⦃ lh : has-linear-height (path-length P) T ⦄
                           → (k : Fin (suc (insertion-tree-size S P T)))
                           → insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (inject₁ (inject₁ k)) ≡ Data.Sum.map (λ - → inject₁ (inject₁ -)) (λ - → inject₁ (inject₁ -)) (insertion-var-split S P T k)
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
                        → sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion S P T σ τ)
sub-from-insertion-susp S P T σ τ
  = sub-≃-term-wise (sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ))
                    (suspSub (sub-from-insertion S P T σ τ)) lem
  where
    open Reasoning tm-setoid
    l2 : sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (fromℕ _)
           ≃tm
         getFst
    l2 with insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (fromℕ _) | insertion-var-split-fst S P T
    ... | inj₂ .(suc (suc (fromℕ _))) | refl = sym≃tm (susp-sub-preserve-getFst τ)

    l3 : sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (inject₁ (fromℕ _))
           ≃tm
         getSnd
    l3 with insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (inject₁ (fromℕ _)) | insertion-var-split-snd S P T
    ... | inj₂ .(suc (inject₁ (fromℕ _))) | refl = sym≃tm (susp-sub-preserve-getSnd τ)

    l4 : (k : Fin (suc (insertion-tree-size S P T)))
       →  sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (inject₁ (inject₁ k))
            ≃tm
          suspTm (sub-from-insertion-func S P T σ τ k)
    l4 k with insertion-var-split (susp-tree S) (PExt P) (susp-tree T) (inject₁ (inject₁ k)) | insertion-var-split S P T k | insertion-var-split-inject S P T k
    ... | inj₁ .(inject₁ (inject₁ y)) | inj₁ y | refl = inject-susp-sub σ y
    ... | inj₂ .(inject₁ (inject₁ y)) | inj₂ y | refl = inject-susp-sub τ y

    lem : (i : Fin (suc (insertion-tree-size (susp-tree S) (PExt P) (susp-tree T))))
        → Var i [ sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) ]tm
            ≃tm
          Var i [ suspSub (sub-from-insertion S P T σ τ) ]tm
    lem i with suspension-vars i
    ... | inj₁ (inj₁ refl) = begin
      < getFst [ sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ)) (fromℕ _) ⟩
      < sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (fromℕ _) >tm ≈⟨ l2 ⟩
      < getFst >tm ≈⟨ susp-sub-preserve-getFst (sub-from-insertion S P T σ τ) ⟩
      < getFst [ suspSub (sub-from-insertion S P T σ τ) ]tm >tm ∎
    ... | inj₁ (inj₂ refl) = begin
      < getSnd [ sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ)) (inject₁ (fromℕ _)) ⟩
      < sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (inject₁ (fromℕ _)) >tm ≈⟨ l3 ⟩
      < getSnd >tm ≈⟨ susp-sub-preserve-getSnd (sub-from-insertion S P T σ τ) ⟩
      < getSnd [ suspSub (sub-from-insertion S P T σ τ) ]tm >tm ∎
    ... | inj₂ (k ,, refl) = begin
      < Var (inject₁ (inject₁ k)) [ sub-from-insertion (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) ]tm >tm
        ≈⟨ sub-from-function-prop (sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ)) (inject₁ (inject₁ k)) ⟩
      < sub-from-insertion-func (susp-tree S) (PExt P) (susp-tree T) (suspSub σ) (suspSub τ) (inject₁ (inject₁ k)) >tm
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
