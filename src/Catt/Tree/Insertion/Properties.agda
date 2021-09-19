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
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; fromℕ; inject₁)
open import Relation.Nullary
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Data.Product renaming (_,_ to _,,_)

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



insertion-eq : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
             → branching-path-to-var S P [ exterior-sub S P T ]tm ≃tm Coh T (unbiased-type (tree-dim T) T) (interior-sub S P T)
insertion-eq (Join S₁ S₂) PHere T = begin
  < 0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
       [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) 0V ⟩
  < 0V [ exterior-sub (Join S₁ S₂) PHere T
       ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (∘-assoc _ _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂))) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (sub-between-connects (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
                               ∘ idSub≃ (linear-tree-compat (suspTree S₁)))
                           getSnd
                           (idSub _)
                           (tree-last-var T)
         ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (sub-action-≃-sub (sub-between-connects-inc-left (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
                               ∘ idSub≃ (linear-tree-compat (suspTree S₁))) getSnd (idSub _) (tree-last-var T)) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))})) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (connect-inc-left (tree-last-var T) _
       ∘ (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
       ∘ idSub≃ (linear-tree-compat (suspTree S₁)))) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _
       ∘ (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
       ∘ idSub≃ (linear-tree-compat (suspTree S₁))))) ⟩
  < 0V [ connect-inc-left (tree-last-var T) _
       ∘ (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _)))
       ∘ idSub≃ (linear-tree-compat (suspTree S₁))) ]tm >tm
    ≈⟨ sub-action-≃-tm {s = 0V} {t = 0V} (Var≃ (≃c-preserve-length (linear-tree-compat (suspTree S₁))) refl) (sub-action-≃-sub (idSub≃-right-unit (linear-tree-compat (suspTree S₁)) (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub (suc _))))) (refl≃s)) ⟩
  < 0V [ connect-inc-left (tree-last-var T) _
       ∘ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub _)) ]tm >tm
    ≈⟨ assoc-tm (connect-inc-left (tree-last-var T) _) (sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (tree-dim S₁)) T) (idSub _))) 0V ⟩
  < Coh T (unbiased-type (suc (tree-dim S₁)) T) (connect-inc-left (tree-last-var T) _ ∘ idSub _) >tm
    ≈⟨ Coh≃ refl≃ (unbiased-type-≃ (recompute ((suc (tree-dim S₁)) ≟ (tree-dim T)) it) refl≃) lem ⟩
  < Coh T (unbiased-type (tree-dim T) T)
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       connect-inc-left (tree-last-var T) _) >tm
    ≡⟨⟩
  < Coh T (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) PHere T) >tm ∎
  where
    lem : connect-inc-left (tree-last-var T) _ ∘ idSub _
          ≃s idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
    lem = begin
      < connect-inc-left (tree-last-var T) _ ∘ idSub _ >s
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
    [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ sub-between-connect-susps (exterior-sub S₁ P T) (idSub _)
    ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P)}) (sub-between-connect-susps-inc-left (exterior-sub S₁ P T) (idSub _)) ⟩
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
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (insertion-eq S₁ P T)) refl≃s ⟩
  < suspTm (Coh T (unbiased-type (tree-dim T) T) (interior-sub S₁ P T))
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ Coh≃ refl≃ (unbiased-type-susp-lem (tree-dim T) T) refl≃s ⟩
  < Coh (Join T Sing) (unbiased-type (tree-dim (Join T Sing)) (Join T Sing)) (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) >tm ∎
  where
    open Reasoning tm-setoid

insertion-eq (Join S₁ S₂) (PShift P) T = begin
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (idSub _) (exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
    [ sub-between-connect-susps (idSub (suc _)) (exterior-sub S₂ P T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P}) (sub-between-connect-susps-inc-right (idSub _) (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
    ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P [ exterior-sub S₂ P T ]tm
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (insertion-eq S₂ P T) refl≃s ⟩
  < Coh T (unbiased-type (tree-dim T) T) (interior-sub S₂ P T)
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≡⟨⟩
  < Coh T (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) (PShift P) T) >tm ∎
  where
    open Reasoning tm-setoid

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
             → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
             → exterior-sub (suspTree S) (PExt P) (suspTree T) ⦃ p = cong suc p ⦄ ≃s suspSub (exterior-sub S P T)
exterior-sub-susp S P T = begin
  < exterior-sub (suspTree S) (PExt P) (suspTree T) ⦃ p = cong suc it ⦄ >s ≡⟨⟩
  < idSub (2 + suc (insertion-tree-size S P T))
       ∘ suspSub (exterior-sub S P T ⦃ p = it ⦄) >s
    ≈⟨ id-left-unit (suspSub (exterior-sub S P T)) ⟩
  < suspSub (exterior-sub S P T) >s ∎
    where
      open Reasoning sub-setoid

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
