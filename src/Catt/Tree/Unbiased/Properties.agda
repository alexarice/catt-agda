{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Nat
open import Data.Bool using (Bool; true; false)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Catt.Discs
open import Catt.Discs.Properties
open import Data.Nat.Properties


unbiased-type-inc-lem : (d : ℕ) → (T : Tree n) → unbiased-type d (tree-bd d T) [ tree-inc d T true ]ty ≃ty unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty
unbiased-type-inc-lem zero T = refl≃ty
unbiased-type-inc-lem (suc d) T = Arr≃ (l1 (unbiased-term d (tree-bd d (tree-bd (suc d) T))) false) (l2 (unbiased-type d (tree-bd d (tree-bd (suc d) T)))) (l1 (unbiased-term d (tree-bd d (tree-bd (suc d) T))) true)
  where
    l1 : (t : Tm (suc (tree-bd-len d (tree-bd (suc d) T)))) → (b : Bool) →
         t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm
           ≃tm
         t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm
    l1 t b = begin
      < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm >tm
        ≈˘⟨ assoc-tm (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) b) t ⟩
      < t [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = t}) (tree-inc-glob-step d T true b) ⟩
      < t [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
        ≈⟨ assoc-tm (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) b) t ⟩
      < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : (A : Ty (suc (tree-bd-len d (tree-bd (suc d) T))) d)
       → A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty
       ≃ty A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty
    l2 A = begin
      < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty >ty
        ≈˘⟨ assoc-ty (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) false) A ⟩
      < A [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
        ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (tree-inc-glob-step d T true false) ⟩
      < A [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
        ≈⟨ assoc-ty (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) false) A ⟩
      < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty >ty ∎
      where
        open Reasoning ty-setoid

unbiased-term-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-term d T) ≃tm unbiased-term (suc d) (suspTree T)
unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → suspTy (unbiased-type d T) ≃ty unbiased-type (suc d) (suspTree T)

unbiased-term-susp-lem d T with is-linear-dec T
... | yes p = refl≃tm
... | no p = Coh≃ refl≃ (unbiased-type-susp-lem d T) (susp-functorial-id (suc _))

unbiased-type-susp-lem zero T = refl≃ty
unbiased-type-susp-lem (suc d) T = Arr≃ (l1 false) l2 (l1 true)
  where
    l1 : (b : Bool)
       → suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≃tm
         unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
           [ tree-inc (suc d) (suspTree T) b ]tm
    l1 b = begin
      < suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) >tm
        ≈⟨ susp-functorial-tm (tree-inc d T b) (unbiased-term d (tree-bd d T)) ⟩
      < suspTm (unbiased-term d (tree-bd d T))
          [ suspSub (tree-inc d T b) ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T b) ⟩
      < unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
          [ tree-inc (suc d) (suspTree T) b ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : suspTy
           (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
           ≃ty
           (unbiased-type (suc d) (tree-bd (suc d) (suspTree T)) [
            tree-inc (suc d) (suspTree T) false ]ty)
    l2 = begin
      < suspTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty) >ty
        ≈⟨ susp-functorial-ty (tree-inc d T false) (unbiased-type d (tree-bd d T)) ⟩
      < suspTy (unbiased-type d (tree-bd d T))
          [ suspSub (tree-inc d T false) ]ty >ty
        ≈⟨ sub-action-≃-ty (unbiased-type-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T false) ⟩
      < unbiased-type (suc d) (tree-bd (suc d) (suspTree T))
          [ tree-inc (suc d) (suspTree T) false ]ty >ty ∎
      where
        open Reasoning ty-setoid

linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type d T
linear-tree-unbiased-lem zero Sing p = refl≃ty
linear-tree-unbiased-lem zero (Join S T) p with .(join-tree-has-non-zero-dim S T (sym p))
... | ()
linear-tree-unbiased-lem (suc d) (Join S Sing) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero >ty
    ≈⟨ susp-‼ (tree-to-ctx S) zero ⟩
  < suspTy (tree-to-ctx S ‼ zero) >ty
    ≈⟨ susp-ty-≃ (linear-tree-unbiased-lem d S (cong pred p)) ⟩
  < suspTy (unbiased-type d S) >ty
    ≈⟨ unbiased-type-susp-lem d S ⟩
  < unbiased-type (suc d) (Join S Sing) >ty ∎
  where
    open Reasoning ty-setoid

unbiased-type-sphere-lem : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
                         → Var (fromℕ _)
                           [ sub-from-sphere (unbiased-type (suc d) T) ]tm
                           ≃tm Var (fromℕ (tree-size T))
unbiased-type-sphere-lem zero T p = refl≃tm
unbiased-type-sphere-lem (suc d) T p = begin
  < Var (fromℕ (suc (sphere-size (suc d))))
      [ sub-from-sphere (unbiased-type (suc (suc d)) T) ]tm >tm ≡⟨⟩
  < Var (fromℕ (suc (sphere-size d)))
      [ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ _)}) (sphere-to-subbed-ty (unbiased-type (suc d) (tree-bd (suc d) T)) (tree-inc (suc d) T false)) ⟩
  < Var (fromℕ (suc (sphere-size d)))
    [ tree-inc (suc d) T false ∘ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T)) ]tm >tm
    ≈⟨ assoc-tm (tree-inc (suc d) T false) (sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T))) (Var (fromℕ (suc (sphere-size d)))) ⟩
  < Var (fromℕ (suc (sphere-size d)))
    [ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T)) ]tm
    [ tree-inc (suc d) T false ]tm >tm
    ≈⟨ sub-action-≃-tm (unbiased-type-sphere-lem d (tree-bd (suc d) T) (tree-dim-bd′ (suc d) T (≤-trans (n≤1+n (suc d)) (≤-reflexive (sym p))))) refl≃s ⟩
  < Var (fromℕ (tree-size (tree-bd (suc d) T)))
    [ tree-inc (suc d) T false ]tm >tm
    ≈⟨ tree-inc-preserve-fst-var d T false ⟩
  < Var (fromℕ (tree-size T)) >tm ∎
  where
    open Reasoning tm-setoid

unbiased-type-disc-lem : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d)
                       → .⦃ NonZero′ d ⦄
                       → Var (fromℕ _)
                         [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type d T) (idSub _)) ]tm
                         ≃tm Var (fromℕ (tree-size T))
unbiased-type-disc-lem (suc zero) T p = id-on-tm (Var (fromℕ (tree-size T)))
unbiased-type-disc-lem (suc (suc d)) T p = begin
  < Var (fromℕ (suc (suc (sphere-size (suc d)))))
    [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc (suc d)) T) (idSub (suc _))) ]tm >tm
    ≡⟨⟩
  < Var (fromℕ (suc (sphere-size (suc d))))
     [ sub-from-sphere (unbiased-type (suc (suc d)) T [ idSub _ ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ (suc (sphere-size (suc d))))}) (sub-from-sphere-ty-≃ (id-on-ty (unbiased-type (suc (suc d)) T))) ⟩
  < Var (fromℕ (suc (sphere-size (suc d))))
      [ sub-from-sphere (unbiased-type (suc (suc d)) T) ]tm >tm
    ≈⟨ unbiased-type-sphere-lem (suc d) T p ⟩
  < Var (fromℕ (tree-size T)) >tm ∎
  where
    open Reasoning tm-setoid

unbiased-type-sphere-lem-2 : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
                           → getSnd
                             [ sub-from-sphere (unbiased-type (suc d) T) ]tm
                             ≃tm tree-last-var T
unbiased-type-sphere-lem-2 zero T p = refl≃tm
unbiased-type-sphere-lem-2 (suc d) T p = begin
  < getSnd [ sub-from-sphere (unbiased-type (suc (suc d)) T) ]tm >tm
    ≡⟨⟩
  < getSnd [ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = getSnd}) (sphere-to-subbed-ty (unbiased-type (suc d) (tree-bd (suc d) T)) (tree-inc (suc d) T false)) ⟩
  < getSnd [ tree-inc (suc d) T false ∘ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T)) ]tm >tm
    ≈⟨ assoc-tm (tree-inc (suc d) T false) (sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T))) getSnd ⟩
  < getSnd [ sub-from-sphere (unbiased-type (suc d) (tree-bd (suc d) T)) ]tm
           [ tree-inc (suc d) T false ]tm >tm
    ≈⟨ sub-action-≃-tm (unbiased-type-sphere-lem-2 d (tree-bd (suc d) T) (tree-dim-bd′ (suc d) T (≤-trans (n≤1+n (suc d)) (≤-reflexive (sym p))))) refl≃s ⟩
  < tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T false ]tm >tm
    ≈⟨ tree-inc-preserve-last-var d T false ⟩
  < tree-last-var T >tm ∎
  where
    open Reasoning tm-setoid

unbiased-type-disc-lem-2 : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
                         → getSnd
                           [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc d) T) (idSub _)) ]tm
                           ≃tm tree-last-var T
unbiased-type-disc-lem-2 d T p = begin
  < getSnd
    [ sub-from-disc (tree-to-ctx T) (Coh T (unbiased-type (suc d) T) (idSub _)) ]tm >tm
    ≡⟨⟩
  < getSnd
     [ sub-from-sphere (unbiased-type (suc d) T [ idSub _ ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = getSnd}) (sub-from-sphere-ty-≃ (id-on-ty (unbiased-type (suc d) T))) ⟩
  < getSnd
      [ sub-from-sphere (unbiased-type (suc d) T) ]tm >tm
    ≈⟨ unbiased-type-sphere-lem-2 d T p ⟩
  < tree-last-var T >tm ∎
  where
    open Reasoning tm-setoid
