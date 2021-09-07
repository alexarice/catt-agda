{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Insertion
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Unsuspension
open import Catt.Discs
open import Data.Fin using (Fin; zero; suc; fromℕ)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Data.Sum

exterior-sub-fst-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → .⦃ is-non-empty-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → (A : Ty (suc m) (height-of-branching P))
                     → .⦃ tlh : type-has-linear-height (path-length P) T A ⦄
                     → Var {suc (insertion-tree-size S P T)} (fromℕ _) ≃tm Var (fromℕ _) [ exterior-sub S P T A ]tm
exterior-sub-fst-var (Join S₁ S₂) (PExt P) (Join T Sing) A ⦃ tlh ⦄ = let
  instance .p₁ : is-unsuspendable-ty A
           p₁ = proj₁ tlh
  instance .p₂ : type-has-linear-height (path-length P) T
                   (unsuspend-ty A)
           p₂ = proj₂ tlh
  in begin
  < Var (fromℕ _) >tm
    ≈˘⟨ connect-pd-inc-left-fst-var (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ⟩
  < Var (fromℕ _)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-fst-var (exterior-sub S₁ P T (unsuspend-ty A))) refl≃s ⟩
  < Var (fromℕ _)
      [ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈˘⟨ assoc-tm (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) (suspSub (exterior-sub S₁ P T (unsuspend-ty A))) (Var (fromℕ _)) ⟩
  < Var (fromℕ _)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm >tm
    ≈˘⟨ sub-from-connect-pd-fst-var
         (susp-pd (tree-to-pd S₁))
         (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
           ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)))
         (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ⟩
  < Var (fromℕ _)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
                              ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)))
                            (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) A ]tm >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-fst-var (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T A ⦃ tlh ⦄ = let
  instance .b : is-branching-path P
           b = proj₁ bp
  in begin
  < Var (fromℕ _) >tm
    ≈˘⟨ connect-pd-inc-left-fst-var (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ⟩
  < Var (fromℕ _) [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm >tm
    ≈˘⟨ sub-from-connect-pd-fst-var (susp-pd (tree-to-pd S₁)) (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)) (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ∘ exterior-sub S₂ P T A) ⟩
  < Var (fromℕ _)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                   (insertion-tree-size S₂ P T)
                              ∘ exterior-sub S₂ P T A) ]tm >tm
       ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) (PShift P) T A ]tm >tm ∎
  where
    open Reasoning tm-setoid

insertion-eq : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → (A : Ty (suc m) (height-of-branching P))
             → .⦃ _ : type-has-linear-height (path-length P) T A ⦄
             → branching-path-to-var S P [ exterior-sub S P T A ]tm ≃tm Coh (tree-to-ctx T) A (interior-sub S P T)
insertion-eq S (PHere .S) T A = begin
  < 0V [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _)))
       ∘ idSub≃ (linear-tree-compat S) ]tm >tm
    ≈⟨ assoc-tm (sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _)))) (idSub≃ (linear-tree-compat S)) (Var zero) ⟩
  < 0V [ idSub≃ (linear-tree-compat S) ]tm
       [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _))) ]tm >tm
    ≈⟨ sub-action-≃-tm (trans≃tm (idSub≃-on-tm (linear-tree-compat S) 0V) (Var≃ (≃c-preserve-length (linear-tree-compat S)) refl)) refl≃s ⟩
  < 0V [ sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _))) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx T) A (idSub (suc _)) >tm ≡⟨⟩
  < Coh (tree-to-ctx T) A (interior-sub S (PHere S) T) >tm ∎
  where open Reasoning tm-setoid
insertion-eq (Join S₁ S₂) (PExt P) (Join T Sing) A ⦃ tlh ⦄ = let
  instance .tlh₁ : is-unsuspendable-ty A
           tlh₁ = proj₁ tlh
  instance .tlh₂ : type-has-linear-height (path-length P) T
                     (unsuspend-ty A)
           tlh₂ = proj₂ tlh
  in begin
  < branching-path-to-var (Join S₁ S₂) (PExt P)
      [ exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) A ]tm >tm ≡⟨⟩
  < suspTm (branching-path-to-var S₁ P)
     [ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
     [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                           (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                (tree-size S₂)
                           ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)))
                           (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                 (tree-size S₂))
       ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                 (tree-size S₂)
                            ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)))
                            (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                  (tree-size S₂))
      ∘ connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P)})
                       (sub-from-connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                     (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                                          (tree-size S₂)
                                                     ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)))
                                                     (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                                                                           (tree-size S₂))) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                            (tree-size S₂)
      ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm >tm
    ≈⟨ assoc-tm _ (suspSub (exterior-sub S₁ P T (unsuspend-ty A))) (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
      [ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm lem refl≃s ⟩
  < Coh (tree-to-ctx (Join T Sing)) A (idSub (suc (0 + (2 + _))))
      [ suspSub (interior-sub S₁ P T) ]tm
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ]tm >tm
    ≈˘⟨ assoc-tm _ (suspSub (interior-sub S₁ P T)) (Coh (tree-to-ctx (Join T Sing)) A (idSub (suc (0 + (2 + _))))) ⟩
  < Coh (tree-to-ctx (Join T Sing)) A (idSub (suc (0 + (2 + _))))
      [ connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (interior-sub S₁ P T) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx (Join T Sing)) A (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂)
      ∘ suspSub (interior-sub S₁ P T)
      ∘ idSub (suc (0 + (2 + _)))) >tm
    ≈⟨ Coh≃ refl≃c refl≃ty (id-right-unit _) ⟩
  < Coh (tree-to-ctx (Join T Sing)) A (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) >tm ∎
  where
    open Reasoning tm-setoid
    lem : suspTm (branching-path-to-var S₁ P)
            [ suspSub (exterior-sub S₁ P T (unsuspend-ty A ⦃ proj₁ tlh ⦄) ⦃ proj₂ tlh ⦄) ]tm
          ≃tm
          Coh (tree-to-ctx (Join T Sing)) A (idSub (suc (0 + (2 + _)))) --(tree-to-ctx (Join T Sing)))
            [ suspSub (interior-sub S₁ P T) ]tm
    lem = let
      instance .tlh₁ : is-unsuspendable-ty A
               tlh₁ = proj₁ tlh
      instance .tlh₂ : type-has-linear-height (path-length P) T
                         (unsuspend-ty A)
               tlh₂ = proj₂ tlh
      in begin
      < suspTm (branching-path-to-var S₁ P)
          [ suspSub (exterior-sub S₁ P T (unsuspend-ty A)) ]tm >tm
        ≈˘⟨ susp-functorial-tm (exterior-sub S₁ P T (unsuspend-ty A)) (branching-path-to-var S₁ P) ⟩
      < suspTm (branching-path-to-var S₁ P
          [ exterior-sub S₁ P T (unsuspend-ty A) ]tm) >tm
        ≈⟨ susp-tm-≃ (insertion-eq S₁ P T (unsuspend-ty A)) ⟩
      < Coh (suspCtx (tree-to-ctx T)) (suspTy (unsuspend-ty A)) (suspSub (interior-sub S₁ P T)) >tm
         ≈˘⟨ Coh≃ refl≃c refl≃ty (susp-sub-≃ (id-right-unit (interior-sub S₁ P T))) ⟩
      < Coh (suspCtx (tree-to-ctx T)) (suspTy (unsuspend-ty A)) (suspSub (interior-sub S₁ P T ∘ idSub (suc _))) >tm ≈⟨ Coh≃ refl≃c
                   (unsuspend-ty-compat A)
                   (trans≃s (susp-functorial (interior-sub S₁ P T) (idSub (suc _)))
                            (sub-action-≃-sub (susp-functorial-id (suc (tree-size T))) refl≃s)) ⟩
      < Coh (tree-to-ctx (Join T Sing)) A (idSub (suc (0 + (2 + _))))
          [ suspSub (interior-sub S₁ P T) ]tm >tm ∎
insertion-eq (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T A = let
  instance .l : is-branching-path P
           l = proj₁ bp
  in begin
  < branching-path-to-var (Join S₁ S₂) (PShift P)
    [ exterior-sub (Join S₁ S₂) (PShift P) T A ]tm >tm
    ≡⟨⟩
  < branching-path-to-var S₂ P
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T A)
       ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
      [ sub-from-connect-pd (susp-pd (tree-to-pd S₁))
                            (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                                 (insertion-tree-size S₂ P T))
                            (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                                  (insertion-tree-size S₂ P T)
                            ∘ exterior-sub S₂ P T A)
      ∘ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P})
                       (sub-from-connect-pd-inc-right
                         (susp-pd (tree-to-pd S₁))
                         (connect-pd-inc-left (susp-pd (tree-to-pd S₁))
                                              (insertion-tree-size S₂ P T))
                         (connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                                               (insertion-tree-size S₂ P T)
                         ∘ exterior-sub S₂ P T A)
                         lem) ⟩
  < branching-path-to-var S₂ P
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁))
                             (insertion-tree-size S₂ P T)
      ∘ exterior-sub S₂ P T A ]tm >tm
    ≈⟨ assoc-tm _ (exterior-sub S₂ P T A) (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
      [ exterior-sub S₂ P T A ]tm
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
    >tm ≈⟨ sub-action-≃-tm (insertion-eq S₂ P T A) refl≃s ⟩
  <
    Coh (tree-to-ctx T) A (interior-sub S₂ P T)
      [ connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ]tm
    >tm ≡⟨⟩
  < Coh (tree-to-ctx T) A
      (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T)
       ∘ interior-sub S₂ P T) >tm ≡⟨⟩
  < Coh (tree-to-ctx T) A (interior-sub (Join S₁ S₂) (PShift P) T) >tm ∎
  where
    open Reasoning tm-setoid
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

type-has-linear-height-≃ : (T : Tree m)
                         → (A : Ty (suc m) d)
                         → {B : Ty (suc m) d′}
                         → A ≃ty B
                         → .⦃ lh : has-linear-height n T ⦄
                         → ⦃ type-has-linear-height n T A ⦄
                         → type-has-linear-height n T B
type-has-linear-height-≃ T A p with ≃ty-preserve-height p
... | refl with ≃ty-to-≡ p
... | refl = it

type-has-linear-height-susp : (n : ℕ)
                            → (T : Tree m)
                            → (A : Ty (suc m) d)
                            → .⦃ lh : has-linear-height n T ⦄
                            → ⦃ type-has-linear-height n T A ⦄
                            → type-has-linear-height (suc n) (susp-tree T) (suspTy A)
type-has-linear-height-susp n T A  = (suspension-is-unsuspendable-ty A) ,, type-has-linear-height-≃ T A (sym≃ty (unsusp-susp-compat-ty A))
