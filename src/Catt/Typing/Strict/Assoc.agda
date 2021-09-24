{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

module Catt.Typing.Strict.Assoc where

open import Catt.Typing.Base
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
-- open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc)
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤;tt)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Tree.Insertion
open import Catt.Tree
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Insertion.Properties

record InsertionData : Set where
  field
    id-l : ℕ
    id-Γ : Ctx id-l
    id-n : ℕ
    id-S : Tree id-n
    id-A : Ty (suc id-n)
    id-σ : Sub (suc id-n) id-l ⋆
    id-P : Path id-S
    .⦃ id-bp ⦄ : is-branching-path id-P
    id-m : ℕ
    id-T : Tree id-m
    id-τ : Sub (suc id-m) id-l ⋆
    .⦃ id-lh ⦄ : has-linear-height (path-length id-P) id-T
    -- .⦃ id-p ⦄ : height-of-branching id-P ≡ tree-dim id-T
    id-eq : branching-path-to-var id-S id-P [ id-σ ]tm ≃tm unbiased-comp (tree-dim id-T) id-T id-τ

module _ where
  open InsertionData
  insertionRule : Rule
  insertionRule .Args = InsertionData
  -- insertionRule .tctCount = 2
  -- insertionRule .eqtCount = 1
  -- insertionRule .tgtHeight zero a = a .id-d′
  -- insertionRule .tgtHeight (suc i) a = a .id-d″
  -- insertionRule .tctLen zero a = a .id-l
  -- insertionRule .tctLen (suc i) a = a .id-l
  -- insertionRule .tct zero a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-σ)
  -- insertionRule .tct (suc i) a = Coh (tree-to-ctx (a .id-T)) (a .id-B) (a .id-τ)
  -- insertionRule .tctTy zero a = a .id-C
  -- insertionRule .tctTy (suc i) a = a .id-D
  -- insertionRule .tctCtx zero a = a .id-Γ
  -- insertionRule .tctCtx (suc i) a = a .id-Γ
  -- insertionRule .eqtLen zero a = a .id-l
  -- insertionRule .eqtCtx zero a = a .id-Γ
  -- insertionRule .eqtlhs zero a = branching-path-to-var (a .id-S) (a .id-P) [ a .id-σ ]tm
  -- insertionRule .eqtrhs zero a = Coh (tree-to-ctx (a .id-T)) (unbiased-type (tree-to-pd (a .id-T))) (a .id-τ)
  insertionRule .len a = a .id-l
  insertionRule .tgtCtx a = a .id-Γ
  insertionRule .lhs a = Coh (a .id-S) (a .id-A) (a .id-σ)
  insertionRule .rhs a = Coh (insertion-tree (a .id-S) (a .id-P) (a .id-T))
                             (a .id-A [ exterior-sub (a .id-S) (a .id-P) (a .id-T) ]ty)
                             (sub-from-insertion (a .id-S) (a .id-P) (a .id-T) (a .id-σ) (a .id-τ))

  insertionBuilder : (Γ : Ctx l)
                   → (S : Tree n)
                   → (A : Ty (suc n))
                   → (σ : Sub (suc n) l ⋆)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → (τ : Sub (suc m) l ⋆)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T τ
                   → InsertionData
  insertionBuilder Γ S A σ P T τ eq .id-l = _
  insertionBuilder Γ S A σ P T τ eq .id-Γ = Γ
  insertionBuilder Γ S A σ P T τ eq .id-n = _
  insertionBuilder Γ S A σ P T τ eq .id-S = S
  insertionBuilder Γ S A σ P T τ eq .id-A = A
  insertionBuilder Γ S A σ P T τ eq .id-σ = σ
  insertionBuilder Γ S A σ P T τ eq .id-P = P
  insertionBuilder Γ S A σ P T τ eq .id-bp = it
  insertionBuilder Γ S A σ P T τ eq .id-m = _
  insertionBuilder Γ S A σ P T τ eq .id-T = T
  insertionBuilder Γ S A σ P T τ eq .id-τ = τ
  insertionBuilder Γ S A σ P T τ eq .id-lh = it
  insertionBuilder Γ S A σ P T τ eq .id-eq = eq

open import Catt.Typing 1 (λ x → insertionRule)

Ins≈ : (S : Tree n)
     → (ty : Typing-Tm Γ (Coh S A σ) C)
     → (P : Path S)
     → .⦃ bp : is-branching-path P ⦄
     → (T : Tree m)
     → (branching-path-to-var S P [ σ ]tm) ≃tm unbiased-comp (tree-dim T) T τ
     → .⦃ lh : has-linear-height (path-length P) T ⦄
     → Coh S A σ ≈[ Γ ]tm
       Coh (insertion-tree S P T)
           (A [ exterior-sub S P T ]ty)
           (sub-from-insertion S P T σ τ)
Ins≈ {Γ = Γ} {A = A} {σ = σ} {τ = τ} S ty P T p
  = Rule≈ zero (insertionBuilder Γ S A σ P T τ p) ty

open import Catt.Typing.Properties.Base 1 (λ x → insertionRule)

props : (i : Fin 1) → Props i
props i .lift-rule a tc = begin
  liftTerm (insertionRule .lhs a) ≡⟨⟩
  Coh id-S id-A (liftSub id-σ)
    ≈⟨ Ins≈ id-S tc id-P id-T lem ⟩
  Coh (insertion-tree id-S id-P id-T)
      (id-A [ exterior-sub id-S id-P id-T ]ty)
      (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ))
    ≈⟨ reflexive≈tm (Coh≃ refl≃ refl≃ty (sym≃s (lift-sub-from-insertion id-S id-P id-T id-σ id-τ))) ⟩
  liftTerm (insertionRule .rhs a) ∎

  where
    open InsertionData a
    lem : branching-path-to-var id-S id-P
            [ liftSub id-σ ]tm
          ≃tm
          unbiased-comp (tree-dim id-T) id-T (liftSub id-τ)
    lem = begin
      < branching-path-to-var id-S id-P [ liftSub id-σ ]tm >tm
        ≈⟨ apply-lifted-sub-tm-≃ (branching-path-to-var id-S id-P) id-σ ⟩
      < liftTerm (branching-path-to-var id-S id-P [ id-σ ]tm) >tm
        ≈⟨ lift-tm-≃ id-eq ⟩
      < liftTerm (unbiased-comp (tree-dim id-T) id-T id-τ) >tm
        ≡⟨⟩
      < unbiased-comp (tree-dim id-T) id-T (liftSub id-τ) >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning (tm-setoid-≈ (id-Γ , _))

props i .susp-rule a tc = begin
  Coh (suspTree id-S) (suspTy id-A) (suspSub id-σ)
    ≈⟨ Ins≈ (suspTree id-S) tc (PExt id-P) (suspTree id-T) lem ⟩
  Coh (insertion-tree (suspTree id-S) (PExt id-P) (suspTree id-T))
      (suspTy id-A [ exterior-sub (suspTree id-S) (PExt id-P) (suspTree id-T) ]ty)
      (sub-from-insertion (suspTree id-S) (PExt id-P) (suspTree id-T) (suspSub id-σ) (suspSub id-τ))
    ≈⟨ reflexive≈tm (Coh≃ refl≃ lem-ty (sub-from-insertion-susp id-S id-P id-T id-σ id-τ)) ⟩
  Coh (suspTree (insertion-tree id-S id-P id-T))
        (suspTy (id-A [ exterior-sub id-S id-P id-T ]ty))
        (suspSub (sub-from-insertion id-S id-P id-T id-σ id-τ)) ∎
  where
    open InsertionData a

    lem-ty : suspTy id-A [ exterior-sub (suspTree id-S) (PExt id-P) (suspTree id-T) ]ty
               ≃ty
             suspTy (id-A [ exterior-sub id-S id-P id-T ]ty)
    lem-ty = begin
      < suspTy id-A [ exterior-sub (suspTree id-S) (PExt id-P) (suspTree id-T) ]ty >ty
        ≈⟨ sub-action-≃-ty refl≃ty (exterior-sub-susp id-S id-P id-T) ⟩
      < suspTy id-A [ suspSub (exterior-sub id-S id-P id-T) ]ty >ty
        ≈˘⟨ susp-functorial-ty (exterior-sub id-S id-P id-T) id-A ⟩
      < suspTy (id-A [ exterior-sub id-S id-P id-T ]ty) >ty ∎
      where
        open Reasoning ty-setoid

    lem : (branching-path-to-var (suspTree id-S) (PExt id-P)
             [ suspSub id-σ ]tm)
          ≃tm
          unbiased-comp (tree-dim (suspTree id-T)) (suspTree id-T) (unrestrict (suspSubRes id-τ))
    lem = begin
      < branching-path-to-var (suspTree id-S) (PExt id-P) [ suspSub id-σ ]tm >tm ≡⟨⟩
      < suspTm (branching-path-to-var id-S id-P)
          [ idSub _ ]tm
          [ suspSub id-σ ]tm >tm
        ≈⟨ sub-action-≃-tm (id-on-tm (suspTm (branching-path-to-var id-S id-P))) refl≃s ⟩
      < suspTm (branching-path-to-var id-S id-P)
          [ suspSub id-σ ]tm >tm
        ≈˘⟨ susp-functorial-tm id-σ (branching-path-to-var id-S id-P) ⟩
      < suspTm (branching-path-to-var id-S id-P [ id-σ ]tm) >tm
        ≈⟨ susp-tm-≃ id-eq ⟩
      < suspTm (unbiased-comp (tree-dim id-T) id-T id-τ) >tm ≡⟨⟩
      < Coh (suspTree id-T) (suspTy (unbiased-type (tree-dim id-T) id-T)) (suspSub id-τ) >tm
        ≈⟨ Coh≃ refl≃ (unbiased-type-susp-lem (tree-dim id-T) id-T) refl≃s ⟩
      < Coh (suspTree id-T) (unbiased-type (tree-dim (suspTree id-T)) (suspTree id-T)) (suspSub id-τ) >tm ≡⟨⟩
      < unbiased-comp (tree-dim (suspTree id-T)) (suspTree id-T) (suspSub id-τ) >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning (tm-setoid-≈ (suspCtx id-Γ))

props i .sub-rule a {σ = σ} {Δ = Δ} σty tc = begin
  insertionRule .lhs a [ σ ]tm ≡⟨⟩
  Coh (tree-to-ctx id-S) id-A (σ ∘ id-σ)
    ≈⟨ Ins≈ {τ = σ ∘ id-τ} id-S tc id-P id-T lem ⟩
  Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
      (id-A [ exterior-sub id-S id-P id-T ]ty)
      (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ)) ≈⟨ Coh≈ refl≈ty (reflexive≈s (sub-from-insertion-sub id-S id-P id-T id-σ id-τ σ)) ⟩
  Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
      (id-A [ exterior-sub id-S id-P id-T ]ty)
      (σ ∘ sub-from-insertion id-S id-P id-T id-σ id-τ) ≡⟨⟩
  insertionRule .rhs a [ σ ]tm ∎
  where
    open InsertionData a
    open Reasoning (tm-setoid-≈ Δ)

    -- lem : (branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm)
    --         ≈[ Δ ]tm
    --       Coh (tree-to-ctx id-T) (unbiased-type (tree-to-pd id-T)) (σ ∘ id-τ)
    -- lem = begin
    --   branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm ≈⟨ reflexive≈tm (assoc-tm σ id-σ (branching-path-to-var id-S id-P)) ⟩
    --   branching-path-to-var id-S id-P [ id-σ ]tm [ σ ]tm ≈⟨ eqt zero σty ⟩
    --   Coh (tree-to-ctx id-T) (unbiased-type (tree-to-pd id-T)) (σ ∘ id-τ) ∎
