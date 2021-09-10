{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

module Catt.Typing.Strict.Assoc where

open import Catt.Typing.Base
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
-- open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting.Insertion
open import Catt.Pasting.Insertion.Properties
open import Catt.Pasting.Tree
open import Data.Fin using (Fin;zero;suc)
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤;tt)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Unsuspension

record InsertionData : Set where
  field
    id-l : ℕ
    id-Γ : Ctx id-l
    id-n : ℕ
    id-S : Tree id-n
    id-d : ℕ
    id-A : Ty (suc id-n) id-d
    id-σ : Sub (suc id-n) id-l
    id-P : Path id-S
    .⦃ id-bp ⦄ : is-branching-path id-P
    id-m : ℕ
    id-T : Tree id-m
    id-B : Ty (suc id-m) (height-of-branching id-P)
    id-τ : Sub (suc id-m) id-l
    .⦃ id-lh ⦄ : has-linear-height (path-length id-P) id-T
    .⦃ id-tlh ⦄ : type-has-linear-height (path-length id-P) id-T id-B

module _ where
  open InsertionData
  insertionRule : Rule
  insertionRule .Args = InsertionData
  -- insertionRule .tctCount = 2
  insertionRule .eqtCount = 1
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
  insertionRule .eqtLen zero a = a .id-l
  insertionRule .eqtCtx zero a = a .id-Γ
  insertionRule .eqtlhs zero a = branching-path-to-var (a .id-S) (a .id-P) [ a .id-σ ]tm
  insertionRule .eqtrhs zero a = Coh (tree-to-ctx (a .id-T)) (a .id-B) (a .id-τ)
  insertionRule .len a = a .id-l
  insertionRule .tgtCtx a = a .id-Γ
  insertionRule .lhs a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-σ)
  insertionRule .rhs a = Coh (tree-to-ctx (insertion-tree (a .id-S) (a .id-P) (a .id-T)))
                             (a .id-A [ exterior-sub (a .id-S) (a .id-P) (a .id-T) (a .id-B) ]ty)
                             (sub-from-insertion (a .id-S) (a .id-P) (a .id-T) (a .id-σ) (a .id-τ))

  insertionBuilder : (Γ : Ctx l)
                   → (S : Tree n)
                   → (A : Ty (suc n) d)
                   → (σ : Sub (suc n) l)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → (B : Ty (suc m) (height-of-branching P))
                   → (τ : Sub (suc m) l)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → .⦃ tlh : type-has-linear-height (path-length P) T B ⦄
                   → InsertionData
  insertionBuilder Γ S A σ P T B τ .id-l = _
  insertionBuilder Γ S A σ P T B τ .id-Γ = Γ
  insertionBuilder Γ S A σ P T B τ .id-n = _
  insertionBuilder Γ S A σ P T B τ .id-S = S
  insertionBuilder Γ S A σ P T B τ .id-d = _
  insertionBuilder Γ S A σ P T B τ .id-A = A
  insertionBuilder Γ S A σ P T B τ .id-σ = σ
  insertionBuilder Γ S A σ P T B τ .id-P = P
  insertionBuilder Γ S A σ P T B τ .id-bp = it
  insertionBuilder Γ S A σ P T B τ .id-m = _
  insertionBuilder Γ S A σ P T B τ .id-T = T
  insertionBuilder Γ S A σ P T B τ .id-B = B
  insertionBuilder Γ S A σ P T B τ .id-τ = τ
  insertionBuilder Γ S A σ P T B τ .id-lh = it
  insertionBuilder Γ S A σ P T B τ .id-tlh = it

open import Catt.Typing 1 (λ x → insertionRule)

Ins≈ : (S : Tree n)
     → (ty : Typing-Tm Γ (Coh (tree-to-ctx S) A σ) C)
     → (P : Path S)
     → .⦃ bp : is-branching-path P ⦄
     → (T : Tree m)
     → {B : Ty (suc m) (height-of-branching P)}
     → (branching-path-to-var S P [ σ ]tm) ≈[ Γ ]tm (Coh (tree-to-ctx T) B τ)
     → .⦃ lh : has-linear-height (path-length P) T ⦄
     → .⦃ tlh : type-has-linear-height (path-length P) T B ⦄
     → (Coh (tree-to-ctx S) A σ) ≈[ Γ ]tm
       (Coh (tree-to-ctx (insertion-tree S P T))
            (A [ exterior-sub S P T B ]ty)
            (sub-from-insertion S P T σ τ))
Ins≈ {Γ = Γ} {A = A} {σ = σ} {τ = τ} S ty P T {B} p
  = Rule≈ zero (insertionBuilder Γ S A σ P T B τ) (λ where zero → p) ty

open import Catt.Typing.Properties.Base 1 (λ x → insertionRule)

props : (i : Fin 1) → Props i
props i .lift-rule a eq tc = begin
  liftTerm (insertionRule .lhs a) ≡⟨⟩
  Coh (tree-to-ctx id-S) id-A (liftSub id-σ)
    ≈⟨ Ins≈ id-S tc id-P id-T lem ⟩
  Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
        (id-A [ exterior-sub id-S id-P id-T id-B ]ty)
        (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ))
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (sym≃s lem2)) ⟩
  liftTerm (insertionRule .rhs a) ∎

  where
    open InsertionData a
    lem2 : liftSub (sub-from-insertion id-S id-P id-T id-σ id-τ) ≃s sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ)
    lem2 = begin
      < liftSub (sub-from-insertion id-S id-P id-T id-σ id-τ) >s ≈⟨ lift-sub-from-insertion id-S id-P id-T id-σ id-τ ⟩
      < sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ) >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning (tm-setoid-≈ (id-Γ , _))
    lem : (branching-path-to-var id-S id-P [ liftSub id-σ ]tm) ≈[ id-Γ , _ ]tm Coh (tree-to-ctx id-T) id-B (liftSub id-τ)
    lem = begin
      branching-path-to-var id-S id-P [ liftSub id-σ ]tm
        ≈⟨ reflexive≈tm (apply-lifted-sub-tm-≃ (branching-path-to-var id-S id-P) id-σ) ⟩
      liftTerm (branching-path-to-var id-S id-P [ id-σ ]tm) ≈⟨ eq zero ⟩
      Coh (tree-to-ctx id-T) id-B (liftSub id-τ) ∎
props i .susp-rule a eq tc = let
  instance _ = type-has-linear-height-susp (path-length id-P) id-T id-B
  in begin
  Coh (suspCtx (tree-to-ctx id-S)) (suspTy id-A) (suspSub id-σ)
  ≈⟨ Ins≈ (susp-tree id-S) tc (PExt id-P) (susp-tree id-T) lem ⟩
  Coh (tree-to-ctx (insertion-tree (susp-tree id-S) (PExt id-P) (susp-tree id-T)))
        (suspTy id-A [ exterior-sub (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspTy id-B) ]ty)
        (sub-from-insertion (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspSub id-σ) (suspSub id-τ))
    ≈⟨ reflexive≈tm (Coh≃ refl≃c lem-ty (sub-from-insertion-susp id-S id-P id-T id-σ id-τ)) ⟩
  Coh (suspCtx (tree-to-ctx (insertion-tree id-S id-P id-T)))
        (suspTy (id-A [ exterior-sub id-S id-P id-T id-B ]ty))
        (suspSub (sub-from-insertion id-S id-P id-T id-σ id-τ)) ∎
  where
    open InsertionData a

    lem-ty : suspTy id-A [ exterior-sub (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspTy id-B) ⦃ type-has-linear-height-susp (path-length id-P) id-T id-B ⦄ ]ty
               ≃ty
             suspTy (id-A [ exterior-sub id-S id-P id-T id-B ]ty)
    lem-ty = let
      instance _ = type-has-linear-height-susp (path-length id-P) id-T id-B
      in begin
      < suspTy id-A [ exterior-sub (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspTy id-B) ]ty >ty
        ≈⟨ sub-action-≃-ty refl≃ty (exterior-sub-susp id-S id-P id-T id-B) ⟩
      < suspTy id-A [ suspSub (exterior-sub id-S id-P id-T id-B) ]ty >ty
        ≈˘⟨ susp-functorial-ty (exterior-sub id-S id-P id-T id-B) id-A ⟩
      < suspTy (id-A [ exterior-sub id-S id-P id-T id-B ]ty) >ty ∎
      where
        open Reasoning ty-setoid

    open Reasoning (tm-setoid-≈ (suspCtx id-Γ))

    lem : branching-path-to-var (susp-tree id-S) (PExt id-P) [ suspSub id-σ ]tm
            ≈[ suspCtx id-Γ ]tm
          Coh (tree-to-ctx (susp-tree id-T)) (suspTy id-B) (suspSub id-τ)
    lem = begin
      branching-path-to-var (susp-tree id-S) (PExt id-P) [ suspSub id-σ ]tm ≡⟨⟩
      suspTm (branching-path-to-var id-S id-P)
          [ idSub (3 + id-n) ]tm
          [ suspSub id-σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (id-on-tm (suspTm (branching-path-to-var id-S id-P))) refl≃s) ⟩
      suspTm (branching-path-to-var id-S id-P) [ suspSub id-σ ]tm
        ≈˘⟨ reflexive≈tm (susp-functorial-tm id-σ (branching-path-to-var id-S id-P)) ⟩
      suspTm (branching-path-to-var id-S id-P
        [ a .InsertionData.id-σ ]tm) ≈⟨ eq zero ⟩
      Coh (tree-to-ctx (susp-tree id-T)) (suspTy id-B) (suspSub id-τ) ∎

props i .sub-rule a eqt {σ = σ} {Δ = Δ} σty tc = begin
  insertionRule .lhs a [ σ ]tm ≡⟨⟩
  Coh (tree-to-ctx id-S) id-A (σ ∘ id-σ)
    ≈⟨ Ins≈ {τ = σ ∘ id-τ} id-S tc id-P id-T lem ⟩
  Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
      (id-A [ exterior-sub id-S id-P id-T id-B ]ty)
      (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ)) ≈⟨ Coh≈ refl≈ty (reflexive≈s (sub-from-insertion-sub id-S id-P id-T id-σ id-τ σ)) ⟩
  Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
      (id-A [ exterior-sub id-S id-P id-T id-B ]ty)
      (σ ∘ sub-from-insertion id-S id-P id-T id-σ id-τ) ≡⟨⟩
  insertionRule .rhs a [ σ ]tm ∎
  where
    open InsertionData a
    open Reasoning (tm-setoid-≈ Δ)

    lem : (branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm)
            ≈[ Δ ]tm
          Coh (tree-to-ctx id-T) id-B (σ ∘ id-τ)
    lem = begin
      branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm ≈⟨ reflexive≈tm (assoc-tm σ id-σ (branching-path-to-var id-S id-P)) ⟩
      branching-path-to-var id-S id-P [ id-σ ]tm [ σ ]tm ≈⟨ eqt zero σty ⟩
      Coh (tree-to-ctx id-T) id-B (σ ∘ id-τ) ∎
