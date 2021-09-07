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

record InsertionData : Set where
  field
    id-l : ℕ
    id-Γ : Ctx id-l
    id-n : ℕ
    id-S : Tree id-n
    id-d : ℕ
    id-A : Ty (suc id-n) id-d
    id-σ : Sub (suc id-n) id-l
    id-d′ : ℕ
    id-C : Ty id-l id-d′
    id-P : Path id-S
    .⦃ id-bp ⦄ : is-branching-path id-P
    id-m : ℕ
    id-T : Tree id-m
    id-B : Ty (suc id-m) (height-of-branching id-P)
    id-τ : Sub (suc id-m) id-l
    id-d″ : ℕ
    id-D : Ty id-l id-d″
    .⦃ id-lh ⦄ : has-linear-height (path-length id-P) id-T
    .⦃ id-tlh ⦄ : type-has-linear-height (path-length id-P) id-T id-B

module _ where
  open InsertionData
  insertionRule : Rule
  insertionRule .Args = InsertionData
  insertionRule .tctCount = 2
  insertionRule .eqtCount = 1
  insertionRule .tgtHeight zero a = a .id-d′
  insertionRule .tgtHeight (suc i) a = a .id-d″
  insertionRule .tctLen zero a = a .id-l
  insertionRule .tctLen (suc i) a = a .id-l
  insertionRule .tct zero a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-σ)
  insertionRule .tct (suc i) a = Coh (tree-to-ctx (a .id-T)) (a .id-B) (a .id-τ)
  insertionRule .tctTy zero a = a .id-C
  insertionRule .tctTy (suc i) a = a .id-D
  insertionRule .tctCtx zero a = a .id-Γ
  insertionRule .tctCtx (suc i) a = a .id-Γ
  insertionRule .eqtlhsLen zero a = a .id-l
  insertionRule .eqtlhs zero a = branching-path-to-var (a .id-S) (a .id-P) [ a .id-σ ]tm
  insertionRule .eqtrhsLen zero a = a .id-l
  insertionRule .eqtrhs zero a = Coh (tree-to-ctx (a .id-T)) (a .id-B) (a .id-τ)
  insertionRule .lhsLen a = a .id-l
  insertionRule .rhsLen a = a .id-l
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
                   → (C : Ty l d′)
                   → (T : Tree m)
                   → (B : Ty (suc m) (height-of-branching P))
                   → (τ : Sub (suc m) l)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → .⦃ tlh : type-has-linear-height (path-length P) T B ⦄
                   → (D : Ty l d″)
                   → InsertionData
  insertionBuilder Γ S A σ P C T B τ D .id-l = _
  insertionBuilder Γ S A σ P C T B τ D .id-Γ = Γ
  insertionBuilder Γ S A σ P C T B τ D .id-n = _
  insertionBuilder Γ S A σ P C T B τ D .id-S = S
  insertionBuilder Γ S A σ P C T B τ D .id-d = _
  insertionBuilder Γ S A σ P C T B τ D .id-A = A
  insertionBuilder Γ S A σ P C T B τ D .id-σ = σ
  insertionBuilder Γ S A σ P C T B τ D .id-d′ = _
  insertionBuilder Γ S A σ P C T B τ D .id-C = C
  insertionBuilder Γ S A σ P C T B τ D .id-P = P
  insertionBuilder Γ S A σ P C T B τ D .id-bp = it
  insertionBuilder Γ S A σ P C T B τ D .id-m = _
  insertionBuilder Γ S A σ P C T B τ D .id-T = T
  insertionBuilder Γ S A σ P C T B τ D .id-B = B
  insertionBuilder Γ S A σ P C T B τ D .id-τ = τ
  insertionBuilder Γ S A σ P C T B τ D .id-d″ = _
  insertionBuilder Γ S A σ P C T B τ D .id-D = D
  insertionBuilder Γ S A σ P C T B τ D .id-lh = it
  insertionBuilder Γ S A σ P C T B τ D .id-tlh = it

open import Catt.Typing 1 (λ x → insertionRule)

Ins≈ : (S : Tree n)
     → (ty : Typing-Tm Γ (Coh (tree-to-ctx S) A σ) C)
     → (P : Path S)
     → .⦃ bp : is-branching-path P ⦄
     → (T : Tree m)
     → {B : Ty (suc m) (height-of-branching P)}
     → (ty2 : Typing-Tm Γ (Coh (tree-to-ctx T) B τ) D)
     → (branching-path-to-var S P [ σ ]tm) ≈tm (Coh (tree-to-ctx T) B τ)
     → .⦃ lh : has-linear-height (path-length P) T ⦄
     → .⦃ tlh : type-has-linear-height (path-length P) T B ⦄
     → (Coh (tree-to-ctx S) A σ) ≈tm
       (Coh (tree-to-ctx (insertion-tree S P T))
            (A [ exterior-sub S P T B ]ty)
            (sub-from-insertion S P T σ τ))
Ins≈ {Γ = Γ} {A = A} {σ = σ} {C = C} {τ = τ} {D = D} S ty P T {B} ty2 eq
  = Rule≈ zero
          (insertionBuilder Γ S A σ P C T B τ D)
          (λ where zero → ty
                   (suc j) → ty2)
          λ where zero → eq


open import Catt.Typing.Properties.Base 1 (λ x → insertionRule)

props : (i : Fin 1) → Props i
props i .lift-rule a tc eq = begin
  < liftTerm (insertionRule .lhs a) >tm ≡⟨⟩
  < (Coh (tree-to-ctx id-S) id-A (liftSub id-σ)) >tm
    ≈⟨ Ins≈ id-S (tc zero {A = ⋆}) id-P id-T (tc (suc zero)) lem ⟩
  < Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
        (id-A [ exterior-sub id-S id-P id-T id-B ]ty)
        (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ))
    >tm ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (sym≃s lem2)) ⟩
  < liftTerm (insertionRule .rhs a) >tm ∎

  where
    open InsertionData a
    lem2 : liftSub (sub-from-insertion id-S id-P id-T id-σ id-τ) ≃s sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ)
    lem2 = begin
      < liftSub (sub-from-insertion id-S id-P id-T id-σ id-τ) >s ≈⟨ lift-sub-from-insertion id-S id-P id-T id-σ id-τ ⟩
      < sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ) >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid-≈
    lem : (branching-path-to-var id-S id-P [ liftSub id-σ ]tm) ≈tm Coh (tree-to-ctx id-T) id-B (liftSub id-τ)
    lem = begin
      < branching-path-to-var id-S id-P [ liftSub id-σ ]tm >tm
        ≈⟨ reflexive≈tm (apply-lifted-sub-tm-≃ (branching-path-to-var id-S id-P) id-σ) ⟩
      < liftTerm (branching-path-to-var id-S id-P [ id-σ ]tm) >tm ≈⟨ eq zero ⟩
      < Coh (tree-to-ctx id-T) id-B (liftSub id-τ) >tm ∎

props i .susp-rule a ty eq = let
  instance _ = type-has-linear-height-susp (path-length id-P) id-T id-B
  in begin
  < Coh (suspCtx (tree-to-ctx id-S)) (suspTy id-A) (suspSub id-σ) >tm
    ≈⟨ Ins≈ (susp-tree id-S) (ty zero) (PExt id-P) (susp-tree id-T) (ty (suc zero)) {!!} ⟩
  < Coh (tree-to-ctx (insertion-tree (susp-tree id-S) (PExt id-P) (susp-tree id-T)))
        (suspTy id-A [ exterior-sub (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspTy id-B) ]ty)
        (sub-from-insertion (susp-tree id-S) (PExt id-P) (susp-tree id-T) (suspSub id-σ) (suspSub id-τ))
    >tm ≈⟨ reflexive≈tm (Coh≃ refl≃c {!!} {!!}) ⟩
  < Coh (suspCtx (tree-to-ctx (insertion-tree id-S id-P id-T)))
        (suspTy (id-A [ exterior-sub id-S id-P id-T id-B ]ty))
        (suspSub (sub-from-insertion id-S id-P id-T id-σ id-τ)) >tm ∎
  where
    open InsertionData a
    open Reasoning tm-setoid-≈

    -- lem : (branching-path-to-var (susp-tree (a .id-S)) (PExt (a .id-P)) _ [
    --          suspSub (a .id-σ) ]tm)
    --         ≈tm
    --         Coh (tree-to-ctx (susp-tree (a .id-T))) (suspTy (a .id-C)) _
    --         (suspSub (a .id-τ))
    -- lem = begin
    --   < suspTm (branching-path-to-var (a .id-S) (a .id-P) _) [ idSub (suspCtx (tree-to-ctx (a .id-S))) ]tm [ suspSub (a .id-σ) ]tm >tm
    --     ≈⟨ reflexive≈tm (sub-action-≃-tm (id-on-tm (suspTm (branching-path-to-var (a .id-S) (a .id-P) _))) refl≃s) ⟩
    --   < suspTm (branching-path-to-var (a .id-S) (a .id-P) _) [ suspSub (a .id-σ) ]tm >tm ≈⟨ reflexive≈tm (sym≃tm (susp-functorial-tm (a .id-σ) (branching-path-to-var (a .id-S) (a .id-P) (a .id-bp)))) ⟩
    --   < suspTm (branching-path-to-var (a .id-S) (a .id-P) _ [ a .id-σ ]tm) >tm ≈⟨ eq zero ⟩
    --   < Coh (tree-to-ctx (susp-tree (a .id-T))) (suspTy (a .id-C)) _ (suspSub (a .id-τ)) >tm ∎
