{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

module Catt.Strict.Assoc where

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
open Rule
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Connection.Support
open import Catt.Connection.Properties
open import Catt.Tree.Properties

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
    id-eq : branching-path-to-var id-S id-P [ id-σ ]tm ≃tm unbiased-comp (tree-dim id-T) id-T [ id-τ ]tm

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
                   → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
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
     → (branching-path-to-var S P [ σ ]tm) ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
     → .⦃ lh : has-linear-height (path-length P) T ⦄
     → Coh S A σ ≈[ Γ ]tm
       Coh (insertion-tree S P T)
           (A [ exterior-sub S P T ]ty)
           (sub-from-insertion S P T σ τ)
Ins≈ {Γ = Γ} {A = A} {σ = σ} {τ = τ} S ty P T p
  = Rule≈ zero (insertionBuilder Γ S A σ P T τ p) ty

module _ where
  open import Catt.Typing.Properties.Base 1 (λ x → insertionRule)

  lift-rule : ∀ i a → LiftRule {i} a
  lift-rule i a tc = begin
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
            unbiased-comp (tree-dim id-T) id-T [ liftSub id-τ ]tm
      lem = begin
        < branching-path-to-var id-S id-P [ liftSub id-σ ]tm >tm
          ≈⟨ apply-lifted-sub-tm-≃ (branching-path-to-var id-S id-P) id-σ ⟩
        < liftTerm (branching-path-to-var id-S id-P [ id-σ ]tm) >tm
          ≈⟨ lift-tm-≃ id-eq ⟩
        < liftTerm (unbiased-comp (tree-dim id-T) id-T [ id-τ ]tm) >tm
          ≈˘⟨ apply-lifted-sub-tm-≃ (unbiased-comp (tree-dim id-T) id-T) id-τ ⟩
        < unbiased-comp (tree-dim id-T) id-T [ liftSub id-τ ]tm >tm ∎
        where
          open Reasoning tm-setoid

      open Reasoning (tm-setoid-≈ (id-Γ , _))

  susp-rule : ∀ i a → SuspRule {i} a
  susp-rule i a tc = begin
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
            unbiased-comp (tree-dim (suspTree id-T)) (suspTree id-T) [ unrestrict (suspSubRes id-τ) ]tm
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
        < suspTm (unbiased-comp (tree-dim id-T) id-T [ id-τ ]tm) >tm
          ≈⟨ susp-functorial-tm id-τ (unbiased-comp (tree-dim id-T) id-T) ⟩
        < suspTm (unbiased-comp (tree-dim id-T) id-T) [ suspSub id-τ ]tm >tm
          ≈⟨ sub-action-≃-tm (unbiased-comp-susp-lem (tree-dim id-T) id-T) (refl≃s {σ = suspSub id-τ}) ⟩
        < unbiased-comp (tree-dim (suspTree id-T)) (suspTree id-T) [ suspSub id-τ ]tm >tm ∎
        where
          open Reasoning tm-setoid

      open Reasoning (tm-setoid-≈ (suspCtx id-Γ))

  sub-rule : ∀ i a → SubRule {i} a
  sub-rule i a {σ = σ} {Δ = Δ} σty tc = begin
    insertionRule .lhs a [ σ ]tm ≡⟨⟩
    Coh id-S id-A (σ ∘ id-σ)
      ≈⟨ Ins≈ {τ = σ ∘ id-τ} id-S tc id-P id-T lem ⟩
    Coh (insertion-tree id-S id-P id-T)
        (id-A [ exterior-sub id-S id-P id-T ]ty)
        (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ)) ≈⟨ Coh≈ refl≈ty (reflexive≈s (sub-from-insertion-sub id-S id-P id-T id-σ id-τ σ)) ⟩
    Coh (insertion-tree id-S id-P id-T)
        (id-A [ exterior-sub id-S id-P id-T ]ty)
        (σ ∘ sub-from-insertion id-S id-P id-T id-σ id-τ) ≡⟨⟩
    insertionRule .rhs a [ σ ]tm ∎
    where
      open InsertionData a

      lem : branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm
        ≃tm unbiased-comp (tree-dim id-T) id-T [ σ ∘ id-τ ]tm
      lem = begin
        < branching-path-to-var id-S id-P [ σ ∘ id-σ ]tm >tm
          ≈⟨ assoc-tm σ id-σ (branching-path-to-var id-S id-P) ⟩
        < branching-path-to-var id-S id-P [ id-σ ]tm [ σ ]tm >tm
          ≈⟨ sub-action-≃-tm id-eq refl≃s ⟩
        < unbiased-comp (tree-dim id-T) id-T [ id-τ ]tm [ σ ]tm >tm
          ≈˘⟨ assoc-tm σ id-τ (unbiased-comp (tree-dim id-T) id-T) ⟩
        < unbiased-comp (tree-dim id-T) id-T [ σ ∘ id-τ ]tm >tm ∎
        where
          open Reasoning tm-setoid

      open Reasoning (tm-setoid-≈ Δ)

open import Catt.Typing.Properties 1 (λ x → insertionRule) lift-rule susp-rule sub-rule

-- example-ctx : Ctx 7
-- example-ctx = ∅ , ⋆ , ⋆ , 1V ─⟨ ⋆ ⟩⟶ 0V , ⋆ , 2V ─⟨ ⋆ ⟩⟶ 0V , ⋆ , 2V ─⟨ ⋆ ⟩⟶ 0V

-- example-tree : Tree 6
-- example-tree = Join Sing (Join Sing (Join Sing Sing))

-- test1 : tree-to-ctx (example-tree) ≡ example-ctx
-- test1 = refl

-- test2 : unbiased-type 1 example-tree ≡ 6V ─⟨ ⋆ ⟩⟶ 1V
-- test2 = refl

-- example-tm-1 : Tm 7
-- example-tm-1 = Coh example-tree (6V ─⟨ ⋆ ⟩⟶ 1V) (idSub _)

-- example-tm-2 : Tm 7
-- example-tm-2 = Coh (Join Sing (Join Sing Sing)) (4V ─⟨ ⋆ ⟩⟶ 1V)
--   ⟨ ⟨ ⟨ ⟨ ⟨ ⟨⟩ , 6V ⟩ , 5V ⟩ , 4V ⟩ , 1V ⟩ ,
--     Coh (Join Sing (Join Sing Sing)) (4V ─⟨ ⋆ ⟩⟶ 1V)
--     ⟨ ⟨ ⟨ ⟨ ⟨ ⟨⟩ , 5V ⟩ , 3V ⟩ , 2V ⟩ , 1V ⟩ , 0V ⟩ ⟩

-- open import Data.Bool
-- open import Data.Product renaming (_,_ to _,,_)
-- open import Catt.Tree.Unbiased.Typing 1 (λ x → insertionRule) lift-rule susp-rule sub-rule

-- example-tm-1-Ty : Typing-Tm example-ctx example-tm-1 (6V ─⟨ ⋆ ⟩⟶ 1V)
-- example-tm-1-Ty = TyCoh (TyArr (var-Ty (example-ctx) (suc (suc (suc (suc (suc (suc zero))))))) TyStar (var-Ty example-ctx (suc zero))) id-Ty true (refl ,, refl) refl≈ty

-- example-tm-2-Ty : Typing-Tm example-ctx example-tm-2 (6V ─⟨ ⋆ ⟩⟶ 1V)
-- example-tm-2-Ty = TyCoh (unbiased-type-Ty 1 (Join Sing (Join Sing Sing)) (s≤s z≤n))
--   (TyExt (TyExt (TyExt (TyExt (TyExt (TyNull TyStar) (var-Ty example-ctx (suc (suc (suc (suc (suc (suc zero)))))))) (var-Ty example-ctx (suc (suc (suc (suc (suc zero))))))) (var-Ty example-ctx (suc (suc (suc (suc zero)))))) (var-Ty example-ctx (suc zero))) (TyCoh (unbiased-type-Ty 1 (Join Sing (Join Sing Sing)) (s≤s z≤n)) (TyExt (TyExt (TyExt (TyExt (TyExt (TyNull TyStar) (var-Ty example-ctx (suc (suc (suc (suc (suc zero))))))) (var-Ty example-ctx (suc (suc (suc zero))))) (var-Ty example-ctx (suc (suc zero)))) (var-Ty example-ctx (suc zero))) (var-Ty example-ctx zero)) true (refl ,, refl) refl≈ty))
--   true (refl ,, refl) refl≈ty

-- example-ins : example-tm-2 ≈[ example-ctx ]tm example-tm-1
-- example-ins = Ins≈ (Join Sing (Join Sing Sing)) example-tm-2-Ty (PShift PHere) (Join Sing (Join Sing Sing)) refl≃tm

open import Catt.Tree.Insertion.Typing 1 (λ i → insertionRule) lift-rule susp-rule sub-rule

-- convRule : ∀ i a → ConvRule {i} a
-- convRule i a (TyCoh {B = B} Aty σty b sc p) = TyCoh (apply-sub-ty-typing Aty (exterior-sub-Ty id-S id-P id-T ⦃ p = insertion-dim-lem id-S id-P id-T σty τty p′ ⦄)) (sub-from-insertion-Ty id-S id-P id-T σty τty p′) b {!!} lem
--   where
--     open InsertionData a

--     p′ = trans≃tm id-eq (Coh≃ refl≃ refl≃ty (sym≃s (id-right-unit _)))

--     τty : Typing-Sub (tree-to-ctx id-T) id-Γ id-τ
--     τty = coh-sub-ty (transport-typing (apply-sub-tm-typing (isVar-Ty (tree-to-ctx id-S) (branching-path-to-var id-S id-P) ⦃ branching-path-to-var-is-var id-S id-P ⦄) σty) id-eq)

--     lem : id-A [ exterior-sub id-S id-P id-T ]ty [ sub-from-insertion id-S id-P id-T id-σ id-τ ]ty
--             ≈[ id-Γ ]ty B
--     lem = begin
--       id-A [ exterior-sub id-S id-P id-T ]ty [ sub-from-insertion id-S id-P id-T id-σ id-τ ]ty
--         ≈˘⟨ reflexive≈ty (assoc-ty _ _ id-A) ⟩
--       id-A [ sub-from-insertion id-S id-P id-T id-σ id-τ ∘ exterior-sub id-S id-P id-T ]ty
--         ≈⟨ apply-sub-eq-ty id-A (exterior-sub-comm id-S id-P id-T σty τty p′) ⟩
--       id-A [ id-σ ]ty
--         ≈⟨ p ⟩
--       B ∎
--       where
--         open Reasoning (ty-setoid-≈ id-Γ)

suppStuff : (S : Tree n)
          → (P : Path S)
          → .⦃ bp : is-branching-path P ⦄
          → (T : Tree m)
          → {σ : Sub (suc n) l A}
          → {τ : Sub (suc m) l A}
          → Typing-Sub (tree-to-ctx S) Γ σ
          → Typing-Sub (tree-to-ctx T) Γ τ
          → (branching-path-to-var S P [ σ ]tm) ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
          → .⦃ lh : has-linear-height (path-length P) T ⦄
          → FVSub (sub-from-insertion S P T σ τ) ≡ FVSub σ
suppStuff (Join S₁ S₂) PHere T {σ} {τ} σty τty p = begin
  FVSub
      (sub-from-connect τ
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
       ∘ idSub≃ (connect-tree-to-ctx T S₂))
    ≡˘⟨ {!!} ⟩
  FVSub
      (sub-from-connect τ
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ≡⟨ sub-from-connect-supp τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) {!!} ⟩
  FVSub τ ∪ FVSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ≡⟨ {!!} ⟩
  {!!} ∎
  where
    open ≡-Reasoning
suppStuff (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p = begin
  FVSub
      (sub-from-connect
       (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ≡⟨ sub-from-connect-supp (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) {!!} ⟩
  FVSub
    (unrestrict
     (sub-from-insertion S₁ P T
      (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (getFst [ τ ]tm) (getSnd [ τ ]tm))
      (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    ∪ FVSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ≡⟨ cong
         (_∪
          FVSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
         lem ⟩
  FVSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ∪
    FVSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ≡˘⟨ sub-from-connect-supp (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) {!!} ⟩
  FVSub
    (sub-from-connect
     (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ≡⟨ cong FVSub (≃s-to-≡ (sub-from-connect-prop′ getSnd (tree-size S₂) σ)) ⟩
  FVSub σ ∎
  where
    open ≡-Reasoning
    lem : FVSub
            (unrestrict
             (sub-from-insertion S₁ P T
              (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
               (getFst [ τ ]tm) (getSnd [ τ ]tm))
              (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
            ≡ FVSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    lem = begin
      FVSub
        (unrestrict
         (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ τ ]tm) (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
        ≡⟨ unrestrict-supp (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ τ ]tm) (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) ⟩
      FVSub
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
        ≡⟨ suppStuff S₁ P T {!!} {!!} {!!} ⟩
      FVSub
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
         (getFst [ τ ]tm) (getSnd [ τ ]tm))
        ≡⟨ {!!} ⟩
      {!!} ∎
suppStuff (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = begin
  FVSub
      (sub-from-connect
       (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (sub-from-insertion S₂ P T
        (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ))
    ≡⟨ sub-from-connect-supp (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) {!!} ⟩
  FVSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ∪
    FVSub
    (sub-from-insertion S₂ P T
     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    ≡⟨ cong
         (FVSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          ∪_)
         (suppStuff S₂ P T {!!} {!!} {!!}) ⟩
  FVSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ∪
    FVSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ≡˘⟨ sub-from-connect-supp (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) {!!} ⟩
  FVSub
    (sub-from-connect
     (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ≡⟨ cong FVSub (≃s-to-≡ (sub-from-connect-prop′ getSnd (tree-size S₂) σ)) ⟩
  FVSub σ ∎
  where
    open ≡-Reasoning
