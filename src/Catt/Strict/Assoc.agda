module Catt.Strict.Assoc where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Support
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Insertion.Support
open import Catt.Tree.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Pasting
open import Catt.Typing.Base

open Rule

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
    id-eq : branching-path-to-var id-S id-P [ id-σ ]tm ≃tm unbiased-comp (tree-dim id-T) id-T [ id-τ ]tm

module _ where

  open InsertionData
  insertionRule : Rule
  insertionRule .Args = InsertionData
  insertionRule .len a = a .id-l
  insertionRule .tgtCtx a = a .id-Γ
  insertionRule .lhs a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-σ)
  insertionRule .rhs a = Coh (tree-to-ctx (insertion-tree (a .id-S) (a .id-P) (a .id-T)))
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


module _ where
  open import Catt.Typing 1 (λ x → insertionRule)

  Ins≈ : (S : Tree n)
       → (ty : Typing-Tm Γ (Coh (tree-to-ctx S) A σ) C)
       → (P : Path S)
       → .⦃ bp : is-branching-path P ⦄
       → (T : Tree m)
       → (branching-path-to-var S P [ σ ]tm) ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
       → .⦃ lh : has-linear-height (path-length P) T ⦄
       → Coh (tree-to-ctx S) A σ ≈[ Γ ]tm
         Coh (tree-to-ctx (insertion-tree S P T))
             (A [ exterior-sub S P T ]ty)
             (sub-from-insertion S P T σ τ)
  Ins≈ {Γ = Γ} {A = A} {σ = σ} {τ = τ} S ty P T p
    = Rule≈ zero (insertionBuilder Γ S A σ P T τ p) ty

  open import Catt.Typing.Properties.Base 1 (λ x → insertionRule)

  lift-rule : ∀ i a → LiftRule {i} a
  lift-rule i a tc = begin
    liftTerm (insertionRule .lhs a) ≡⟨⟩
    Coh (tree-to-ctx id-S) id-A (liftSub id-σ)
      ≈⟨ Ins≈ id-S tc id-P id-T lem ⟩
    Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
        (id-A [ exterior-sub id-S id-P id-T ]ty)
        (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ))
        ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (sym≃s (lift-sub-from-insertion id-S id-P id-T id-σ id-τ))) ⟩
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
    Coh (tree-to-ctx (suspTree id-S)) (suspTy id-A) (suspSub id-σ)
      ≈⟨ Ins≈ (suspTree id-S) tc (PExt id-P) (suspTree id-T) lem ⟩
    Coh (tree-to-ctx (insertion-tree (suspTree id-S) (PExt id-P) (suspTree id-T)))
        (suspTy id-A [ exterior-sub (suspTree id-S) (PExt id-P) (suspTree id-T) ]ty)
        (sub-from-insertion (suspTree id-S) (PExt id-P) (suspTree id-T) (suspSub id-σ) (suspSub id-τ))
        ≈⟨ reflexive≈tm (Coh≃ refl≃c lem-ty (sub-from-insertion-susp id-S id-P id-T id-σ id-τ)) ⟩
    Coh (tree-to-ctx (suspTree (insertion-tree id-S id-P id-T)))
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
            [ idSub ]tm
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

module Support where

  modifyRule : Rule → Rule
  modifyRule r .Args = Σ[ a ∈ r .Args ] SuppTm (r .tgtCtx a) (r .lhs a) ≡ SuppTm (r .tgtCtx a) (r .rhs a)
  modifyRule r .len (a ,, p) = r .len a
  modifyRule r .tgtCtx (a ,, p) = r .tgtCtx a
  modifyRule r .lhs (a ,, p) = r .lhs a
  modifyRule r .rhs (a ,, p) = r .rhs a

  open import Catt.Typing 1 (λ x → modifyRule insertionRule) public
  module _ where
    open import Catt.Typing.Properties.Base 1 (λ x → modifyRule insertionRule)

    InsSupp≈ : (S : Tree n)
             → (ty : Typing-Tm Γ (Coh (tree-to-ctx S) A σ) C)
             → (P : Path S)
             → .⦃ bp : is-branching-path P ⦄
             → (T : Tree m)
             → (branching-path-to-var S P [ σ ]tm) ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
             → .⦃ lh : has-linear-height (path-length P) T ⦄
             → SuppTm Γ (Coh (tree-to-ctx S) A σ) ≡ SuppTm Γ (Coh (tree-to-ctx (insertion-tree S P T))
               (A [ exterior-sub S P T ]ty)
               (sub-from-insertion S P T σ τ))
             → Coh (tree-to-ctx S) A σ ≈[ Γ ]tm
             Coh (tree-to-ctx (insertion-tree S P T))
               (A [ exterior-sub S P T ]ty)
               (sub-from-insertion S P T σ τ)
    InsSupp≈ {Γ = Γ} {A = A} {σ = σ} {τ = τ} S ty P T p sc
      = Rule≈ zero (insertionBuilder Γ S A σ P T τ p ,, sc) ty

    lift-rule-supp : ∀ i a → LiftRule {i} a
    lift-rule-supp i (a ,, sc) tc = begin
      liftTerm (insertionRule .lhs a) ≡⟨⟩
      Coh (tree-to-ctx id-S) id-A (liftSub id-σ)
        ≈⟨ InsSupp≈ id-S tc id-P id-T lem lem2 ⟩
      Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
          (id-A [ exterior-sub id-S id-P id-T ]ty)
          (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ))
          ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (sym≃s (lift-sub-from-insertion id-S id-P id-T id-σ id-τ))) ⟩
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

        lem2 : SuppTm (id-Γ , A) (Coh (tree-to-ctx id-S) id-A (liftSub id-σ))
             ≡ SuppTm (id-Γ , A) (Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
                                   (id-A [ exterior-sub (id-S) (id-P) (id-T) ]ty)
                                   (sub-from-insertion (id-S) (id-P) (id-T) (liftSub (id-σ)) (liftSub id-τ)))
        lem2 = begin
          SuppSub (id-Γ , _) (liftSub id-σ)
            ≡⟨ cong (DC (id-Γ , _)) (supp-lift-sub id-σ) ⟩
          ewf (SuppSub id-Γ id-σ)
            ≡⟨ cong ewf sc ⟩
          ewf (SuppSub id-Γ (sub-from-insertion id-S id-P id-T id-σ id-τ))
            ≡˘⟨ cong (DC (id-Γ , _)) (supp-lift-sub (sub-from-insertion id-S id-P id-T id-σ id-τ)) ⟩
          SuppSub (id-Γ , _) (liftSub (sub-from-insertion id-S id-P id-T id-σ id-τ))
            ≡⟨ cong (SuppSub (id-Γ , _)) (≃s-to-≡ (lift-sub-from-insertion id-S id-P id-T id-σ id-τ)) ⟩
          SuppSub (id-Γ , _) (sub-from-insertion id-S id-P id-T (liftSub id-σ) (liftSub id-τ)) ∎
          where
            open ≡-Reasoning

        open Reasoning (tm-setoid-≈ (id-Γ , _))

    susp-rule-supp : ∀ i a → SuspRule {i} a
    susp-rule-supp i (a ,, sc) tc = begin
      Coh (tree-to-ctx (suspTree id-S)) (suspTy id-A) (suspSub id-σ)
        ≈⟨ InsSupp≈ (suspTree id-S) tc (PExt id-P) (suspTree id-T) lem lem2 ⟩
      Coh (tree-to-ctx (insertion-tree (suspTree id-S) (PExt id-P) (suspTree id-T)))
          (suspTy id-A [ exterior-sub (suspTree id-S) (PExt id-P) (suspTree id-T) ]ty)
          (sub-from-insertion (suspTree id-S) (PExt id-P) (suspTree id-T) (suspSub id-σ) (suspSub id-τ))
          ≈⟨ reflexive≈tm (Coh≃ refl≃c lem-ty (sub-from-insertion-susp id-S id-P id-T id-σ id-τ)) ⟩
      Coh (tree-to-ctx (suspTree (insertion-tree id-S id-P id-T)))
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
              [ idSub ]tm
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

        lem2 : SuppSub (suspCtx id-Γ) (suspSub id-σ)
             ≡ SuppSub (suspCtx id-Γ)
                       (sub-from-insertion (suspTree id-S) (PExt id-P) (suspTree id-T) (suspSub id-σ) (suspSub id-τ))
        lem2 = begin
          SuppSub (suspCtx id-Γ) (suspSub id-σ)
            ≡⟨ SuspSuppTmProp (Coh (tree-to-ctx id-S) id-A id-σ) (Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
                                                        (id-A [ exterior-sub id-S id-P id-T ]ty)
                                                        (sub-from-insertion id-S id-P id-T id-σ id-τ)) sc ⟩
          SuppSub (suspCtx id-Γ) (suspSub (sub-from-insertion id-S id-P id-T id-σ id-τ))
            ≡˘⟨ cong (SuppSub (suspCtx id-Γ)) (≃s-to-≡ (sub-from-insertion-susp id-S id-P id-T id-σ id-τ)) ⟩
          SuppSub (suspCtx id-Γ) (sub-from-insertion (suspTree id-S)
                                                     (PExt id-P)
                                                     (suspTree id-T)
                                                     (suspSub id-σ)
                                                     (suspSub id-τ)) ∎
          where
            open ≡-Reasoning

        open Reasoning (tm-setoid-≈ (suspCtx id-Γ))

    supp-rule-supp : ∀ i a → SupportRule {i} a
    supp-rule-supp i (a ,, sc) tty = sc

    open import Catt.Typing.Properties.Support 1 (λ x → modifyRule insertionRule) supp-rule-supp

    sub-rule-supp : ∀ i a → SubRule {i} a
    sub-rule-supp i (a ,, sc) {σ = σ} {Δ = Δ} σty tc = begin
      insertionRule .lhs a [ σ ]tm ≡⟨⟩
      Coh (tree-to-ctx id-S) id-A (σ ∘ id-σ)
        ≈⟨ InsSupp≈ {τ = σ ∘ id-τ} id-S tc id-P id-T lem lem2 ⟩
      Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
          (id-A [ exterior-sub id-S id-P id-T ]ty)
          (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ)) ≈⟨ Coh≈ refl≈ty (reflexive≈s (sub-from-insertion-sub id-S id-P id-T id-σ id-τ σ)) ⟩
      Coh (tree-to-ctx (insertion-tree id-S id-P id-T))
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

        lem2 : SuppSub Δ (σ ∘ id-σ)
             ≡ SuppSub Δ (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ))
        lem2 = begin
          SuppSub Δ (σ ∘ id-σ)
            ≡˘⟨ cong (DC Δ) (TransportVarSet-sub id-σ σ) ⟩
          DC Δ (TransportVarSet (FVSub id-σ) σ)
            ≡⟨ TransportVarSet-DC (FVSub id-σ) σty ⟩
          TransportVarSet (SuppSub id-Γ id-σ) σ
            ≡⟨ cong (λ - → TransportVarSet - σ) sc ⟩
          TransportVarSet (SuppSub id-Γ (sub-from-insertion id-S id-P id-T id-σ id-τ)) σ
            ≡˘⟨ TransportVarSet-DC (FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ)) σty ⟩
          DC Δ (TransportVarSet (FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ)) σ)
            ≡⟨ cong (DC Δ) (TransportVarSet-sub (sub-from-insertion id-S id-P id-T id-σ id-τ) σ) ⟩
          SuppSub Δ (σ ∘ sub-from-insertion id-S id-P id-T id-σ id-τ)
            ≡˘⟨ cong (SuppSub Δ) (≃s-to-≡ (sub-from-insertion-sub id-S id-P id-T id-σ id-τ σ)) ⟩
          SuppSub Δ (sub-from-insertion id-S id-P id-T (σ ∘ id-σ) (σ ∘ id-τ)) ∎
          where
            open ≡-Reasoning

        open Reasoning (tm-setoid-≈ Δ)

  open import Catt.Typing.Properties 1 (λ x → modifyRule insertionRule) lift-rule-supp susp-rule-supp sub-rule-supp
  open import Catt.Tree.Insertion.Typing 1 (λ x → modifyRule insertionRule) lift-rule-supp susp-rule-supp sub-rule-supp
  open import Catt.Tree.Typing 1 (λ x → modifyRule insertionRule) lift-rule-supp susp-rule-supp sub-rule-supp
  open import Catt.Typing.Properties.Support 1 (λ x → modifyRule insertionRule) supp-rule-supp public

  SuppProp : (a : InsertionData)
           → {A : Ty (insertionRule .len a)}
           → Typing-Tm (insertionRule .tgtCtx a) (insertionRule .lhs a) A
           → SuppTm (insertionRule .tgtCtx a) (insertionRule .lhs a)
           ≡ SuppTm (insertionRule .tgtCtx a) (insertionRule .rhs a)
  SuppProp a tty = begin
    SuppSub id-Γ id-σ
      ≡˘⟨ EqSuppSub (exterior-sub-comm id-S id-P id-T σty τty id-eq) ⟩
    SuppSub id-Γ (sub-from-insertion id-S id-P id-T id-σ id-τ
                 ∘ exterior-sub id-S id-P id-T)
      ≡⟨ cong (DC id-Γ) lem ⟩
    SuppSub id-Γ (sub-from-insertion id-S id-P id-T id-σ id-τ) ∎
    where
      open InsertionData a
      open ≡-Reasoning

      σty : Typing-Sub (tree-to-ctx id-S) id-Γ id-σ
      σty = coh-sub-ty tty

      τty : Typing-Sub (tree-to-ctx id-T) id-Γ id-τ
      τty = coh-sub-ty (transport-typing (apply-sub-tm-typing (isVar-Ty (branching-path-to-var id-S id-P) ⦃ branching-path-to-var-is-var id-S id-P ⦄) σty) (trans≃tm id-eq (Coh≃ refl≃c refl≃ty (id-right-unit id-τ))))

      lem : FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ
                  ∘ exterior-sub id-S id-P id-T)
          ≡ FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ)
      lem = begin
        FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ
                  ∘ exterior-sub id-S id-P id-T)
          ≡˘⟨ TransportVarSet-sub (exterior-sub id-S id-P id-T) (sub-from-insertion id-S id-P id-T id-σ id-τ) ⟩
        TransportVarSet (FVSub (exterior-sub id-S id-P id-T)) (sub-from-insertion id-S id-P id-T id-σ id-τ)
          ≡⟨ cong
               (λ - →
                  TransportVarSet - (sub-from-insertion id-S id-P id-T id-σ id-τ))
               (exterior-sub-supp-full id-S id-P id-T ⦃ p = insertion-dim-lem id-S id-P id-T σty τty id-eq ⦄) ⟩
        TransportVarSet full (sub-from-insertion id-S id-P id-T id-σ id-τ)
          ≡⟨ TransportVarSet-full (sub-from-insertion id-S id-P id-T id-σ id-τ) ⟩
        FVSub (sub-from-insertion id-S id-P id-T id-σ id-τ) ∎

module _ where
  open import Catt.Typing 1 (λ x → insertionRule)
  open import Catt.Typing.Properties 1 (λ x → insertionRule) lift-rule susp-rule sub-rule

  toSuppTyping-Ty : Typing-Ty Γ A → Support.Typing-Ty Γ A
  toSuppTyping-Tm : Typing-Tm Γ t A → Support.Typing-Tm Γ t A
  toSuppTyping-Sub : Typing-Sub Γ Δ σ → Support.Typing-Sub Γ Δ σ

  toSuppEq-Ty : A ≈[ Γ ]ty B → A Support.≈[ Γ ]ty B
  toSuppEq-Tm : s ≈[ Γ ]tm t → s Support.≈[ Γ ]tm t
  toSuppEq-Sub : σ ≈[ Γ ]s τ → σ Support.≈[ Γ ]s τ

  toSuppTyping-Ty TyStar = Support.TyStar
  toSuppTyping-Ty (TyArr sty Aty tty) = Support.TyArr (toSuppTyping-Tm sty) (toSuppTyping-Ty Aty) (toSuppTyping-Tm tty)

  toSuppTyping-Tm (TyConv tty p) = Support.TyConv (toSuppTyping-Tm tty) (toSuppEq-Ty p)
  toSuppTyping-Tm (TyVar i) = Support.TyVar i
  toSuppTyping-Tm (TyCoh Aty σty b sc) = Support.TyCoh (toSuppTyping-Ty Aty)
                                                         (toSuppTyping-Sub σty)
                                                         b
                                                         sc

  toSuppTyping-Sub (TyNull Aty) = Support.TyNull (toSuppTyping-Ty Aty)
  toSuppTyping-Sub (TyExt σty tty) = Support.TyExt (toSuppTyping-Sub σty)
                                                   (toSuppTyping-Tm tty)

  toSuppEq-Ty Star≈ = Support.Star≈
  toSuppEq-Ty (Arr≈ p q r) = Support.Arr≈ (toSuppEq-Tm p) (toSuppEq-Ty q) (toSuppEq-Tm r)

  toSuppEq-Tm (Var≈ x) = Support.Var≈ x
  toSuppEq-Tm (Sym≈ p) = Support.Sym≈ (toSuppEq-Tm p)
  toSuppEq-Tm (Trans≈ p q) = Support.Trans≈ (toSuppEq-Tm p) (toSuppEq-Tm q)
  toSuppEq-Tm (Coh≈ p q) = Support.Coh≈ (toSuppEq-Ty p) (toSuppEq-Sub q)
  toSuppEq-Tm (Rule≈ i a tty) = Support.Rule≈ i (a ,, (Support.SuppProp a (toSuppTyping-Tm tty))) (toSuppTyping-Tm tty)

  toSuppEq-Sub (Null≈ x) = Support.Null≈ (toSuppEq-Ty x)
  toSuppEq-Sub (Ext≈ p x) = Support.Ext≈ (toSuppEq-Sub p) (toSuppEq-Tm x)

  supp-rule : ∀ i a → SupportRule {i} a
  supp-rule i a tty = Support.EqSuppTm (toSuppEq-Tm (Rule≈ i a tty))

  open import Catt.Tree.Typing 1 (λ x → insertionRule) lift-rule susp-rule sub-rule
  open import Catt.Tree.Insertion.Typing 1 (λ x → insertionRule) lift-rule susp-rule sub-rule


  conv-rule : ∀ i a → ConvRule {i} a
  conv-rule i a (TyConv tty p) = TyConv (conv-rule i a tty) p
  conv-rule i a (TyCoh Aty σty b sc)
    = TyConv (TyCoh ⦃ tree-to-pd (insertion-tree id-S id-P id-T) ⦄
            (apply-sub-ty-typing Aty (exterior-sub-Ty id-S id-P id-T ⦃ p = dim-lem ⦄))
            (sub-from-insertion-Ty id-S id-P id-T σty τty id-eq)
            b
            (insertion-supp-condition b _ id-S id-P id-T ⦃ p = dim-lem ⦄ sc))
            lem
    where
      open InsertionData a

      τty : Typing-Sub (tree-to-ctx id-T) id-Γ id-τ
      τty = coh-sub-ty (transport-typing (apply-sub-tm-typing (isVar-Ty (branching-path-to-var id-S id-P) ⦃ branching-path-to-var-is-var id-S id-P ⦄) σty) (trans≃tm id-eq (Coh≃ refl≃c refl≃ty (id-right-unit id-τ))))

      dim-lem : height-of-branching id-P ≡ tree-dim id-T
      dim-lem = insertion-dim-lem id-S id-P id-T σty τty id-eq

      lem : id-A [ exterior-sub id-S id-P id-T ]ty
                 [ sub-from-insertion id-S id-P id-T id-σ id-τ ]ty
          ≈[ id-Γ ]ty (id-A [ id-σ ]ty)
      lem = begin
        id-A [ exterior-sub id-S id-P id-T ]ty
             [ sub-from-insertion id-S id-P id-T id-σ id-τ ]ty
          ≈˘⟨ reflexive≈ty (assoc-ty _ _ id-A) ⟩
        id-A [ sub-from-insertion id-S id-P id-T id-σ id-τ ∘ exterior-sub id-S id-P id-T ]ty
          ≈⟨ apply-sub-eq-ty id-A (exterior-sub-comm id-S id-P id-T σty τty id-eq) ⟩
        id-A [ id-σ ]ty ∎
        where
          open Reasoning (ty-setoid-≈ _)
