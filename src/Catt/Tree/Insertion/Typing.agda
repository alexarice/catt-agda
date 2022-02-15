{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Insertion.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Unbiased.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Variables
open import Catt.Variables.Properties

branching-path-to-var-height : (S : Tree n)
                             → (P : Path S)
                             → .⦃ bp : is-branching-path P ⦄
                             → tm-height (tree-to-ctx S) (branching-path-to-var S P) ≡ height-of-branching P
branching-path-to-var-height (Join S₁ S₂) PHere = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 0V (tree-to-ctx (suspTree S₁)) (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) ⟩
  tm-height (tree-to-ctx (suspTree S₁)) 0V
    ≡⟨ susp-tm-height 0V (tree-to-ctx S₁) ⟩
  suc (tm-height (tree-to-ctx S₁) 0V)
    ≡⟨ cong suc (linear-tree-dim S₁) ⟩
  suc (tree-dim S₁) ∎
  where
    open ≡-Reasoning
branching-path-to-var-height (Join S₁ S₂) (PExt P) = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (suspTm (branching-path-to-var S₁ P)
        [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 (suspTm (branching-path-to-var S₁ P)) (tree-to-ctx (suspTree S₁)) (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) ⟩
  tm-height (tree-to-ctx (suspTree S₁)) (suspTm (branching-path-to-var S₁ P))
    ≡⟨ susp-tm-height (branching-path-to-var S₁ P) (tree-to-ctx S₁) ⟩
  suc (tm-height (tree-to-ctx S₁) (branching-path-to-var S₁ P))
    ≡⟨ cong suc (branching-path-to-var-height S₁ P) ⟩
  suc (height-of-branching P) ∎
  where
    open ≡-Reasoning
branching-path-to-var-height (Join S₁ S₂) (PShift P) = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (branching-path-to-var S₂ P [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 (branching-path-to-var S₂ P) (tree-to-ctx S₂) (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) ⟩
  tm-height (tree-to-ctx S₂) (branching-path-to-var S₂ P)
    ≡⟨ branching-path-to-var-height S₂ P ⟩
  height-of-branching P ∎
  where
    open ≡-Reasoning

insertion-dim-lem : (S : Tree n)
                  → (P : Path S)
                  → .⦃ bp : is-branching-path P ⦄
                  → (T : Tree m)
                  → .⦃ lh : has-linear-height (path-length P) T ⦄
                  → {σ : Sub (suc n) l A}
                  → {τ : Sub (suc m) l A}
                  → Typing-Sub (tree-to-ctx S) Γ σ
                  → Typing-Sub (tree-to-ctx T) Γ τ
                  → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                  → height-of-branching P ≡ tree-dim T
insertion-dim-lem {A = A} S P T {σ} {τ} σty τty p = +-cancelʳ-≡ (height-of-branching P) (tree-dim T) (begin
  height-of-branching P + ty-dim A
    ≡˘⟨ cong (_+ ty-dim A) (branching-path-to-var-height S P) ⟩
  tm-height (tree-to-ctx S) (branching-path-to-var S P) + ty-dim A
    ≡⟨ sub-tm-height (branching-path-to-var S P) (tree-to-ctx S) σty ⟩
  tm-height _ (branching-path-to-var S P [ σ ]tm)
    ≡⟨ tm-height-≃ _ p ⟩
  tm-height _ (unbiased-comp (tree-dim T) T [ τ ]tm)
    ≡˘⟨ sub-tm-height (unbiased-comp (tree-dim T) T) (tree-to-ctx T) τty ⟩
  tm-height (tree-to-ctx T) (unbiased-comp (tree-dim T) T) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (unbiased-comp-dim (tree-dim T) T) ⟩
  tree-dim T + ty-dim A ∎)
  where
    open ≡-Reasoning

interior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T)) (interior-sub S P T)
interior-sub-Ty (Join S₁ S₂) PHere T = apply-sub-sub-typing (connect-inc-left-Ty (tree-to-ctx-Ty T) (tree-last-var-Ty T) (tree-to-ctx S₂)) (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)) (connect-Ty (tree-to-ctx-Ty T) (tree-last-var-Ty T) (tree-to-ctx-Ty S₂)))
interior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing) = apply-sub-sub-typing (suspSubTy (interior-sub-Ty S₁ P T)) (connect-susp-inc-left-Ty (tree-to-ctx-Ty (insertion-tree S₁ P T)) (tree-to-ctx S₂))
interior-sub-Ty (Join S₁ S₂) (PShift P) T = apply-sub-sub-typing (interior-sub-Ty S₂ P T) (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty (insertion-tree S₂ P T)))

exterior-sub-Ty : (S : Tree n)
                → (P : Path S)
                → .⦃ _ : is-branching-path P ⦄
                → (T : Tree m)
                → .⦃ _ : has-linear-height (path-length P) T ⦄
                → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T)) (exterior-sub S P T)
exterior-sub-Ty (Join S₁ S₂) PHere T
  = apply-sub-sub-typing
      (sub-between-connects-Ty
        (sub-from-linear-tree-unbiased-Ty-0 (suspTree S₁) T ⦃ NonZero-subst it it ⦄ (sym it))
        getSndTy
        (id-Ty (tree-to-ctx-Ty S₂))
        (tree-last-var-Ty T)
        (tree-to-ctx-Ty T)
        (tree-to-ctx-Ty S₂)
        (reflexive≈tm (sym≃tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1))))
        (reflexive≈tm (id-on-tm (Var (fromℕ _)))))
      (idSub≃-Ty (sym≃c (connect-tree-to-ctx T S₂)) (connect-Ty (tree-to-ctx-Ty T) (tree-last-var-Ty T) (tree-to-ctx-Ty S₂)))
exterior-sub-Ty (Join S₁ S₂) (PExt P) (Join T Sing)
  = sub-between-connect-susps-Ty (exterior-sub-Ty S₁ P T ⦃ p = cong pred it ⦄)
                                 (id-Ty (tree-to-ctx-Ty S₂))
                                 (tree-to-ctx-Ty (insertion-tree S₁ P T))
                                 (tree-to-ctx-Ty S₂)
                                 (reflexive≈tm (id-on-tm (Var (fromℕ _))))
exterior-sub-Ty (Join S₁ S₂) (PShift P) T
  = sub-between-connect-susps-Ty (id-Ty (tree-to-ctx-Ty S₁))
                                 (exterior-sub-Ty S₂ P T)
                                 (tree-to-ctx-Ty S₁)
                                 (tree-to-ctx-Ty (insertion-tree S₂ P T))
                                 (reflexive≈tm (sym≃tm (exterior-sub-fst-var S₂ P T)))

sub-from-insertion-lem : (S₁ : Tree n)
                       → (S₂ : Tree m)
                       → (T : Tree l)
                       → (t : Tm (suc n))
                       → .⦃ isVar t ⦄
                       → {σ : Sub (suc (m + (2 + n))) o A}
                       → {τ : Sub (suc l) o A}
                       → Typing-Sub (tree-to-ctx (Join S₁ S₂)) Γ σ
                       → Typing-Sub (tree-to-ctx T) Γ τ
                       → suspTm t [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                       → (getFst ─⟨ ⋆ ⟩⟶ getSnd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
                         ≈[ Γ ]ty
                         (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty
sub-from-insertion-lem {A = A} {Γ = Γ} S₁ S₂ T t {σ} {τ} σty τty p = ty-trunc-eq
  where
    T-dim-lem : suc (tm-height (tree-to-ctx S₁) t) ≡ tree-dim T
    T-dim-lem = +-cancelʳ-≡ (suc (tm-height (tree-to-ctx S₁) t)) (tree-dim T) (begin
      suc (tm-height (tree-to-ctx S₁) t) + ty-dim A
        ≡˘⟨ cong (_+ ty-dim A) (susp-tm-height t (tree-to-ctx S₁)) ⟩
      tm-height (suspCtx (tree-to-ctx S₁)) (suspTm t) + ty-dim A
        ≡⟨ cong (_+ ty-dim A) (sub-tm-height-0 (suspTm t) (suspCtx (tree-to-ctx S₁)) (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂))) ⟩
      tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
        (suspTm t [ connect-susp-inc-left _ _ ]tm) + ty-dim A
        ≡⟨ sub-tm-height (suspTm t [ connect-susp-inc-left _ _ ]tm) (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂)) σty ⟩
      tm-height Γ ((suspTm t [ connect-susp-inc-left _ _ ]tm) [ σ ]tm)
        ≡⟨ tm-height-≃ Γ p ⟩
      tm-height Γ (unbiased-comp (tree-dim T) T [ τ ]tm)
        ≡˘⟨ sub-tm-height (unbiased-comp (tree-dim T) T) (tree-to-ctx T) τty ⟩
      tm-height (tree-to-ctx T) (unbiased-comp (tree-dim T) T) + ty-dim A
        ≡⟨ cong (_+ ty-dim A) (unbiased-comp-dim (tree-dim T) T) ⟩
      tree-dim T + ty-dim A ∎)
      where
        open ≡-Reasoning

    instance x : NonZero (tree-dim T)
             x = NonZero-subst T-dim-lem it

    ty-eq : suspTy (tree-to-ctx S₁ ‼ getVarFin t)
                   [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
            ≈[ Γ ]ty
            unbiased-type (tree-dim T) T [ τ ]ty
    ty-eq = Ty-unique-≃ (trans≃tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (suspTm t)) p)
                        (apply-sub-tm-typing (suspTmTy (isVar-Ty (tree-to-ctx-Ty S₁) t))
                                             (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) σty))
                        (apply-sub-tm-typing (unbiased-comp-Ty (tree-dim T) T refl) τty)

    ty-trunc-eq : (getFst ─⟨ ⋆ ⟩⟶ getSnd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
                  ≈[ Γ ]ty
                  (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty
    ty-trunc-eq = begin
      (getFst ─⟨ ⋆ ⟩⟶ getSnd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (suspTy-truncate (tree-to-ctx S₁ ‼ getVarFin t)) refl≃s) ⟩
      truncate 1 (suspTy (tree-to-ctx S₁ ‼ getVarFin t))
        [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈˘⟨ reflexive≈ty (truncate-sub 1 (suspTy (tree-to-ctx S₁ ‼ getVarFin t)) (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))) ⟩
      truncate (suc (ty-dim (sub-type σ))) (suspTy (tree-to-ctx S₁ ‼ getVarFin t)
        [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
        ≈⟨ truncate-≈ {d = suc (ty-dim (sub-type σ))} refl ty-eq ⟩
      truncate (suc (ty-dim (sub-type σ)))
        (unbiased-type (tree-dim T) T [ τ ]ty)
        ≈⟨ reflexive≈ty (truncate-sub 1 (unbiased-type (tree-dim T) T) τ) ⟩
      truncate 1 (unbiased-type (tree-dim T) T) [ τ ]ty
        ≈⟨ reflexive≈ty (sub-action-≃-ty (unbiased-type-truncate-1′ (tree-dim T) T) refl≃s) ⟩
      (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty ∎
       where
        open Reasoning (ty-setoid-≈ Γ)

sub-from-insertion-fst-var : (S : Tree n)
                           → (P : Path S)
                           → .⦃ bp : is-branching-path P ⦄
                           → (T : Tree m)
                           → .⦃ lh : has-linear-height (path-length P) T ⦄
                           → {σ : Sub (suc n) l A}
                           → {τ : Sub (suc m) l A}
                           → Typing-Sub (tree-to-ctx S) Γ σ
                           → Typing-Sub (tree-to-ctx T) Γ τ
                           → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                           → Var (fromℕ _) [ sub-from-insertion S P T σ τ ]tm ≈[ Γ ]tm Var (fromℕ _) [ σ ]tm
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = begin
  Var (fromℕ _)
    [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ∘ idSub≃ (connect-tree-to-ctx T S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm _ (idSub≃ (connect-tree-to-ctx T S₂)) (Var (fromℕ _))) ⟩
  Var (fromℕ (connect-tree-length T S₂)) [ idSub≃ (connect-tree-to-ctx T S₂) ]tm
    [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (idSub≃-fst-var (connect-tree-to-ctx T S₂)) refl≃s) ⟩
  Var (fromℕ _) [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm
    ≈⟨ reflexive≈tm (sub-from-connect-fst-var τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  Var (fromℕ _) [ τ ]tm
    ≈˘⟨ src-eq (sub-from-insertion-lem S₁ S₂ T 0V σty τty p) ⟩
  getFst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getFst) ⟩
  getFst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ _) [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Γ)
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p = begin
  Var (fromℕ _) [
       sub-from-connect
       (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
       ]tm
    ≈⟨ reflexive≈tm (sub-from-connect-fst-var _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  Var (fromℕ _)
    [ unrestrict (sub-from-insertion S₁ P T
     (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (getFst [ τ ]tm) (getSnd [ τ ]tm))
     (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
    ]tm
    ≈⟨ reflexive≈tm (getFst-unrestrict (sub-from-insertion S₁ P T _ _)) ⟩
  getFst [ τ ]tm
    ≈˘⟨ src-eq (sub-from-insertion-lem S₁ S₂ (suspTree T)
                                             (branching-path-to-var S₁ P)
                                             ⦃ branching-path-to-var-is-var S₁ P ⦄
                                             σty τty p) ⟩
  getFst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getFst) ⟩
  getFst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ _) [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Γ)
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = reflexive≈tm (begin
  < Var (fromℕ _) [
       sub-from-connect
       (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (sub-from-insertion S₂ P T
        (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
       ]tm >tm
    ≈⟨ sub-from-connect-fst-var (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T
        (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) ⟩
  < Var (fromℕ _) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-inc-left-fst-var getSnd (tree-size S₂)) refl≃s ⟩
  < Var (fromℕ _) [ σ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-from-insertion-Ty : (S : Tree n)
                      → (P : Path S)
                      → .⦃ bp : is-branching-path P ⦄
                      → (T : Tree m)
                      → .⦃ lh : has-linear-height (path-length P) T ⦄
                      → {σ : Sub (suc n) l A}
                      → {τ : Sub (suc m) l A}
                      → Typing-Sub (tree-to-ctx S) Γ σ
                      → Typing-Sub (tree-to-ctx T) Γ τ
                      → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                      → Typing-Sub (tree-to-ctx (insertion-tree S P T)) Γ (sub-from-insertion S P T σ τ)
sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = apply-sub-sub-typing (idSub≃-Ty (connect-tree-to-ctx T S₂) (tree-to-ctx-Ty (connect-tree T S₂))) (sub-from-connect-Ty τty (tree-last-var-Ty T) (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) σty) lem2)
  where
    lem : ((getFst ─⟨ ⋆ ⟩⟶ getSnd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
            ≈[ Γ ]ty ((Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty)
    lem = sub-from-insertion-lem S₁ S₂ T 0V σty τty p

    lem2 : (tree-last-var T [ τ ]tm) ≈[ Γ ]tm
             (Var (fromℕ _) [ σ ∘ connect-inc-right getSnd _ ]tm)
    lem2 = begin
      tree-last-var T [ τ ]tm
        ≈˘⟨ tgt-eq lem ⟩
      getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd) ⟩
      getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var {n = tree-size (suspTree S₁)} getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ (tree-size S₂)) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p
  = sub-from-connect-Ty
      (unrestrictTy (sub-from-insertion-Ty S₁ P T
                       (restrictTy (apply-sub-sub-typing (connect-inc-left-Ty (tree-to-ctx-Ty (suspTree S₁)) getSndTy (tree-to-ctx S₂)) σty)
                                   (tree-to-ctx-Ty S₁)
                                   (apply-sub-tm-typing getFstTy τty)
                                   (apply-sub-tm-typing getSndTy τty)
                                   (sym≈tm tm-eq-1)
                                   (sym≈tm tm-eq-2))
                       (restrictTy τty
                                   (tree-to-ctx-Ty T)
                                   (apply-sub-tm-typing getFstTy τty)
                                   (apply-sub-tm-typing getSndTy τty)
                                   refl≈tm
                                   refl≈tm)
                       lem))
      getSndTy
      (apply-sub-sub-typing (connect-inc-right-Ty getSndTy (tree-to-ctx-Ty S₂)) σty)
      l2
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left getSnd _) ⟩
      < suspTm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left getSnd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left getSnd _) (suspTm (branching-path-to-var S₁ P)) ⟩
      < suspTm (branching-path-to-var S₁ P) [ connect-inc-left getSnd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (suc (tree-dim T)) (suspTree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-comp-susp-lem (tree-dim T) T) (refl≃s {σ = τ}) ⟩
      < suspTm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    instance _ = branching-path-to-var-is-var S₁ P

    tm-eq-1 : getFst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getFst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getSnd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    l2 : getSnd [ unrestrict (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm)
              (getSnd [ τ ]tm))
             (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
            ]tm
         ≈[ Γ ]tm
         (Var (fromℕ _) [ σ ∘ connect-inc-right getSnd _ ]tm)
    l2 = begin
      getSnd [ unrestrict (sub-from-insertion S₁ P T _ _) ]tm
        ≈⟨ reflexive≈tm (getSnd-unrestrict (sub-from-insertion S₁ P T _ _)) ⟩
      getSnd [ τ ]tm
        ≈˘⟨ tm-eq-2 ⟩
      getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd) ⟩
      getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p
  = sub-from-connect-Ty
      (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) σty)
      getSndTy
      (sub-from-insertion-Ty S₂ P T σcty τty p′)
      lem
    where
      σcty = apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) σty
      p′ = trans≃tm (assoc-tm _ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p
      open Reasoning (tm-setoid-≈ Γ)
      lem : getSnd [ σ ∘ connect-susp-inc-left _ _ ]tm
            ≈[ Γ ]tm
            Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
      lem = begin
        getSnd [ σ ∘ connect-susp-inc-left _ _ ]tm
          ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left _ _) getSnd) ⟩
        getSnd [ connect-susp-inc-left _ _ ]tm [ σ ]tm
          ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
        Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
          ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
        Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
          ≈˘⟨ sub-from-insertion-fst-var S₂ P T σcty τty p′ ⟩
        Var (fromℕ (insertion-tree-size S₂ P T))
          [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎

interior-sub-comm : (S : Tree n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → {σ : Sub (suc n) l A}
                   → {τ : Sub (suc m) l A}
                   → Typing-Sub (tree-to-ctx S) Γ σ
                   → Typing-Sub (tree-to-ctx T) Γ τ
                   → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                   → sub-from-insertion S P T σ τ ∘ interior-sub S P T ≈[ Γ ]s τ
interior-sub-comm {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = reflexive≈s (begin
  < sub-from-insertion (Join S₁ S₂) PHere T σ τ ∘ interior-sub (Join S₁ S₂) PHere T >s ≡⟨⟩
  < sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)
    ∘ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) (tree-size S₂)) >s
    ≈⟨ sub-action-≃-sub (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _)) (idSub≃-right-unit (connect-tree-to-ctx T S₂) _) ⟩
  < sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ connect-inc-left (tree-last-var T) (tree-size S₂) >s
    ≈⟨ sub-from-connect-inc-left τ (tree-last-var T) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < τ >s ∎)
  where
    open Reasoning sub-setoid

interior-sub-comm {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p = begin
  < sub-from-connect (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ τ ]tm) (getSnd [ τ ]tm))
    (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
  ∘ (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
    ∘ suspSub (interior-sub S₁ P T)) >s′
    ≈˘⟨ reflexive≈s (∘-assoc _ _ _) ⟩
  < sub-from-connect (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ τ ]tm) (getSnd [ τ ]tm))
    (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
    ∘ suspSub (interior-sub S₁ P T) >s′
    ≈⟨ reflexive≈s (sub-action-≃-sub refl≃s (sub-from-connect-inc-left (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ τ ]tm) (getSnd [ τ ]tm))
    (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) getSnd (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < unrestrict (sub-from-insertion S₁ P T
      (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                (getFst [ τ ]tm)
                (getSnd [ τ ]tm))
      (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
    ∘ suspSub (interior-sub S₁ P T) >s′
    ≈˘⟨ reflexive≈s (unrestrict-comp _ _) ⟩
  < unrestrict (sub-from-insertion S₁ P T
       (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ τ ]tm)
                 (getSnd [ τ ]tm))
       (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
     ∘ interior-sub S₁ P T) >s′
    ≈⟨ unrestrictEq (interior-sub-comm S₁ P T
                      (restrictTy (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) σty)
                                  (tree-to-ctx-Ty S₁)
                                  (apply-sub-tm-typing getFstTy τty)
                                  (apply-sub-tm-typing getSndTy τty)
                                  (sym≈tm tm-eq-1)
                                  (sym≈tm tm-eq-2))
                      (restrictTy τty
                                  (tree-to-ctx-Ty T)
                                  (apply-sub-tm-typing getFstTy τty)
                                  (apply-sub-tm-typing getSndTy τty)
                                  refl≈tm
                                  refl≈tm)
                      lem) ⟩
  < unrestrict (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s′
    ≈⟨ reflexive≈s (unrestrict-restrict-≃ τ refl≃tm refl≃tm) ⟩
  < τ >s′ ∎
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left getSnd _) ⟩
      < suspTm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left getSnd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left getSnd _) (suspTm (branching-path-to-var S₁ P)) ⟩
      < suspTm (branching-path-to-var S₁ P) [ connect-inc-left getSnd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (tree-dim (suspTree T)) (suspTree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-comp-susp-lem (tree-dim T) T) (refl≃s {σ = τ}) ⟩
      < suspTm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid
    instance _ = branching-path-to-var-is-var S₁ P
    tm-eq-1 : getFst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getFst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getSnd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    open Reasoning (sub-setoid-≈ (suc (tree-size (suspTree T))) Γ)

interior-sub-comm {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = begin
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    ∘ (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T) >s′
    ≈˘⟨ reflexive≈s (∘-assoc _ _ _) ⟩
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    ∘ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)
    ∘ interior-sub S₂ P T >s′
    ≈⟨ apply-sub-eq-sub (interior-sub S₂ P T) (sub-from-connect-inc-right-≈ _ _ _ lem) ⟩
  < sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ∘ interior-sub S₂ P T >s′
    ≈⟨ interior-sub-comm S₂ P T (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) σty) τty (trans≃tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p) ⟩
  < τ >s′ ∎
  where
    lem : getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
          ≈[ Γ ]tm
          Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
    lem = begin
      getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd) ⟩
      getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
        ≈˘⟨ sub-from-insertion-fst-var S₂ P T (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) σty) τty (trans≃tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p) ⟩
      Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size T)) Γ)

exterior-sub-comm : (S : Tree n)
                  → (P : Path S)
                  → .⦃ _ : is-branching-path P ⦄
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height (path-length P) T ⦄
                  → {σ : Sub (suc n) l A}
                  → {τ : Sub (suc m) l A}
                  → Typing-Sub (tree-to-ctx S) Γ σ
                  → Typing-Sub (tree-to-ctx T) Γ τ
                  → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                  → sub-from-insertion S P T σ τ ∘ exterior-sub S P T ≈[ Γ ]s σ
exterior-sub-comm {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = begin
  < sub-from-connect τ
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
       ∘ idSub≃ (connect-tree-to-ctx T S₂)
       ∘ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
         idSub (tree-last-var T)) >s′
    ≈⟨ reflexive≈s (sub-action-≃-sub (idSub≃-on-sub _ _) (idSub≃-right-unit _ _)) ⟩
  < sub-from-connect τ
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
      ∘ sub-between-connects
         (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
         idSub (tree-last-var T) >s′
    ≈⟨ between-connect-from-connect-≈ (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                                      idSub
                                      (tree-last-var T)
                                      τ
                                      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                      lem2 ⟩
  < sub-from-connect
      (τ ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0)
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ∘ idSub) >s′
    ≈⟨ sub-from-connect-≈ l1 (reflexive≈s (id-right-unit (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ getSnd (tree-size S₂) σ) ⟩
  < σ >s′ ∎

  where
    lem : ((getFst ─⟨ ⋆ ⟩⟶ getSnd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
            ≈[ Γ ]ty ((Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty)
    lem = sub-from-insertion-lem S₁ S₂ T 0V σty τty p

    lem2 : (tree-last-var T [ τ ]tm) ≈[ Γ ]tm
             (Var (fromℕ _) [ σ ∘ connect-inc-right getSnd _ ]tm)
    lem2 = begin
      tree-last-var T [ τ ]tm
        ≈˘⟨ tgt-eq lem ⟩
      getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd) ⟩
      getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var {n = tree-size (suspTree S₁)} getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ (tree-size S₂)) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    dim-lem : tree-dim (suspTree S₁) ≡ tree-dim T
    dim-lem = insertion-dim-lem (Join S₁ S₂) PHere T σty τty p

    l2 : (0V [ τ ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm)
           ≃tm (0V [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    l2 = begin
      < 0V [ τ ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm >tm
        ≈⟨ assoc-tm τ (sub-from-linear-tree-unbiased (suspTree S₁) T 0) 0V ⟩
      < 0V [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
           [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm (sub-from-linear-tree-unbiased-0V (suspTree S₁) T 0) refl≃s ⟩
      < unbiased-comp (tree-dim (suspTree S₁)) T [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-comp-≃ dim-lem (refl≃ {T = T})) (refl≃s {σ = τ}) ⟩
      < unbiased-comp (tree-dim T) T [ τ ]tm >tm
        ≈˘⟨ p ⟩
      < 0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
           [ σ ]tm >tm
        ≈˘⟨ assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) 0V ⟩
      < 0V [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l1 : τ ∘ (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
         ≈[ Γ ]s σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)
    l1 = begin
      < τ ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 >s′
        ≈⟨ sub-from-linear-Eq (suspTree S₁)
                              (apply-sub-sub-typing (sub-from-linear-tree-unbiased-Ty-0 (suspTree S₁) T ⦃ NonZero-subst dim-lem it ⦄ (sym dim-lem)) τty)
                              (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) σty)
                              l2 ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) >s′ ∎
      where
        open Reasoning (sub-setoid-≈ (suc (tree-size (suspTree S₁))) Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)

exterior-sub-comm {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ = σ} {τ} σty τty p = begin
  < sub-from-connect
    (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ sub-between-connect-susps (exterior-sub S₁ P T) idSub >s′
    ≈⟨ between-connect-from-connect-≈ (suspSub (exterior-sub S₁ P T)) idSub getSnd (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) l2 ⟩
  < sub-from-connect
    (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
      ∘ suspSub (exterior-sub S₁ P T))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ∘ idSub) >s′
    ≈⟨ sub-from-connect-≈ l3 (reflexive≈s (id-right-unit (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ getSnd (tree-size S₂) σ) ⟩
  < σ >s′ ∎
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left getSnd _) ⟩
      < suspTm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left getSnd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left getSnd _) (suspTm (branching-path-to-var S₁ P)) ⟩
      < suspTm (branching-path-to-var S₁ P) [ connect-inc-left getSnd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (tree-dim (suspTree T)) (suspTree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (Coh≃ refl≃c (unbiased-type-susp-lem (tree-dim T) T) susp-functorial-id) (refl≃s {σ = τ}) ⟩
      < suspTm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    instance _ = branching-path-to-var-is-var S₁ P

    tm-eq-1 : getFst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getFst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              getSnd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (suspTree T) (branching-path-to-var S₁ P) σty τty p)

    l2 : getSnd [ unrestrict (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-inc-left getSnd _) (getFst [ τ ]tm)
              (getSnd [ τ ]tm))
             (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
            ]tm
         ≈[ Γ ]tm
         (Var (fromℕ _) [ σ ∘ connect-inc-right getSnd _ ]tm)
    l2 = begin
      getSnd [ unrestrict (sub-from-insertion S₁ P T _ _) ]tm
        ≈⟨ reflexive≈tm (getSnd-unrestrict (sub-from-insertion S₁ P T _ _)) ⟩
      getSnd [ τ ]tm
        ≈˘⟨ tm-eq-2 ⟩
      getSnd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) getSnd) ⟩
      getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    l3 : (unrestrict
            (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ τ ]tm) (getSnd [ τ ]tm))
             (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
            ∘ suspSub (exterior-sub S₁ P T))
           ≈[ Γ ]s (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    l3 = begin
      < unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))
        ∘ suspSub (exterior-sub S₁ P T) >s′
        ≈˘⟨ reflexive≈s (unrestrict-comp _ _) ⟩
      < unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
         ∘ exterior-sub S₁ P T) >s′
        ≈⟨ unrestrictEq (exterior-sub-comm S₁ P T
             (restrictTy (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx-Ty S₁) (tree-to-ctx S₂)) σty)
                         (tree-to-ctx-Ty S₁)
                         (apply-sub-tm-typing getFstTy τty)
                         (apply-sub-tm-typing getSndTy τty)
                         (sym≈tm tm-eq-1)
                         (sym≈tm tm-eq-2))
             (restrictTy τty
                         (tree-to-ctx-Ty T)
                         (apply-sub-tm-typing getFstTy τty)
                         (apply-sub-tm-typing getSndTy τty)
                         refl≈tm
                         refl≈tm)
             lem) ⟩
      < unrestrict (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s′
        ≈⟨ unrestrict-restrict-≈ (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sym≈tm tm-eq-1) (sym≈tm tm-eq-2) ⟩
      < σ ∘ connect-inc-left getSnd _ >s′ ∎
      where
        open Reasoning (sub-setoid-≈ (suc (tree-size (suspTree S₁))) Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)

exterior-sub-comm {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = begin
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T
                       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                       τ)
    ∘ sub-between-connect-susps idSub (exterior-sub S₂ P T) >s′
    ≈⟨ between-connect-from-connect-≈ (suspSub idSub) (exterior-sub S₂ P T) getSnd (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) lem ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ suspSub idSub)
    (sub-from-insertion S₂ P T
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ
    ∘ exterior-sub S₂ P T) >s′
    ≈⟨ sub-from-connect-≈ (reflexive≈s l1) (exterior-sub-comm S₂ P T σcty τty p′) ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ getSnd (tree-size S₂) σ) ⟩
  < σ >s′ ∎
  where
    σcty = apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁) (tree-to-ctx-Ty S₂)) σty
    p′ = trans≃tm (assoc-tm _ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p

    lem : getSnd [ σ ∘ connect-susp-inc-left _ _ ]tm
            ≈[ Γ ]tm
            Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
    lem = begin
      getSnd [ σ ∘ connect-susp-inc-left _ _ ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left _ _) getSnd) ⟩
      getSnd [ connect-susp-inc-left _ _ ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var getSnd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
        ≈˘⟨ sub-from-insertion-fst-var S₂ P T σcty τty p′ ⟩
      Var (fromℕ (insertion-tree-size S₂ P T))
        [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎
        where
          open Reasoning (tm-setoid-≈ Γ)

    l1 : (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘
            suspSub idSub)
      ≃s (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    l1 = begin
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ idSub >s
        ≈⟨ id-right-unit (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) >s ∎
      where
        open Reasoning sub-setoid

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)
