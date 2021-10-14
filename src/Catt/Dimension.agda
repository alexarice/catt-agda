{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

module Catt.Dimension where

open import Catt.Syntax
open import Data.Nat
open import Catt.Variables
open import Data.Fin using (suc;zero;Fin)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree
open import Catt.Tree.Properties
open import Induction.WellFounded
open import Data.Unit using (⊤; tt)

data CtxSyntax : ℕ → Set where
  CtxTm : (t : Tm n) → (Γ : Ctx n) → CtxSyntax n
  CtxTy : (A : Ty n) → (Γ : Ctx n) → CtxSyntax n
  CtxSub : (σ : Sub m n A) → (Γ : Ctx n) → CtxSyntax n

data _≺_ : CtxSyntax n → CtxSyntax m → Set where
  Tm1 : CtxTy A Γ ≺ CtxTm 0V (Γ , A)
  Tm2 : {i : Fin n} → CtxTm (Var i) Γ ≺ CtxTm (Var (suc i)) (Γ , A)
  Tm3 : CtxTy A (tree-to-ctx S) ≺ CtxTm (Coh S A σ) Γ
  Tm4 : CtxSub σ Γ ≺ CtxTm (Coh S A σ) Γ
  Ty1 : CtxTm s Γ ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ
  Ty2 : CtxTy A Γ ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ
  Ty3 : CtxTm t Γ ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ
  Sub1 : CtxTy A Γ ≺ CtxSub (⟨⟩ {A = A}) Γ
  Sub2 : CtxSub σ Γ ≺ CtxSub ⟨ σ , t ⟩ Γ
  Sub3 : CtxTm t Γ ≺ CtxSub ⟨ σ , t ⟩ Γ

data Acc≺ (x : CtxSyntax n) : Set where
  acc≺ : (rec : ∀ {m} (y : CtxSyntax m) → y ≺ x → Acc≺ y) → Acc≺ x

access-tm-glob-var : (t : Tm n) → ⦃ isVar t ⦄ → (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → Acc≺ (CtxTm t Γ)
access-ty-glob-var : (A : Ty n) → ⦃ ty-is-globular A ⦄ → (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → Acc≺ (CtxTy A Γ)

access-tm-glob-var (Var zero) (Γ , A) ⦃ a ,, b ⦄ = acc≺ (λ where ._ Tm1 → access-ty-glob-var A ⦃ b ⦄ Γ ⦃ a ⦄ )
access-tm-glob-var (Var (suc i)) (Γ , A) ⦃ a ,, b ⦄ = acc≺ (λ where ._ Tm2 → access-tm-glob-var (Var i) Γ ⦃ a ⦄)

access-ty-glob-var ⋆ Γ = acc≺ (λ y ())
access-ty-glob-var (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ) → Acc≺ y
    f .(CtxTm s Γ) Ty1 = access-tm-glob-var s ⦃ a ⦄ Γ
    f .(CtxTy A Γ) Ty2 = access-ty-glob-var A ⦃ b ⦄ Γ
    f .(CtxTm t Γ) Ty3 = access-tm-glob-var t ⦃ c ⦄ Γ

access-tm-glob : (t : Tm n) → (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → Acc≺ (CtxTm t Γ)
access-ty-glob : (A : Ty n) → (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → Acc≺ (CtxTy A Γ)
access-sub-glob : (σ : Sub m n A) → (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → Acc≺ (CtxSub σ Γ)

access-tm-glob (Var i) Γ = access-tm-glob-var (Var i) Γ
access-tm-glob (Coh S A σ) Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxTm (Coh S A σ) Γ) → Acc≺ y
    f .(CtxTy A (tree-to-ctx S)) Tm3 = access-ty-glob A (tree-to-ctx S) ⦃ tree-to-ctx-glob S ⦄
    f .(CtxSub σ Γ) Tm4 = access-sub-glob σ Γ

access-ty-glob ⋆ Γ = acc≺ (λ y ())
access-ty-glob (s ─⟨ A ⟩⟶ t) Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ) → Acc≺ y
    f .(CtxTm s Γ) Ty1 = access-tm-glob s Γ
    f .(CtxTy A Γ) Ty2 = access-ty-glob A Γ
    f .(CtxTm t Γ) Ty3 = access-tm-glob t Γ

access-sub-glob {A = A} ⟨⟩ Γ = acc≺ λ where ._ Sub1 → access-ty-glob A Γ
access-sub-glob ⟨ σ , t ⟩ Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxSub ⟨ σ , t ⟩ Γ) → Acc≺ y
    f .(CtxSub σ Γ) Sub2 = access-sub-glob σ Γ
    f .(CtxTm t Γ) Sub3 = access-tm-glob t Γ

access-tm : (t : Tm n) → (Γ : Ctx n) → Acc≺ (CtxTm t Γ)
access-ty : (A : Ty n) → (Γ : Ctx n) → Acc≺ (CtxTy A Γ)
access-sub : (σ : Sub m n A) → (Γ : Ctx n) → Acc≺ (CtxSub σ Γ)

access-tm (Var zero) (Γ , A) = acc≺ (λ where ._ Tm1 → access-ty A Γ)
access-tm (Var (suc i)) (Γ , A) = acc≺ (λ where ._ Tm2 → access-tm (Var i) Γ)
access-tm (Coh S A σ) Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxTm (Coh S A σ) Γ) → Acc≺ y
    f .(CtxTy A (tree-to-ctx S)) Tm3 = access-ty-glob A (tree-to-ctx S) ⦃ tree-to-ctx-glob S ⦄
    f .(CtxSub σ Γ) Tm4 = access-sub σ Γ

access-ty ⋆ Γ = acc≺ (λ y ())
access-ty (s ─⟨ A ⟩⟶ t) Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxTy (s ─⟨ A ⟩⟶ t) Γ) → Acc≺ y
    f .(CtxTm s Γ) Ty1 = access-tm s Γ
    f .(CtxTy A Γ) Ty2 = access-ty A Γ
    f .(CtxTm t Γ) Ty3 = access-tm t Γ

access-sub {A = A} ⟨⟩ Γ = acc≺ (λ where ._ Sub1 → access-ty A Γ)
access-sub ⟨ σ , t ⟩ Γ = acc≺ f
  where
    f : (y : CtxSyntax n) → (y ≺ CtxSub ⟨ σ , t ⟩ Γ) → Acc≺ y
    f .(CtxSub σ Γ) Sub2 = access-sub σ Γ
    f .(CtxTm t Γ) Sub3 = access-tm t Γ

access : (x : CtxSyntax n) → Acc≺ x
access (CtxTm t Γ) = access-tm t Γ
access (CtxTy A Γ) = access-ty A Γ
access (CtxSub σ Γ) = access-sub σ Γ

≺-rec : (A : ∀ {n} → CtxSyntax n → Set)
      → (∀ {n} → (x : CtxSyntax n)
               → (∀ {m} → (y : CtxSyntax m) → y ≺ x → A y)
               → A x)
      → (x : CtxSyntax m) → A x
≺-rec A rec x = f x (access x)
  where
    f : (x : CtxSyntax n) → Acc≺ x → A x
    f x (acc≺ r) = rec x λ y p → f y (r y p)


fullDimCtxSyntax : CtxSyntax n → ℕ
fullDimCtxSyntax = ≺-rec (λ _ → ℕ) r
  where
    r : (x : CtxSyntax n) → (∀ {m} → (y : CtxSyntax m) → y ≺ x → ℕ) → ℕ
    r (CtxTm (Var zero) (Γ , A)) rec = rec (CtxTy A Γ) Tm1
    r (CtxTm (Var (suc i)) (Γ , A)) rec = rec (CtxTm (Var i) Γ) Tm2
    r (CtxTm (Coh S A σ) Γ) rec = rec (CtxTy A (tree-to-ctx S)) Tm3 ⊔ rec (CtxSub σ Γ) Tm4
    r (CtxTy ⋆ Γ) rec = 0
    r (CtxTy (s ─⟨ A ⟩⟶ t) Γ) rec = rec (CtxTm s Γ) Ty1 ⊔ suc (rec (CtxTy A Γ) Ty2) ⊔ rec (CtxTm t Γ) Ty3
    r (CtxSub ⟨⟩ Γ) rec = rec (CtxTy _ Γ) Sub1
    r (CtxSub ⟨ σ , t ⟩ Γ) rec = (rec (CtxSub σ Γ) Sub2) ⊔ (rec (CtxTm t Γ) Sub3)

liftCtxSyntax : (x : CtxSyntax n) → (A : Ty n) → CtxSyntax (suc n)
liftCtxSyntax (CtxTm t Γ) A = CtxTm (liftTerm t) (Γ , A)
liftCtxSyntax (CtxTy B Γ) A = CtxTy (liftType B) (Γ , A)
liftCtxSyntax (CtxSub σ Γ) A = CtxSub (liftSub σ) (Γ , A)
