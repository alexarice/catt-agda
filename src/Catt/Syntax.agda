{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty



data Ctx : Set
data Ty : Ctx → ℕ → Set
data Term : Ctx → ℕ → Set
data Sub : Ctx → Ctx → Set


private
  variable
    n m l dim : ℕ
    Γ Δ Υ : Ctx


ty-dim : Ty Γ dim → ℕ
ty-dim {dim = dim} ty = dim

length : Ctx → ℕ



infixl 45 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ dim) → Ctx

length ∅ = 0
length (Γ , A) = suc (length Γ)

infix 50 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ 0
  _─⟨_⟩⟶_ : (s : Term Γ dim) → (A : Ty Γ dim) → (t : Term Γ dim) → Ty Γ (suc dim)

data Sub where
  ⟨⟩ : Sub Γ ∅
  ⟨_,_⟩ : (σ : Sub Γ Δ) → (Term Γ dim) → {A : Ty Δ dim} → Sub Γ (Δ , A)

retrieveDim : (Γ : Ctx) → Fin (length Γ) → ℕ
retrieveDim (_,_ {dim = dim} _ _) zero = dim
retrieveDim (Γ , A) (suc i) = retrieveDim Γ i

data Term where
  Var : (i : Fin (length Γ)) → Term Γ (retrieveDim Γ i)
  Coh : (Δ : Ctx) → (A : Ty Δ dim) → (σ : Sub Γ Δ) → Term Γ dim

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty Δ dim → Sub Γ Δ → Ty Γ dim
_[_]tm : Term Δ dim → Sub Γ Δ → Term Γ dim
infixl 31 _∘_
_∘_ : Sub Δ Γ → Sub Υ Δ → Sub Υ Γ

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc i) [ ⟨ σ , t ⟩ ]tm = Var i [ σ ]tm
Coh Γ A τ [ σ ]tm = Coh Γ A (τ ∘ σ)

⟨⟩ ∘ τ = ⟨⟩
⟨ σ , t ⟩ ∘ τ = ⟨ σ ∘ τ , t [ τ ]tm ⟩

liftType : Ty Γ dim → {A : Ty Γ n} → Ty (Γ , A) dim
liftTerm : Term Γ dim → {A : Ty Γ n} → Term (Γ , A) dim
liftSub : Sub Γ Δ → {A : Ty Γ n} → Sub (Γ , A) Δ

liftType ⋆ = ⋆
liftType (s ─⟨ B ⟩⟶ t) = (liftTerm s) ─⟨ (liftType B) ⟩⟶ (liftTerm t)

liftTerm (Var x) = Var (suc x)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , x ⟩ = ⟨ (liftSub σ) , (liftTerm x) ⟩

idSub : Sub Γ Γ
idSub {∅} = ⟨⟩
idSub {Γ , A} = ⟨ liftSub idSub , Var zero ⟩

infix 45 _‼_
_‼_ : (Γ : Ctx) → (i : Fin (length Γ)) → Ty Γ (retrieveDim Γ i)
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)

-- ty-base : Ty n (suc dim) → Ty n dim
-- ty-base (t ─⟨ A ⟩⟶ u) = A

-- ty-base-n : ∀ x → Ty n (x + dim) → Ty n dim
-- ty-base-n zero A = A
-- ty-base-n (suc x) A = ty-base-n x (ty-base A)

-- ty-base-≤ : ∀ {d₁ d₂} → d₁ ≤′ d₂ → Ty n d₂ → Ty n d₁
-- ty-base-≤ ≤′-refl A = A
-- ty-base-≤ (≤′-step p) A = ty-base-≤ p (ty-base A)

-- liftTypeN : ∀ m {n dim} → Ty n dim → Ty (m + n) dim
-- liftTypeN zero A = A
-- liftTypeN (suc m) A = liftType (liftTypeN m A)

-- TermAndType : ℕ → ℕ → Set
-- TermAndType n dim = Term n × Ty n dim

-- TermAndTypeSrc : ∀ {n dim-1} → TermAndType n (suc dim-1) → TermAndType n dim-1
-- TermAndTypeSrc (_ ,, t ─⟨ A ⟩⟶ _) = t ,, A

-- TermAndTypeTgt : ∀ {n dim-1} → TermAndType n (suc dim-1) → TermAndType n dim-1
-- TermAndTypeTgt (_ ,, _ ─⟨ A ⟩⟶ u) = u ,, A
