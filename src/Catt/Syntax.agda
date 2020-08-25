{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Catt.Fin
open import Data.Product renaming (_,_ to _,,_)

private
  variable
    n m l dim : ℕ

data Ctx : ℕ → Set
data Ty : ℕ → ℕ → Set
data Term : ℕ → Set
data Sub : ℕ → ℕ → Set

liftType : Ty n dim → Ty (suc n) dim
liftTerm : Term n → Term (suc n)
liftSub : Sub m n → Sub (suc m) n

infixl 45 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx n) → (A : Ty n dim) → Ctx (suc n)

infix 50 _‼_
_‼_ : Ctx n → Fin n → ∃ (Ty n)
(Γ , A) ‼ fromℕ n = -, liftType A
(Γ , A) ‼ inject i = -, liftType (proj₂ (Γ ‼ i))

last : Ctx (suc n) → ∃ (Ty (suc n))
last Γ = Γ ‼ fromℕ _

infix 50 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n 0
  _─⟨_⟩⟶_ : (t : Term n) → (A : Ty n dim) → (u : Term n) → Ty n (suc dim)

data Sub where
  ⟨⟩ : Sub m 0
  ⟨_,_⟩ : (σ : Sub m n) → (Term m) → Sub m (suc n)

data Term where
  Var : (x : Fin n) → Term n
  Coh : (Γ : Ctx n) → (A : Ty n (suc dim)) → (σ : Sub m n) → Term m

liftType ⋆ = ⋆
liftType (t ─⟨ A ⟩⟶ u) = (liftTerm t) ─⟨ (liftType A) ⟩⟶ (liftTerm u)

liftTerm (Var x) = Var (inject x)
liftTerm (Coh Γ A σ) = Coh Γ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n dim → Sub m n → Ty m dim
_[_]tm : Term n → Sub m n → Term m
infixl 31 _∘_
_∘_ : Sub m n → Sub l m → Sub l n

⋆ [ σ ]ty = ⋆
(t ─⟨ A ⟩⟶ u) [ σ ]ty = (t [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (u [ σ ]tm)

Var (fromℕ n) [ ⟨ σ , t ⟩ ]tm = t
Var (inject i) [ ⟨ σ , t ⟩ ]tm = Var i [ σ ]tm
Coh Γ A τ [ σ ]tm = Coh Γ A (τ ∘ σ)

⟨⟩ ∘ τ = ⟨⟩
⟨ σ , t ⟩ ∘ τ = ⟨ σ ∘ τ , t [ τ ]tm ⟩

ty-dim : Ty n dim → ℕ
ty-dim {dim = dim} _ = dim

ty-base : Ty n (suc dim) → Ty n dim
ty-base (t ─⟨ A ⟩⟶ u) = A

ty-base-n : ∀ x → Ty n (x + dim) → Ty n dim
ty-base-n zero A = A
ty-base-n (suc x) A = ty-base-n x (ty-base A)

ty-base-≤ : ∀ {d₁ d₂} → d₁ ≤′ d₂ → Ty n d₂ → Ty n d₁
ty-base-≤ ≤′-refl A = A
ty-base-≤ (≤′-step p) A = ty-base-≤ p (ty-base A)

liftTypeN : ∀ m {n dim} → Ty n dim → Ty (m + n) dim
liftTypeN zero A = A
liftTypeN (suc m) A = liftType (liftTypeN m A)

TermAndType : ℕ → ℕ → Set
TermAndType n dim = Term n × Ty n dim

TermAndTypeSrc : ∀ {n dim-1} → TermAndType n (suc dim-1) → TermAndType n dim-1
TermAndTypeSrc (_ ,, t ─⟨ A ⟩⟶ _) = t ,, A

TermAndTypeTgt : ∀ {n dim-1} → TermAndType n (suc dim-1) → TermAndType n dim-1
TermAndTypeTgt (_ ,, _ ─⟨ A ⟩⟶ u) = u ,, A
