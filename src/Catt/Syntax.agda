{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Catt.Fin

private
  variable
    n m l : ℕ

data Ctx : ℕ → Set
data Ty : ℕ → Set
data Term : ℕ → Set
data Sub : ℕ → ℕ → Set

liftType : Ty n → Ty (suc n)
liftTerm : Term n → Term (suc n)
liftSub : Sub m n → Sub (suc m) n

infixl 45 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx n) → (A : Ty n) → Ctx (suc n)

infix 50 _‼_
_‼_ : Ctx n → Fin n → Ty n
(Γ , A) ‼ fromℕ n = liftType A
(Γ , A) ‼ inject i = liftType (Γ ‼ i)

infix 50 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (t : Term n) → (A : Ty n) → (u : Term n) → Ty n

data Sub where
  ⟨⟩ : Sub m 0
  ⟨_,_⟩ : (σ : Sub m n) → (Term m) → Sub m (suc n)

data Term where
  Var : (x : Fin n) → Term n
  Coh : (Γ : Ctx n) → (A : Ty n) → (σ : Sub m n) → Term m

liftType ⋆ = ⋆
liftType (t ─⟨ A ⟩⟶ u) = (liftTerm t) ─⟨ (liftType A) ⟩⟶ (liftTerm u)

liftTerm (Var x) = Var (inject x)
liftTerm (Coh Γ A σ) = Coh Γ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub m n → Ty m
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
