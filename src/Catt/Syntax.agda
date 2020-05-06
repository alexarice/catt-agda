{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin

private
  variable
    n m : ℕ

Ctx : ℕ → Set
data Ty : ℕ → Set
data Term : ℕ → Set
Substitution : ℕ → ℕ → Set

liftType : Ty n → Ty (suc n)
liftTerm : Term n → Term (suc n)
liftSub : Substitution m n → Substitution (suc m) n

Ctx n = Fin n → Ty n

helper : {A : Set} → (Fin n → A) → A → Fin (suc n) → A
helper {zero} f a zero = a
helper {suc n} f a zero = f zero
helper {suc n} f a (suc x) = helper (λ y → f (suc y)) a x

extendC : Ctx n → Ty n → Ctx (suc n)
extendC Γ A = helper (λ x → liftType (Γ x)) (liftType A)

data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (t : Term n) → (A : Ty n) → (u : Term n) → Ty n

Substitution n m = Fin m → Term n

extendS : Substitution m n → Term m → Substitution m (suc n)
extendS σ t = helper σ t

data Term where
  Var : (x : Fin n) → Term n
  Coh : (Γ : Ctx n) → (A : Ty n) → (σ : Substitution m n) → Term m
  Comp : (Γ : Ctx n) → (A : Ty n) → (t : Term n) → (u : Term n) → (σ : Substitution m n) → Term m

liftType ⋆ = ⋆
liftType (t ─⟨ A ⟩⟶ u) = (liftTerm t) ─⟨ (liftType A) ⟩⟶ (liftTerm u)

liftTerm (Var x) = Var (inject₁ x)
liftTerm (Coh Γ A σ) = Coh Γ A (liftSub σ)
liftTerm (Comp Γ A t u σ) = Comp Γ A t u (liftSub σ)

liftSub σ x = liftTerm (σ x)
