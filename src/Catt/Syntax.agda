{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Product
open import Catt.Fin
open import Catt.Vec.Functional
private
  variable
    n m l : ℕ

Ctx : ℕ → Set
data Ty : ℕ → Set
data Term : ℕ → Set
Sub : ℕ → ℕ → Set

liftType : Ty n → Ty (suc n)
liftTerm : Term n → Term (suc n)
liftSub : Sub m n → Sub (suc m) n

Ctx n = VectorD Ty n

infix 50 _‼_
_‼_ : Ctx n → Fin n → Ty n
Γ ‼ fromℕ n = liftType (get Γ (fromℕ n))
Γ ‼ inject x = liftType (front Γ ‼ x)

infix 50 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (t : Term n) → (A : Ty n) → (u : Term n) → Ty n

Sub m n = Vector (Term m) n

data Term where
  Var : (x : Fin n) → Term n
  Coh : (Γ : Ctx n) → (A : Ty n) → (σ : Sub m n) → Term m

liftType ⋆ = ⋆
liftType (t ─⟨ A ⟩⟶ u) = (liftTerm t) ─⟨ (liftType A) ⟩⟶ (liftTerm u)

liftTerm (Var x) = Var (inject x)
liftTerm (Coh Γ A σ) = Coh Γ A (liftSub σ)

liftSub σ .get f = liftTerm (get σ f)
