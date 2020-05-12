{-# OPTIONS --without-K --safe #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin

private
  variable
    n m : ℕ

data Ctx : ℕ → Set
data Ty : ℕ → Set
data Term : ℕ → Set
data Sub : ℕ → ℕ → Set

liftType : Ty n → Ty (suc n)
liftTerm : Term n → Term (suc n)
liftSub : Sub m n → Sub (suc m) n

infixl 40 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : Ctx n → Ty n → Ctx (suc n)

infix 50 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (t : Term n) → (A : Ty n) → (u : Term n) → Ty n

data Sub where
  ⟨⟩ : Sub n 0
  ⟨_,_⟩ : Sub n m → Term n → Sub n (suc m)

data Term where
  Var : (x : Fin n) → Term n
  Coh : (Γ : Ctx n) → (A : Ty n) → (σ : Sub m n) → Term m
  Comp : (Γ : Ctx n) → (A : Ty n) → (t : Term n) → (u : Term n) → (σ : Sub m n) → Term m

liftType ⋆ = ⋆
liftType (t ─⟨ A ⟩⟶ u) = (liftTerm t) ─⟨ (liftType A) ⟩⟶ (liftTerm u)

liftTerm (Var x) = Var (suc x)
liftTerm (Coh Γ A σ) = Coh Γ A (liftSub σ)
liftTerm (Comp Γ A t u σ) = Comp Γ A t u (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , x ⟩ = ⟨ liftSub σ , liftTerm x ⟩

ctx-get : Ctx n → Fin n → Ty n
ctx-get (Γ , A) zero = liftType A
ctx-get (Γ , A) (suc n) = liftType (ctx-get Γ n)

sub-get : Sub n m → Fin m → Term n
sub-get ⟨ σ , x ⟩ zero = x
sub-get ⟨ σ , x ⟩ (suc m) = sub-get σ m
