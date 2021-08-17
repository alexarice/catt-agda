{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Fin.Patterns
open import Relation.Nullary
open import Data.Empty
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

variable
  n n′ m m′ d d′ : ℕ

data Ctx : ℕ → Set
data Ty : ℕ → Set
data Tm : ℕ → Set
data Sub : ℕ → ℕ → Set

variable
  Γ Γ′ Δ Δ′ Υ : Ctx n
  A A′ B C : Ty n
  s s′ t t′ u : Tm n
  σ σ′ τ μ : Sub n m

infixl 25 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx m) → (A : Ty m) → Ctx (suc m)

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (s : Tm n) → (A : Ty n) → (t : Tm n) → Ty n

data Sub where
  ⟨⟩ : Sub 0 m
  ⟨_,_⟩ : (σ : Sub n m) → (t : Tm m) → Sub (suc n) m


data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + suc (suc n))

data Tm where
  Var : (i : (Fin n)) → Tm n
  Coh : (T : Tree n) → (A : Ty (suc n)) → (σ : Sub (suc n) m) → Tm m

pattern 0V = Var 0F
pattern 1V = Var 1F
pattern 2V = Var 2F
pattern 3V = Var 3F
pattern 4V = Var 4F
pattern 5V = Var 5F
pattern 6V = Var 5F
pattern 7V = Var 6F
pattern 8V = Var 7F
pattern 9V = Var 8F

ctxLength : Ctx n → ℕ
ctxLength {n} Γ = n

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub n m → Ty m
_[_]tm : Tm n → Sub n m → Tm m

infixl 31 _∘_
_∘_ : Sub n m → Sub n′ n → Sub n′ m

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A τ [ σ ]tm = Coh Δ A (σ ∘ τ)

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

liftTerm : Tm n → Tm (suc n)
liftSub : Sub n m → Sub n (suc m)
liftType : Ty n → Ty (suc n)

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

idSub : (n : ℕ) → Sub n n
idSub zero = ⟨⟩
idSub (suc n) = ⟨ liftSub (idSub n) , 0V ⟩

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)
