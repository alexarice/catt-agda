{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax.Base where

open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Fin.Patterns
open import Data.Bool.Base using (not) renaming (T to Truth)
open import Relation.Nullary

variable
  n n′ m m′ l l′ o d d′ d″ : ℕ

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

data Ctx : ℕ → Set
data Ty : ℕ → Set
data Tm : ℕ → Set
data Sub : (n m : ℕ) → (Ty m) → Set

variable
  S S′ T T′ U U′ : Tree n
  Γ Γ′ Δ Δ′ Υ Θ : Ctx n
  A A′ B C D : Ty n
  s s′ t t′ u : Tm n
  σ σ′ τ τ′ μ : Sub n m A

infixl 25 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx n) → (A : Ty n) → Ctx (suc n)

ctxLength : (Γ : Ctx n) → ℕ
ctxLength {n = n} Γ = n

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n
  _─⟨_⟩⟶_ : (s : Tm n) → (A : Ty n) → (t : Tm n) → Ty n

data Sub where
  ⟨⟩ : Sub 0 n A
  ⟨_,_⟩ : (σ : Sub n m A) → (t : Tm m) → Sub (suc n) m A

data Tm where
  Var : (i : (Fin n)) → Tm n
  Coh : (S : Tree n) → (A : Ty (suc n)) → (σ : Sub (suc n) m ⋆) → Tm m

pattern 0V {n} = Var {n} 0F
pattern 1V {n} = Var {n} 1F
pattern 2V {n} = Var {n} 2F
pattern 3V {n} = Var {n} 3F
pattern 4V {n} = Var {n} 4F
pattern 5V {n} = Var {n} 5F
pattern 6V {n} = Var {n} 6F
pattern 7V {n} = Var {n} 7F
pattern 8V {n} = Var {n} 8F
pattern 9V {n} = Var {n} 9F

ty-dim : Ty n → ℕ
ty-dim ⋆ = 0
ty-dim (s ─⟨ A ⟩⟶ t) = suc (ty-dim A)
