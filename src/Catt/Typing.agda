{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Typing where

open import Catt.Syntax
open import Catt.Pasting
open import Data.Nat

data _⊢ : Ctx → Set
data _⊢_ : Ctx → Ty → Set
data _⊢_∶_ : Ctx → Term → Ty → Set
data _⊢_∷_ : Ctx → Sub → Ctx → Set

data _⊢ where
  CtxBase : ∅ ⊢
  CtxStep : Γ ⊢ A → Γ , A ⊢

data _⊢_ where
  TyStar : Γ ⊢ → Γ ⊢ ⋆
  TyArr : Γ ⊢ s ∶ A → Γ ⊢ t ∶ A → Γ ⊢ (s ─⟨ A ⟩⟶ t)
