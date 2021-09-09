{-# OPTIONS --without-K --safe --exact-split #-}

open import Catt.Typing.Base
open import Data.Nat
open import Data.Fin using (Fin)

module Catt.Typing.Induction (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Typing index rule

data SyntaxTy : Set where
  Context : (Γ : Ctx m) → Typing-Ctx Γ → SyntaxTy
  Type : (Γ : Ctx n) → (A : Ty n d) → Typing-Ty Γ A → SyntaxTy
  Term : (Γ : Ctx n) → (A : Ty n d) → (t : Tm n) → Typing-Tm Γ t A → SyntaxTy
  Substitution : (Γ : Ctx n) → (Δ : Ctx m) → (σ : Sub n m) → Typing-Sub Γ Δ σ → SyntaxTy
