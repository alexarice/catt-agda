{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular where

open import Catt.Syntax
open import Data.Nat
open import Data.Empty
open import Catt.Tree
open import Data.Fin
open import Catt.Variables

tm-to-ty : (Γ : Ctx n) → (t : Tm n) → Ty n
tm-to-ty Γ (Var i) = Γ ‼ i
tm-to-ty Γ (Coh Δ A σ) = A [ σ ]ty

tm-height : Ctx n → Tm n → ℕ
tm-height Γ t = ty-dim (tm-to-ty Γ t)

-- get-right-base-tm : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → Tm n
-- get-right-base-tm {d = suc zero} A = ty-tgt A
-- get-right-base-tm {d = suc (suc d)} A = get-right-base-tm (ty-base A)

-- ty-base′ : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → Ty n (pred d)
-- ty-base′ (s ─⟨ A ⟩⟶ t) = A

-- tm-src : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-src t = ty-src (tm-to-ty t)

-- tm-tgt : Tm Γ (suc (suc (suc d))) → Tm Γ (suc (suc d))
-- tm-tgt t = ty-tgt (tm-to-ty t)
data BoundedTm : ℕ → Ctx n → Tm n → Set
data BoundedTy : ℕ → Ctx n → Ty n → Set
data BoundedSub : ℕ → Ctx n → Sub m n ⋆ → Set

data BoundedTm where
  VarBoundZ : BoundedTy d Γ A → BoundedTm d (Γ , A) 0V
  VarBoundS : ∀ i → BoundedTm d Γ (Var i) → BoundedTm d (Γ , A) (Var (suc i))
  CohBound : (S : Tree n) → BoundedTy d (tree-to-ctx S) A → BoundedSub d Γ σ → BoundedTm d Γ (Coh S A σ)

data BoundedTy where
  StarBound : BoundedTy d Γ ⋆
  ArrBound : BoundedTm d Γ s → BoundedTy d Γ A → BoundedTm d Γ t → BoundedTy (suc d) Γ (s ─⟨ A ⟩⟶ t)

data BoundedSub where
  NullBound : BoundedSub d Γ ⟨⟩
  ExtBound : BoundedSub d Γ σ → BoundedTm d Γ t → BoundedSub d Γ ⟨ σ , t ⟩
