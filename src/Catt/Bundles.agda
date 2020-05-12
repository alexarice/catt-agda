{-# OPTIONS --without-K --safe #-}

module Catt.Bundles where

open import Catt.Syntax
open import Catt.Typing
open import Data.Nat

record TypedCtx : Set where
  field
    {size} : ℕ
    {ctx} : Ctx size
    typing-ctx : ctx ⊢

open TypedCtx public

record TypedSub (Γ Δ : TypedCtx) : Set where
  field
    {sub} : Sub (size Δ) (size Γ)
    typing-sub : (ctx Δ) ⊢ sub :: (ctx Γ)

open TypedSub public

record TypedTy (Γ : TypedCtx) : Set where
  field
    {ty} : Ty (size Γ)
    typing-ty : (ctx Γ) ⊢ ty

open TypedTy public

record TypedTerm {Γ : TypedCtx} (A : TypedTy Γ) : Set where
  field
    {term} : Term (size Γ)
    typing-term : (ctx Γ) ⊢ term ∷ (ty A)

open TypedTerm public
