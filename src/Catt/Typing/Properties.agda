{-# OPTIONS --safe --without-K #-}

module Catt.Typing.Properties where

open import Catt.Syntax
open import Catt.Typing
open import Data.Nat
open import Data.Fin

private
  variable
    n m : ℕ
    Γ Δ : Ctx n
    t u : Term n
    A B : Ty n

liftingTermLemma : Γ ⊢ t ∷ A → Γ ⊢ B → Γ , B ⊢ liftTerm t ∷ liftType A
liftingTermLemma (TypeTermVar x ctx) p = TypeTermVar (suc x) (TypeCtxStep p)
liftingTermLemma (TypeTermCoh ty sub fv) p = {!!}
liftingTermLemma (TypeTermComp x b b₁ x₁ x₂) p = {!!}

liftingTypeLemma : Γ ⊢ A → Γ ⊢ B → Γ , B ⊢ liftType A
liftingTypeLemma (TypeTyStar x) p = TypeTyStar (TypeCtxStep p)
liftingTypeLemma (TypeTyArr x x₁) p = {!!}

termCheck⇒typeCheck : Γ ⊢ t ∷ A → Γ ⊢ A
termCheck⇒typeCheck {Γ = Γ , x} (TypeTermVar zero (TypeCtxStep p)) = {!!}
termCheck⇒typeCheck {Γ = Γ , x} (TypeTermVar (suc y) p) = {!!}
termCheck⇒typeCheck (TypeTermCoh x x₁ x₂) = {!!}
termCheck⇒typeCheck (TypeTermComp x p p₁ x₁ x₂) = {!!}
