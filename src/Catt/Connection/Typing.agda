{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Connection.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Connection
open import Catt.Connection.Properties
open import Relation.Binary.PropositionalEquality

connect-Ty : {Γ : Ctx (suc n)} → Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → {Δ : Ctx (suc m)} → Typing-Ctx Δ → Typing-Ctx (connect Γ t Δ)
connect-inc-right-Ty : {Γ : Ctx (suc n)} → Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → {Δ : Ctx (suc m)} → Typing-Ctx Δ → Typing-Sub Δ (connect Γ t Δ) (connect-inc-right t m)

connect-Ty Γty tty (TyAdd TyEmp x) = Γty
connect-Ty Γty tty (TyAdd (TyAdd Δty y) x) = TyAdd (connect-Ty Γty tty (TyAdd Δty y)) {!!}

connect-inc-right-Ty Γty tty (TyAdd {A = A} TyEmp x) with ≃ty-preserve-height (⋆-is-only-ty-in-empty-context A)
... | refl with A
... | ⋆ = TyExt TyNull TyStar tty
connect-inc-right-Ty Γty tty (TyAdd (TyAdd Δty y) x) = TyExt (lift-sub-typing (connect-inc-right-Ty Γty tty (TyAdd Δty y))) x (TyVar zero (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ (connect-inc-right _ _)))))
