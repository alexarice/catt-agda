{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Typing.BoundedEq.Properties.Suspension (index : ℕ)
                              (rule : Fin index → Rule)
                              (bound-rule : ∀ i a → P.BoundRule index rule {i} a)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Typing.BoundedEq index rule
open import Catt.Typing.BoundedEq.Properties index rule bound-rule
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Suspension
open import Data.Fin.Properties using (toℕ-injective)
open import Relation.Binary.PropositionalEquality
open import Catt.Globular
open import Catt.Globular.Properties
open P index rule

susp-ty-bdeq : B ≈⟨ d ⟩[ Γ ]ty C → (suspTy B) ≈⟨ suc d ⟩[ suspCtx Γ ]ty (suspTy C)
susp-tm-bdeq : s ≈⟨ d ⟩[ Γ ]tm t → (suspTm s) ≈⟨ suc d ⟩[ suspCtx Γ ]tm (suspTm t)
susp-sub-bdeq : σ ≈⟨ d ⟩[ Γ ]s τ → (suspSub σ) ≈⟨ suc d ⟩[ suspCtx Γ ]s (suspSub τ)

susp-ty-bdeq StarB≈ = refl≈tyb
susp-ty-bdeq (ArrB≈ p q r) = ArrB≈ (susp-tm-bdeq p) (susp-ty-bdeq q) (susp-tm-bdeq r)

susp-tm-bdeq (VarB≈ x) with toℕ-injective x
... | refl = refl≈tmb
susp-tm-bdeq (SymB≈ p) = sym≈tmb (susp-tm-bdeq p)
susp-tm-bdeq (TransB≈ p q) = trans≈tmb (susp-tm-bdeq p) (susp-tm-bdeq q)
susp-tm-bdeq (CohB≈ p q) = CohB≈ (susp-ty-bdeq p) (susp-sub-bdeq q)
susp-tm-bdeq (RuleB≈ i a tty b) = eq-to-bd-eq-tm (susp-rule i a (suspTmTy tty)) (BoundedSuspTm b)

susp-sub-bdeq (NullB≈ x) = refl≈sb
susp-sub-bdeq (ExtB≈ p x) = ExtB≈ (susp-sub-bdeq p) (susp-tm-bdeq x)
