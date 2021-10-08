{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.BoundedEq.Properties.Lifting (index : ℕ)
                                      (rule : Fin index → Rule)
                                      (dim-rule : ∀ i a → P.DimRule index rule {i} a)
                                      (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Typing.BoundedEq index rule
open import Catt.Typing.BoundedEq.Properties index rule dim-rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open P index rule
open import Relation.Binary.PropositionalEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Globular.Typing index rule lift-rule
open import Data.Nat.Properties

lift-ty-bdeq : B ≈⟨ d ⟩[ Γ ]ty C → (liftType B) ≈⟨ d ⟩[ Γ , A ]ty (liftType C)
lift-tm-bdeq : s ≈⟨ d ⟩[ Γ ]tm t → (liftTerm s) ≈⟨ d ⟩[ Γ , A ]tm (liftTerm t)
lift-sub-bdeq : σ ≈⟨ d ⟩[ Γ ]s τ → (liftSub σ) ≈⟨ d ⟩[ Γ , A ]s (liftSub τ)

lift-ty-bdeq StarB≈ = StarB≈
lift-ty-bdeq (ArrB≈ q r s) = ArrB≈ (lift-tm-bdeq q) (lift-ty-bdeq r) (lift-tm-bdeq s)

lift-tm-bdeq (VarB≈ x) = VarB≈ (cong suc x)
lift-tm-bdeq (SymB≈ eq) = SymB≈ (lift-tm-bdeq eq)
lift-tm-bdeq (TransB≈ eq eq′) = TransB≈ (lift-tm-bdeq eq) (lift-tm-bdeq eq′)

lift-tm-bdeq (CohB≈ r s) = CohB≈ r (lift-sub-bdeq s)
lift-tm-bdeq {A = A} (RuleB≈ i a tc p) = eq-to-bd-eq-tm (lift-rule i a (lift-tm-typing tc)) {!!} -- lift-rule i a (lift-tm-typing tc)

lift-sub-bdeq (NullB≈ x) = NullB≈ (lift-ty-bdeq x)
lift-sub-bdeq (ExtB≈ eq x) = ExtB≈ (lift-sub-bdeq eq) (lift-tm-bdeq x)
