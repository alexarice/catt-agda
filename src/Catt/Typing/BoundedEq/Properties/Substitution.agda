{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Typing.BoundedEq.Properties.Substitution (index : ℕ)
                              (rule : Fin index → Rule)
                              (bound-rule : ∀ i a → P.BoundRule index rule {i} a)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a)
                              where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Typing.BoundedEq index rule
open import Catt.Typing.BoundedEq.Properties index rule bound-rule
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Typing.Properties.Substitution index rule lift-rule susp-rule sub-rule
open import Catt.Typing.BoundedEq.Properties.Suspension index rule bound-rule lift-rule susp-rule
open import Catt.Suspension
open import Data.Fin.Properties using (toℕ-injective)
open import Relation.Binary.PropositionalEquality
open import Catt.Globular
open import Catt.Globular.Properties
open P index rule
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Data.Nat.Properties

apply-sub-ty-bdeq : Typing-Sub Γ Δ σ → A ≈⟨ d ⟩[ Γ ]ty B → A [ σ ]ty ≈⟨ sl σ + d ⟩[ Δ ]ty B [ σ ]ty
apply-sub-tm-bdeq : {σ : Sub n m A} → Typing-Sub Γ Δ σ → s ≈⟨ d ⟩[ Γ ]tm t → s [ σ ]tm ≈⟨ sl σ + d ⟩[ Δ ]tm t [ σ ]tm
apply-sub-sub-bdeq : Typing-Sub Γ Δ σ → τ ≈⟨ d ⟩[ Γ ]s μ → σ ∘ τ ≈⟨ sl σ + d ⟩[ Δ ]s σ ∘ μ

apply-sub-ty-bdeq σty StarB≈ = refl≈tyb
apply-sub-ty-bdeq σty (ArrB≈ p q r) = ArrB≈ (apply-sub-tm-bdeq σty p) (apply-sub-ty-bdeq σty q) (apply-sub-tm-bdeq σty r)

apply-sub-tm-bdeq σty (VarB≈ x) with toℕ-injective x
... | refl = refl≈tmb
apply-sub-tm-bdeq σty (SymB≈ p) = sym≈tmb (apply-sub-tm-bdeq σty p)
apply-sub-tm-bdeq σty (TransB≈ p q) = trans≈tmb (apply-sub-tm-bdeq σty p) (apply-sub-tm-bdeq σty q)
apply-sub-tm-bdeq {A = ⋆} σty (CohB≈ p q) = CohB≈ p (apply-sub-sub-bdeq σty q)
apply-sub-tm-bdeq {A = s ─⟨ A ⟩⟶ t} {d = d} σty (CohB≈ p q) = bd-eq-tm (+-suc (ty-dim A) d) (apply-sub-tm-bdeq (unrestrictTy σty) (CohB≈ (susp-ty-bdeq p) (susp-sub-bdeq q)))
apply-sub-tm-bdeq {A = ⋆} σty (RuleB≈ i a tty b) = eq-to-bd-eq-tm (sub-rule i a σty (apply-sub-tm-typing tty σty)) {!!}
apply-sub-tm-bdeq {A = s ─⟨ A ⟩⟶ t} {Δ = Δ} {d = d} {σ = σ} σty (RuleB≈ i a tty b) = begin
  lhs a [ σ ]tm
    ≈⟨ reflexive≈tmb (unrestrict-comp-tm (lhs a) σ) ⟩
  suspTm (lhs a) [ unrestrict σ ]tm
    ≈⟨ bd-eq-tm (+-suc (ty-dim A) d) (apply-sub-tm-bdeq (unrestrictTy σty) (susp-tm-bdeq (RuleB≈ i a tty b))) ⟩
  suspTm (rhs a) [ unrestrict σ ]tm
    ≈˘⟨ reflexive≈tmb (unrestrict-comp-tm (rhs a) σ) ⟩
  rhs a [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈b (suc (ty-dim A + d)) Δ)
    open Rule (rule i)

apply-sub-sub-bdeq σty (NullB≈ x) = NullB≈ (apply-sub-ty-bdeq σty x)
apply-sub-sub-bdeq σty (ExtB≈ p x) = ExtB≈ (apply-sub-sub-bdeq σty p) (apply-sub-tm-bdeq σty x)
