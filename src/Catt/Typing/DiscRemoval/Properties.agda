open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
import Catt.Typing.DiscRemoval as DR

module Catt.Typing.DiscRemoval.Properties {index : Set}
                                          (rule : index → Rule)
                                          (lift-rule : ∀ i → P.LiftRule rule i)
                                          (susp-rule : ∀ i → P.SuspRule rule i)
                                          (sub-rule : ∀ i → P.SubRule rule i)
                                          (disc-rem : DR.HasDiscRemoval rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Typing.Properties.Base rule

unbiased-stm-is-comp′ : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → unbiased-stm d S ≈[ incTree S ]stm unbiased-comp′ d S
unbiased-stm-is-comp′ (suc zero) Sing = refl≈stm
unbiased-stm-is-comp′ (suc zero) (Join S (Join T₁ T₂)) = refl≈stm
unbiased-stm-is-comp′ (suc zero) (Join Sing Sing) = begin
  SExt (SPath PHere)
    ≈⟨ compute-≈ refl≈stm ⟩
  SPath (is-linear-max-path (Join Sing Sing))
    ≈˘⟨ disc-rem (Join Sing Sing) SPath (id-label-Ty (Join Sing Sing)) ⟩
  unbiased-comp 1 (Join Sing Sing)
    ≈⟨ [ refl≈tm ] ⟩
  SExt (SCoh Sing S⋆ (SPath ,, S⋆)) ∎
  where
    open Reasoning (stm-setoid-≈ (incTree (Join Sing Sing)))
unbiased-stm-is-comp′ (suc zero) (Join (Join S S₁) Sing) = refl≈stm
unbiased-stm-is-comp′ (suc (suc d)) Sing = refl≈stm
unbiased-stm-is-comp′ (suc (suc d)) (Join S Sing) = ≈SExt (unbiased-stm-is-comp′ (suc d) S)
unbiased-stm-is-comp′ (suc (suc d)) (Join S (Join S₁ S₂)) = refl≈stm

unbiased-stm-is-comp : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → unbiased-stm d S ≈[ incTree S ]stm unbiased-comp d S
unbiased-stm-is-comp d S = begin
  unbiased-stm d S
    ≈⟨ unbiased-stm-is-comp′ d S ⟩
  unbiased-comp′ d S
    ≈⟨ reflexive≈stm (unbiased-comp′-compat d S) ⟩
  unbiased-comp d S ∎
  where
    open Reasoning (stm-setoid-≈ (incTree S))
