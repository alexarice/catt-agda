open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
import Catt.Typing.DiscRemoval as DR

module Catt.Typing.DiscRemoval.Properties (index : ℕ)
                                          (rule : Fin index → Rule)
                                          (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                          (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                          (sub-rule : ∀ i a → P.SubRule index rule {i} a)
                                          (disc-rem : DR.HasDiscRemoval index rule) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Typing index rule
open import Catt.Tree.Label.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path
open import Catt.Typing.Properties.Base index rule

unbiased-stm-is-comp : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → unbiased-stm d S ≈[ incTree S ]stm unbiased-comp′ d S
unbiased-stm-is-comp (suc zero) Sing = refl≈stm
unbiased-stm-is-comp (suc zero) (Join S (Join T₁ T₂)) = refl≈stm
unbiased-stm-is-comp (suc zero) (Join Sing Sing) = begin
  SExt (SPath PHere)
    ≈⟨ compute-≈ refl≈stm ⟩
  SPath (is-linear-max-path (Join Sing Sing))
    ≈˘⟨ disc-rem (Join Sing Sing) SPath (id-label-Ty (Join Sing Sing)) ⟩
  unbiased-comp 1 (Join Sing Sing)
    ≈⟨ [ refl≈tm ] ⟩
  SExt (SCoh Sing S⋆ (SPath ,, S⋆)) ∎
  where
    open Reasoning (stm-setoid-≈ (incTree (Join Sing Sing)))
unbiased-stm-is-comp (suc zero) (Join (Join S S₁) Sing) = refl≈stm
unbiased-stm-is-comp (suc (suc d)) Sing = refl≈stm
unbiased-stm-is-comp (suc (suc d)) (Join S Sing) = ≈SExt (unbiased-stm-is-comp (suc d) S)
unbiased-stm-is-comp (suc (suc d)) (Join S (Join S₁ S₂)) = refl≈stm
