open import Catt.Typing.Rule
import Catt.Typing.DiscRemoval as DR

module Catt.Typing.DiscRemoval.Properties {index : Set}
                                          (rule : index → Rule)
                                          (lift-rule : ∀ i → LiftRule rule (rule i))
                                          (susp-rule : ∀ i → SuspRule rule (rule i))
                                          (sub-rule : ∀ i → SubRule rule (rule i))
                                          (disc-rem : DR.HasDiscRemoval rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Discs
open import Catt.Discs.Properties

disc-rem-stm : DR.HasDiscRemoval-STm rule
disc-rem-stm S L Lty .get = begin
  stm-to-term (unbiased-comp (tree-dim S) S >>= L ,, S⋆)
    ≈⟨ reflexive≈tm (Coh≃ (linear-tree-compat S) (unbiased-type-linear (tree-dim S) S refl) (trans≃s (id-right-unit (label-to-sub (L ,, S⋆))) (sym≃s (idSub≃-right-unit (sym≃c (linear-tree-compat S)) (label-to-sub (L ,, S⋆)))))) ⟩
  disc-term (tree-dim S) (label-to-sub (L ,, S⋆) ● idSub≃ (sym≃c (linear-tree-compat S)))
    ≈⟨ disc-rem (apply-sub-sub-typing (idSub≃-Ty (sym≃c (linear-tree-compat S))) (label-to-sub-Ty Lty TySStar)) ⟩
  0V [ label-to-sub (L ,, S⋆) ● idSub≃ (sym≃c (linear-tree-compat S)) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm {s = 0V} {t = 0V} (Var≃ (≃c-preserve-length (sym≃c (linear-tree-compat S))) refl) (idSub≃-right-unit (sym≃c (linear-tree-compat S)) (label-to-sub (L ,, S⋆)))) ⟩
  0V [ label-to-sub (L ,, S⋆)]tm
    ≈˘⟨ reflexive≈tm (label-linear-0V (L ,, S⋆)) ⟩
  stm-to-term (L (is-linear-max-path S)) ∎
  where
    open Reasoning (tm-setoid-≈ _)

unbiased-stm-is-comp′ : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → unbiased-stm d S ≈[ tree-to-ctx S ]stm unbiased-comp′ d S
unbiased-stm-is-comp′ (suc zero) Sing = refl≈stm
unbiased-stm-is-comp′ (suc zero) (Join S (Join T₁ T₂)) = refl≈stm
unbiased-stm-is-comp′ (suc zero) (Join Sing Sing) = begin
  SExt (SPath PHere)
    ≈⟨ compute-≈ refl≈stm ⟩
  SPath (is-linear-max-path (Join Sing Sing))
    ≈˘⟨ disc-rem-stm (Join Sing Sing) SPath (id-label-Ty (Join Sing Sing)) ⟩
  unbiased-comp 1 (Join Sing Sing)
    ≈⟨ [ refl≈tm ] ⟩
  SExt (SCoh Sing S⋆ (SPath ,, S⋆)) ∎
  where
    open Reasoning stm-setoid-≈
unbiased-stm-is-comp′ (suc zero) (Join (Join S S₁) Sing) = refl≈stm
unbiased-stm-is-comp′ (suc (suc d)) Sing = refl≈stm
unbiased-stm-is-comp′ (suc (suc d)) (Join S Sing) = ≈SExt (unbiased-stm-is-comp′ (suc d) S)
unbiased-stm-is-comp′ (suc (suc d)) (Join S (Join S₁ S₂)) = refl≈stm

unbiased-stm-is-comp : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → unbiased-stm d S ≈[ tree-to-ctx S ]stm unbiased-comp d S
unbiased-stm-is-comp d S = begin
  unbiased-stm d S
    ≈⟨ unbiased-stm-is-comp′ d S ⟩
  unbiased-comp′ d S
    ≈⟨ reflexive≈stm (unbiased-comp′-compat d S) ⟩
  unbiased-comp d S ∎
  where
    open Reasoning stm-setoid-≈
