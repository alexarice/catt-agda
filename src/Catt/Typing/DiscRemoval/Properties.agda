open import Catt.Typing.Rule
import Catt.Typing.DiscRemoval as DR

module Catt.Typing.DiscRemoval.Properties (ops : Op)
                                          (rules : RuleSet)
                                          (tame : Tame ops rules)
                                          (disc-rem : DR.HasDiscRemoval ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame

open DR ops rules

disc-rem-stm : HasDiscRemoval-STm
disc-rem-stm S L Lty .get = begin
  Coh ⌊ S ⌋ (sty-to-type (disc-sty S)) (idSub ● label-to-sub (L ,, S⋆))
    ≈⟨ reflexive≈tm (Coh≃ (linear-tree-compat S)
                          (disc-sty-to-type S)
                          (trans≃s (id-left-unit _)
                                   (sym≃s (idSub≃-left-unit (sym≃c (linear-tree-compat S)) _)))) ⟩
  disc-term (tree-dim S) (idSub≃ (sym≃c (linear-tree-compat S)) ● (label-to-sub (L ,, S⋆)))
    ≈⟨ disc-rem (disc-term-Ty (tree-dim S) (apply-sub-sub-typing (idSub≃-Ty (sym≃c (linear-tree-compat S))) (label-to-sub-Ty Lty TySStar))) ⟩
  0V [ idSub≃ (sym≃c (linear-tree-compat S)) ● label-to-sub (L ,, S⋆) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm {s = 0V} {t = 0V} (Var≃ (≃c-preserve-length (sym≃c (linear-tree-compat S))) refl) (idSub≃-left-unit (sym≃c (linear-tree-compat S)) (label-to-sub (L ,, S⋆)))) ⟩
  0V [ label-to-sub (L ,, S⋆)]tm
    ≈˘⟨ reflexive≈tm (label-linear-0V (L ,, S⋆)) ⟩
  stm-to-term (L (is-linear-max-path S)) ∎
  where
    open Reasoning (tm-setoid-≈ _)

standard-stm-is-comp′ : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → standard-stm d S ≈[ ⌊ S ⌋ ]stm standard-coh′ d S
standard-stm-is-comp′ (suc zero) Sing = refl≈stm
standard-stm-is-comp′ (suc zero) (Join S (Join T₁ T₂)) = refl≈stm
standard-stm-is-comp′ (suc zero) (Join Sing Sing) = begin
  SExt (SPath PHere)
    ≈⟨ compute-≈ refl≈stm ⟩
  SPath (is-linear-max-path (Join Sing Sing))
    ≈˘⟨ disc-rem-stm (Join Sing Sing) SPath (id-label-Ty (Join Sing Sing)) ⟩
  disc-stm (Susp Sing) >>= id-label-wt (Susp Sing)
    ≈⟨ [ refl≈tm ] ⟩
  SExt (SCoh Sing S⋆ (SPath ,, S⋆)) ∎
  where
    open Reasoning stm-setoid-≈
standard-stm-is-comp′ (suc zero) (Join (Join S S₁) Sing) = refl≈stm
standard-stm-is-comp′ (suc (suc d)) Sing = refl≈stm
standard-stm-is-comp′ (suc (suc d)) (Join S Sing) = ≈SExt (standard-stm-is-comp′ (suc d) S)
standard-stm-is-comp′ (suc (suc d)) (Join S (Join S₁ S₂)) = refl≈stm

standard-stm-is-comp : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → standard-stm d S ≈[ ⌊ S ⌋ ]stm standard-coh d S
standard-stm-is-comp d S = begin
  standard-stm d S
    ≈⟨ standard-stm-is-comp′ d S ⟩
  standard-coh′ d S
    ≈⟨ reflexive≈stm (standard-coh′-compat d S) ⟩
  standard-coh d S ∎
  where
    open Reasoning stm-setoid-≈
