import Catt.Typing.Rule as R
import Catt.Typing.DiscRemoval as DR

module Catt.Typing.DiscRemoval.Properties {index : Set}
                                          (rule : index → R.Rule)
                                          (lift-rule : ∀ i → R.LiftRule rule (rule i))
                                          (susp-rule : ∀ i → R.SuspRule rule (rule i))
                                          (sub-rule : ∀ i → R.SubRule rule (rule i))
                                          (disc-rem : DR.HasDiscRemoval rule) where

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
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Discs.Typing rule lift-rule
open import Catt.Tree.Structured.Typing rule
open import Catt.Tree.Structured.Typing.Properties rule lift-rule susp-rule sub-rule

open DR rule
open R rule

disc-rem-stm : HasDiscRemoval-STm
disc-rem-stm S L Lty .get = begin
  Coh (tree-to-ctx S) (sty-to-type (disc-sty S)) (label-to-sub (L ,, S⋆) ● idSub)
    ≈⟨ reflexive≈tm (Coh≃ (linear-tree-compat S)
                          (disc-sty-to-type S)
                          (trans≃s (id-right-unit _)
                                   (sym≃s (idSub≃-right-unit (sym≃c (linear-tree-compat S)) _)))) ⟩
  disc-term (tree-dim S) ((label-to-sub (L ,, S⋆)) ● idSub≃ (sym≃c (linear-tree-compat S)))
    ≈⟨ disc-rem (disc-term-Ty (tree-dim S) (apply-sub-sub-typing (idSub≃-Ty (sym≃c (linear-tree-compat S))) (label-to-sub-Ty Lty TySStar))) ⟩
  0V [ label-to-sub (L ,, S⋆) ● idSub≃ (sym≃c (linear-tree-compat S)) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm {s = 0V} {t = 0V} (Var≃ (≃c-preserve-length (sym≃c (linear-tree-compat S))) refl) (idSub≃-right-unit (sym≃c (linear-tree-compat S)) (label-to-sub (L ,, S⋆)))) ⟩
  0V [ label-to-sub (L ,, S⋆)]tm
    ≈˘⟨ reflexive≈tm (label-linear-0V (L ,, S⋆)) ⟩
  stm-to-term (L (is-linear-max-path S)) ∎
  where
    open Reasoning (tm-setoid-≈ _)

canonical-stm-is-comp′ : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → canonical-stm d S ≈[ tree-to-ctx S ]stm canonical-comp′ d S
canonical-stm-is-comp′ (suc zero) Sing = refl≈stm
canonical-stm-is-comp′ (suc zero) (Join S (Join T₁ T₂)) = refl≈stm
canonical-stm-is-comp′ (suc zero) (Join Sing Sing) = begin
  SExt (SPath PHere)
    ≈⟨ compute-≈ refl≈stm ⟩
  SPath (is-linear-max-path (Join Sing Sing))
    ≈˘⟨ disc-rem-stm (Join Sing Sing) SPath (id-label-Ty (Join Sing Sing)) ⟩
  disc-stm (susp Sing) >>= id-label-wt (susp Sing)
    ≈⟨ [ refl≈tm ] ⟩
  SExt (SCoh Sing S⋆ (SPath ,, S⋆)) ∎
  where
    open Reasoning stm-setoid-≈
canonical-stm-is-comp′ (suc zero) (Join (Join S S₁) Sing) = refl≈stm
canonical-stm-is-comp′ (suc (suc d)) Sing = refl≈stm
canonical-stm-is-comp′ (suc (suc d)) (Join S Sing) = ≈SExt (canonical-stm-is-comp′ (suc d) S)
canonical-stm-is-comp′ (suc (suc d)) (Join S (Join S₁ S₂)) = refl≈stm

canonical-stm-is-comp : (d : ℕ) → .⦃ NonZero d ⦄ → (S : Tree n) → canonical-stm d S ≈[ tree-to-ctx S ]stm canonical-comp d S
canonical-stm-is-comp d S = begin
  canonical-stm d S
    ≈⟨ canonical-stm-is-comp′ d S ⟩
  canonical-comp′ d S
    ≈⟨ reflexive≈stm (canonical-comp′-compat d S) ⟩
  canonical-comp d S ∎
  where
    open Reasoning stm-setoid-≈

conv-rule : ⦃ NonZero n ⦄
          → {σ : Sub (disc-size n) m ⋆}
          → ConvRule (DiscRemoval Γ σ)
conv-rule {n = n} {σ = ⟨ σ , s ⟩} tty with coh-sub-ty tty
... | TyExt σty sty = TyConv sty (Ty-unique (disc-term-Ty n (TyExt σty sty)) tty)
