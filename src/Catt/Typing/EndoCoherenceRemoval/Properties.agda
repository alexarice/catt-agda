open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
import Catt.Typing.EndoCoherenceRemoval as ECR

module Catt.Typing.EndoCoherenceRemoval.Properties {index : Set}
                                                   (rule : index → Rule)
                                                   (lift-rule : ∀ i → P.LiftRule rule (rule i))
                                                   (susp-rule : ∀ i → P.SuspRule rule (rule i))
                                                   (sub-rule : ∀ i → P.SubRule rule (rule i))
                                                   (ecr : ECR.HasEndoCoherenceRemoval rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Unbiased.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Path
open import Catt.Typing.Properties.Base rule
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Pasting
open import Catt.Typing.EndoCoherenceRemoval rule
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Globular
open import Catt.Globular.Properties

ecr-stm : HasEndoCoherenceRemoval-STm
ecr-stm S s As L [ sty ] [ Asty ] Lty .get = begin
  Coh (tree-to-ctx S) (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s)
      (label-to-sub (L ,, S⋆) ● idSub)
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (id-right-unit (label-to-sub (L ,, S⋆)))) ⟩
  Coh (tree-to-ctx S) (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s)
      (label-to-sub (L ,, S⋆))
    ≈⟨ ecr ⦃ tree-to-pd S ⦄ Asty sty (label-to-sub-Ty Lty TySStar) ⟩
  identity (ty-dim (sty-to-type As))
    (sub-from-disc (ty-dim (sty-to-type As))
     (sty-to-type As [ label-to-sub (L ,, S⋆) ]ty) _
     (stm-to-term s [ label-to-sub (L ,, S⋆) ]tm))
    ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-sub (ty-dim (sty-to-type As)) (sty-to-type As) refl (stm-to-term s) (label-to-sub (L ,, S⋆)))) ⟩
  identity (ty-dim (sty-to-type As))
         (sub-from-disc (ty-dim (sty-to-type As)) (sty-to-type As) _ (stm-to-term s))
         [ label-to-sub (L ,, S⋆) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (identity-≃ (sty-to-type-dim As) lem) (refl≃s {σ = label-to-sub (L ,, S⋆)})) ⟩
  identity (sty-dim As)
    (label-to-sub
     (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆))
    [ label-to-sub (L ,, S⋆) ]tm
    ≈˘⟨ reflexive≈tm (sub-action-≃-tm (identity-≃ (refl {x = sty-dim As}) (id-right-unit (label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)))) (refl≃s {σ = label-to-sub (L ,, S⋆)})) ⟩
  identity (sty-dim As) idSub [
     label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) ]tm
    [ label-to-sub (L ,, S⋆) ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm (label-to-sub (L ,, S⋆)) (label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)) (identity (sty-dim As) idSub)) ⟩
  identity (sty-dim As) idSub [ label-to-sub (L ,, S⋆) ● label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (sym≃tm (identity-stm-to-term (sty-dim As))) (label-comp-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) (L ,, S⋆))) ⟩
  stm-to-term (identity-stm (sty-dim As)) [
    label-to-sub
    (label-wt-comp
     (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
     (L ,, S⋆))
    ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm _ (identity-stm (sty-dim As))) ⟩
  stm-to-term
    (identity-stm (sty-dim As) >>=
     label-wt-comp
     (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) (L ,, S⋆)) ∎
  where
    lem : sub-from-disc (ty-dim (sty-to-type As)) (sty-to-type As) refl (stm-to-term s)
        ≃s label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆)
    lem = begin
      < sub-from-disc (ty-dim (sty-to-type As)) (sty-to-type As) _ (stm-to-term s) >s
        ≈⟨ sub-from-disc-≃ (ty-dim (sty-to-type As)) (sty-dim As) refl≃ty refl (trans (sty-to-type-dim As) (sym refl)) refl≃tm ⟩
      < sub-from-disc (sty-dim As) (sty-to-type As) _ (stm-to-term s) >s
        ≈˘⟨ label-from-linear-tree-to-sub (sty-dim As) s As refl ⟩
      < label-to-sub (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning (tm-setoid-≈ _)
