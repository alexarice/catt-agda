open import Catt.Typing.Rule
import Catt.Typing.EndoCoherenceRemoval as ECR

module Catt.Typing.EndoCoherenceRemoval.Properties (ops : Op)
                                                   (rules : RuleSet)
                                                   (tame : Tame ops rules)
                                                   (ecr : ECR.HasEndoCoherenceRemoval ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules lift-cond

open import Catt.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Support.Properties

open ECR ops rules

ecr-stm : HasEndoCoherenceRemoval-STm
ecr-stm S s sfull As supp L [ sty ] [ Asty ] Lty .get = begin
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (idSub ● label-to-sub (L ,, S⋆))
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (id-left-unit (label-to-sub (L ,, S⋆)))) ⟩
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (label-to-sub (L ,, S⋆))
    ≈⟨ ecr full-lem
           (TyCoh ⦃ tree-to-pd S ⦄
                  (subst₂ (ops ⌊ S ⌋)
                          (trans (DCT-toVarSet (FVSTm s)) (FVSTm-to-term s))
                          (trans (DCT-toVarSet (FVSTm s)) (FVSTm-to-term s))
                          supp)
                  (TyArr sty Asty sty)
                  (label-to-sub-Ty Lty TySStar)) ⟩
  identity (ty-dim (sty-to-type As))
           (sub-from-disc (ty-dim (sty-to-type As))
                          (sty-to-type As [ label-to-sub (L ,, S⋆) ]ty)
                          _
                          (stm-to-term s [ label-to-sub (L ,, S⋆) ]tm))
    ≈⟨ reflexive≈tm (identity-≃ refl
                                (sub-from-disc-sub (ty-dim (sty-to-type As))
                                                   (sty-to-type As)
                                                   refl
                                                   (stm-to-term s)
                                                   (label-to-sub (L ,, S⋆)))) ⟩
  identity (ty-dim (sty-to-type As))
           (sub-from-disc (ty-dim (sty-to-type As))
                          (sty-to-type As)
                          _
                          (stm-to-term s))
    [ label-to-sub (L ,, S⋆) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (identity-≃ (sty-to-type-dim As) lem) (refl≃s {σ = label-to-sub (L ,, S⋆)})) ⟩
  identity (sty-dim As) (label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆)) [ label-to-sub (L ,, S⋆) ]tm
    ≈˘⟨ reflexive≈tm (sub-action-≃-tm (identity-≃ (refl {x = sty-dim As})
                                                  (id-left-unit (label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆))))
                                      (refl≃s {σ = label-to-sub (L ,, S⋆)})) ⟩
  identity (sty-dim As) idSub
    [ label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ]tm
    [ label-to-sub (L ,, S⋆) ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm (label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆))
                               (label-to-sub (L ,, S⋆))
                               (identity (sty-dim As) idSub)) ⟩
  identity (sty-dim As) idSub [ label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆)
                              ● label-to-sub (L ,, S⋆) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (trans≃tm (identity-≃ (sym (≃n-to-≡ (tree-dim-n-disc {n = sty-dim As})))
                                                           (idSub-≃ (cong disc-size (sym (≃n-to-≡ (tree-dim-n-disc {n = sty-dim As}))))))
                                               (sym≃tm (identity-stm-to-term (n-disc (sty-dim As)))))
                                     (label-comp-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) (L ,, S⋆))) ⟩
  stm-to-term (identity-stm (n-disc (sty-dim As))) [ label-to-sub ((stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ●lt (L ,, S⋆)) ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm ((stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ●lt (L ,, S⋆)) (identity-stm (n-disc (sty-dim As)))) ⟩
  stm-to-term (identity-stm (n-disc (sty-dim As)) >>= ((stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ●lt (L ,, S⋆))) ∎
    where
    lem : sub-from-disc (ty-dim (sty-to-type As)) (sty-to-type As) refl (stm-to-term s)
        ≃s label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆)
    lem = begin
      < sub-from-disc (ty-dim (sty-to-type As)) (sty-to-type As) _ (stm-to-term s) >s
        ≈⟨ sub-from-disc-≃ (ty-dim (sty-to-type As)) (sty-dim As) refl≃ty refl (trans (sty-to-type-dim As) (sym refl)) refl≃tm ⟩
      < sub-from-disc (sty-dim As) (sty-to-type As) _ (stm-to-term s) >s
        ≈˘⟨ stm-to-label-to-sub (n-disc (sty-dim As)) s As ⟩
      < label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) >s ∎
      where
        open Reasoning sub-setoid

    full-lem : SuppTm ⌊ S ⌋ (stm-to-term s) ≡ full
    full-lem = begin
      SuppTm ⌊ S ⌋ (stm-to-term s)
        ≡˘⟨ FVSTm-to-term s ⟩
      toVarSet (FVSTm s)
        ≡˘⟨ DCT-toVarSet (FVSTm s) ⟩
      toVarSet (DCT (FVSTm s))
        ≡⟨ cong toVarSet sfull ⟩
      toVarSet (tFull {S = S})
        ≡⟨ toVarSet-full S ⟩
      full ∎
      where
        open ≡-Reasoning

    open Reasoning (tm-setoid-≈ _)
