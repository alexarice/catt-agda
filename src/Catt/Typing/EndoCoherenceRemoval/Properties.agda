open import Catt.Typing.Rule
import Catt.Typing.EndoCoherenceRemoval as ECR

module Catt.Typing.EndoCoherenceRemoval.Properties (rules : RuleSet)
                                                   (tame : Tame rules)
                                                   (ecr : ECR.HasEndoCoherenceRemoval rules) where

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

open import Catt.Typing rules
open import Catt.Typing.Properties rules tame
open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Globular.Typing rules lift-cond
open import Catt.Discs.Typing rules lift-cond

open ECR rules

ecr-stm : HasEndoCoherenceRemoval-STm
ecr-stm S s As L [ sty ] [ Asty ] Lty .get = begin
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (label-to-sub (L ,, S⋆) ● idSub)
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (id-right-unit (label-to-sub (L ,, S⋆)))) ⟩
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (label-to-sub (L ,, S⋆))
    ≈⟨ ecr (TyCoh ⦃ tree-to-pd S ⦄ (TyArr sty Asty sty) (label-to-sub-Ty Lty TySStar)) ⟩
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
                                                  (id-right-unit (label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆))))
                                      (refl≃s {σ = label-to-sub (L ,, S⋆)})) ⟩
  identity (sty-dim As) idSub
    [ label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ]tm
    [ label-to-sub (L ,, S⋆) ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm (label-to-sub (L ,, S⋆))
                     (label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆))
                     (identity (sty-dim As) idSub)) ⟩
  identity (sty-dim As) idSub [ label-to-sub (L ,, S⋆) ● label-to-sub (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ]tm
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
    open Reasoning (tm-setoid-≈ _)

{-
conv-rule : ConvRule (EndoCoherenceRemoval Γ Δ s A σ)
conv-rule {Γ = Γ} {Δ = Δ} {s = s} {A = A} {σ = σ} {A = B} tty
  = TyConv (identity-Ty (ty-dim A) (sub-from-disc-Ty (ty-dim A)
                                                     (apply-sub-ty-typing A_ty σty)
                                                     (sym (sub-dim σ A))
                                                     (apply-sub-tm-typing s_ty σty)))
           lem
  where
    σty : Typing-Sub Δ Γ σ
    σty = coh-sub-ty tty

    s_ty : Typing-Tm Δ s A
    s_ty = ty-src-Ty (coh-ty-ty tty)

    A_ty : Typing-Ty Δ A
    A_ty = ty-base-Ty (coh-ty-ty tty)

    l2 : lift-ty (sphere-type (ty-dim A))
           [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty
         ≃ty
         A [ σ ]ty
    l2 = begin
      < lift-ty (sphere-type (ty-dim A)) [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty (sub-from-sphere (ty-dim A) (A [ σ ]ty) _) (sphere-type (ty-dim A)) ⟩
      < sphere-type (ty-dim A) [ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ ]ty >ty
        ≈⟨ sub-from-sphere-prop (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) ⟩
      < A [ σ ]ty >ty ∎
      where
        open Reasoning ty-setoid

    lem : (Var 0F ─⟨ lift-ty (sphere-type (ty-dim A)) ⟩⟶ Var 0F)
            [ sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm) ]ty
          ≈[ Γ ]ty
          B
    lem = begin
      (s [ σ ]tm) ─⟨ lift-ty (sphere-type (ty-dim A)) [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty ⟩⟶ (s [ σ ]tm)
        ≈⟨ Arr≈ refl≈tm (reflexive≈ty l2) refl≈tm ⟩
      (s [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (s [ σ ]tm)
        ≈⟨ tm-to-ty-prop tty ⟩
      B ∎
      where
        open Reasoning (ty-setoid-≈ Γ)
-}
