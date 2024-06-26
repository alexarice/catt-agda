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
open import Catt.Tree.Boundary
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Standard.Typing ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond

open import Catt.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Standard.Support

open ECR ops rules

ecr-stm : HasEndoCoherenceRemoval-STm
ecr-stm S s sfull As supp L [ sty ] [ Asty ] Lty .get = begin
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (idSub ● label-to-sub (L ,, S⋆))
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (id-left-unit (label-to-sub (L ,, S⋆)))) ⟩
  Coh ⌊ S ⌋ (stm-to-term s ─⟨ sty-to-type As ⟩⟶ stm-to-term s) (label-to-sub (L ,, S⋆))
    ≈⟨ ecr full-lem
           (TyCoh ⦃ tree-to-pd S ⦄
                  (subst₂ (ops ⌊ S ⌋)
                          (SuppSTm-to-term (incTree S) s)
                          (SuppSTm-to-term (incTree S) s)
                          supp)
                  (TyArr sty Asty sty)
                  (label-to-sub-Ty Lty TySStar)) ⟩
  identity-term (sty-to-type As [ label-to-sub (L ,, S⋆) ]ty)
                (stm-to-term s [ label-to-sub (L ,, S⋆) ]tm)
    ≈˘⟨ reflexive≈tm (identity-term-sub (sty-to-type As) (stm-to-term s) (label-to-sub (L ,, S⋆))) ⟩
  identity-term (sty-to-type As) (stm-to-term s)
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
        ≡˘⟨ SuppSTm-to-term (incTree S) s ⟩
      SuppSTm (incTree S) s
        ≡⟨ sfull ⟩
      full ∎
      where
        open ≡-Reasoning

    open Reasoning (tm-setoid-≈ _)

standard-ecr : (d : ℕ)
             → (T : Tree n)
             → (tree-dim T < d)
             → standard-coh d T
               ≈[ ⌊ T ⌋ ]stm
               identity-stm (n-disc (pred d)) >>= (stm-to-label (n-disc (pred d)) (standard-stm (pred d) T) (standard-sty (pred d) T) ⦃ trans≃n tree-dim-n-disc it ⦄ ,, S⋆)
standard-ecr (suc d) T p = begin
  SCoh T
       (SArr (standard-stm d (tree-bd d T) >>=
                             (tree-inc-label d T false))
             (standard-sty d T)
             (standard-stm d (tree-bd d T) >>=
                             (tree-inc-label d T true)))
       (id-label-wt T)
    ≈⟨ reflexive≈stm (SCoh≃ T (SArr≃ (standard-stm-full-lem d T false (≤-pred p))
                                     refl≃sty
                                     (standard-stm-full-lem d T true (≤-pred p)))
                              refl≃l
                              refl≃sty) ⟩
  SCoh T (SArr (standard-stm d T)
               (standard-sty d T)
               (standard-stm d T))
         (id-label-wt T)
    ≈⟨ ecr-stm T (standard-stm d T)
                 (standard-stm-full d T (≤-pred p))
                 (standard-sty d T)
                 (subst₂ (ops ⌊ T ⌋)
                         (supp-lem false)
                         (supp-lem true)
                         (tree-standard-op ops standard-op T d (≤-trans (n≤1+n (tree-dim T)) p)))
                 (id-label T)
                 (standard-stm-Ty d T (≤-pred p))
                 (standard-sty-Ty d T)
                 (id-label-Ty T) ⟩
  identity-stm (n-disc (sty-dim (standard-sty d T)))
    >>=
    (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                  (standard-stm d T)
                  (standard-sty d T) ,, S⋆)
    ●lt id-label-wt T
    ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = identity-stm (n-disc (sty-dim (standard-sty d T)))})
                            (comp-right-unit (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                                                           (standard-stm d T)
                                                           (standard-sty d T)))
                            refl≃sty) ⟩
  identity-stm (n-disc (sty-dim (standard-sty d T)))
    >>= (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                      (standard-stm d T)
                      (standard-sty d T) ⦃ _ ⦄ ,, S⋆)
    ≈⟨ reflexive≈stm (lem (standard-sty-dim d T)) ⟩
  identity-stm (n-disc d)
    >>= (stm-to-label (n-disc d)
                      (standard-stm d T)
                      (standard-sty d T) ⦃ _ ⦄ ,, S⋆) ∎
  where
    supp-lem : (b : Bool) → tree-bd-vs d T b ≡ SuppSTm (incTree T) (standard-stm d T)
    supp-lem b = begin
      tree-bd-vs d T b
        ≡⟨ tree-bd-vs-full d T b (≤-pred p) ⟩
      full
        ≡˘⟨ standard-stm-full d T (≤-pred p) ⟩
      SuppSTm (incTree T) (standard-stm d T) ∎
      where
        open ≡-Reasoning

    open Reasoning stm-setoid-≈

    lem : (p : d′ ≡ d)
        → identity-stm (n-disc d′)
          >>= (stm-to-label (n-disc d′) (standard-stm d T) (standard-sty d T)
                            ⦃ trans≃n tree-dim-n-disc (trans≃n (≡-to-≃n p) it) ⦄ ,, S⋆)
          ≃stm
          identity-stm (n-disc d)
          >>= (stm-to-label (n-disc d) (standard-stm d T) (standard-sty d T)
                            ⦃ trans≃n tree-dim-n-disc it ⦄ ,, S⋆)
    lem refl = refl≃stm
