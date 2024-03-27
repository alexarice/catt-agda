open import Catt.Typing.Rule

module Catt.Typing.Insertion.Support (ops : Op)
                                     (rules : RuleSet)
                                     (tame : Tame ops rules)
                                     (supp-cond : SupportCond ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Insertion.Support
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Boundary.Typing ops rules tame
open import Catt.Tree.Standard.Typing ops rules tame
open import Catt.Tree.Insertion.Typing ops rules tame
open import Catt.Typing.Insertion.Rule

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Standard.Support

open import Catt.Typing.Structured.Support ops rules tame supp-cond

ins-supp : SupportCond′ ops rules InsertionSet
ins-supp [ Insert Γ S As L P T q M p ] tty = begin
  SuppTm Γ (stm-to-term (SCoh S As (L ,, S⋆)))
    ≡˘⟨ SuppSTm-to-term (incCtx Γ) (SCoh S As (L ,, S⋆)) ⟩
  SuppLabel-WT (incCtx Γ) (L ,, S⋆)
    ≡⟨ ∪-left-unit _ ⟩
  SuppLabel (incCtx Γ) L
    ≡˘⟨ EqSuppLabel (label-max-equality-to-equality (κ-comm L P M S⋆ p) (label-comp-Ty (κ-Ty S P T q) l2 TySStar) Lty) ⟩
  SuppLabel (incCtx Γ) (κ S P T ●l (L >>l[ P ] M ,, S⋆))
    ≡⟨ vs-label-Label (incCtx Γ) (κ S P T) (L >>l[ P ] M) l2 ⟩
  (SuppLabel (incTree (S >>[ P ] T)) (κ S P T)) [ L >>l[ P ] M ]vl
    ≡⟨ cong (_[ L >>l[ P ] M ]vl) (κ-full S P T) ⟩
  full [ L >>l[ P ] M ]vl
    ≡⟨ vs-label-full (incCtx Γ) (L >>l[ P ] M) l2 ⟩
  SuppLabel (incCtx Γ) (L >>l[ P ] M)
    ≡˘⟨ ∪-left-unit _ ⟩
  SuppLabel-WT (incCtx Γ) (L >>l[ P ] M ,, S⋆)
    ≡⟨ SuppSTm-to-term (incCtx Γ) (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆)) ⟩
  SuppTm Γ (stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆))) ∎
  where
    open ≡-Reasoning

    Lty : Typing-Label Γ (L ,, S⋆)
    Lty = SCoh-Label-Ty tty


    lem : Typing-STm Γ (standard-coh (lh P) T >>= (M ,, S⋆)) _
    lem = transport-stm-typing (>>=-Ty (TySPath ⌊ P ⌋p) Lty TySStar)
                               (trans≃stm p (>>=-≃ (standard-coh′-compat (lh P) T) refl≃l refl≃sty))
                               refl≃sty

    Mty : Typing-Label Γ (M ,, S⋆)
    Mty = SCoh-Label-Ty {S = T} {As = standard-sty (lh P) T} {L = M} (stm-to-term-Ty lem)

    l1 : branch-type S P >>=′ (L ,, S⋆)
         ≈[ Γ ]sty
         standard-sty (lh P) T >>=′ (M ,, S⋆)
    l1 = STy-unique-≃ p (>>=-Ty (⌊⌋p-Ty P) Lty TySStar) (>>=-Ty (standard-coh′-Ty (lh P) T q) Mty TySStar)

    l2 : Typing-Label Γ (L >>l[ P ] M ,, S⋆)
    l2 = label-from-insertion-Ty Lty P Mty l1
