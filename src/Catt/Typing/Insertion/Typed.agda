open import Catt.Typing.Rule
open import Catt.Ops.Insertion

module Catt.Typing.Insertion.Typed (ops : Op)
                                   (ins-op : InsertionOp ops)
                                   (rules : RuleSet)
                                   (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Support
open import Catt.Tree
open import Catt.Tree.Pasting
open import Catt.Tree.Support
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Support
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing.Insertion.Rule

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Standard.Typing ops rules tame
open import Catt.Tree.Insertion.Typing ops rules tame

open import Catt.Typing.Weak ops

ins-pres : PresCond′ ops rules InsertionSet
ins-pres [ Insert Γ S S⋆ L P T q M pf ] {A = A} tty = ⊥-elim (NonZero-⊥ z≤n ⦃ coh-nonZero tty ⦄)
ins-pres [ Insert Γ S As@(SArr s _ t) L P T q M pf ] {A = A} tty
  = TyConv (stm-to-term-Ty (TySCoh (S >>[ P ] T)
                                   (subst₂ (ops ⌊ S >>[ P ] T ⌋)
                                           (l4 (sty-src As))
                                           (l4 (sty-tgt As))
                                           (ins-op S P T q
                                                         (SuppSTm (incTree S) s)
                                                         (SuppSTm (incTree S) t)
                                                         (subst₂ (ops ⌊ S ⌋)
                                                                 (sym (SuppSTm-to-term (incTree S) s))
                                                                 (sym (SuppSTm-to-term (incTree S) t))
                                                                 (coh-supp tty))))
                                   (>>=′-Ty AsTy (κ-Ty S P T q) TySStar)
                                   (label-from-insertion-Ty Lty P Mty l1)
                                   TySStar))
           l2
  where
    AsTy : Typing-STy ⌊ S ⌋ As
    AsTy = [ coh-ty-ty tty ]

    Lty : Typing-Label Γ (L ,, S⋆)
    Lty = SCoh-Label-Ty {As = As} tty

    lem : Typing-STm Γ (standard-coh (lh P) T >>= (M ,, S⋆)) _
    lem = transport-stm-typing (>>=-Ty (TySPath ⌊ P ⌋p) Lty TySStar)
                               (trans≃stm pf (>>=-≃ (standard-coh′-compat (lh P) T) refl≃l refl≃sty))
                               refl≃sty

    Mty : Typing-Label Γ (M ,, S⋆)
    Mty = SCoh-Label-Ty {S = T} {As = standard-sty (lh P) T} {L = M} (stm-to-term-Ty lem)

    l1 : branch-type S P >>=′ (L ,, S⋆)
         ≈[ Γ ]sty
         standard-sty (lh P) T >>=′ (M ,, S⋆)
    l1 = STy-unique-≃ pf (>>=-Ty (⌊⌋p-Ty P) Lty TySStar) (>>=-Ty (standard-coh′-Ty (lh P) T q) Mty TySStar)

    l3 : As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆)
         ≈[ Γ ]sty
         As >>=′ (L ,, S⋆)
    l3 = begin
      As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆)
        ≈⟨ reflexive≈sty (>>=′-assoc As (κ S P T ,, S⋆) (L >>l[ P ] M ,, S⋆)) ⟩
      As >>=′ (κ S P T ,, S⋆) ●lt (L >>l[ P ] M ,, S⋆)
        ≈⟨ >>=′-≈ As (label-max-equality-to-equality (κ-comm L P M S⋆ pf)
                                                     (label-comp-Ty (κ-Ty S P T q) (label-from-insertion-Ty Lty P Mty l1) TySStar)
                                                     Lty)
                     refl≈sty ⟩
      As >>=′ (L ,, S⋆) ∎
      where
        open Reasoning sty-setoid-≈

    l2 : sty-to-type (As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆)) ≈[ Γ ]ty A
    l2 = begin
      sty-to-type (As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆))
        ≈⟨ l3 .get ⟩
      sty-to-type (As >>=′ (L ,, S⋆))
        ≈˘⟨ reflexive≈ty (label-to-sub-sty (L ,, S⋆) As) ⟩
      sty-to-type As [ label-to-sub (L ,, S⋆) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-left-unit (label-to-sub (L ,, S⋆)))) ⟩
      sty-to-type As [ idSub ● label-to-sub (L ,, S⋆) ]ty
        ≈⟨ tm-to-ty-prop tty ⟩
      A ∎
      where
        open Reasoning (ty-setoid-≈ Γ)

    open ≡-Reasoning

    l4 : (a : STm (someTree S))
       → SuppSTm (incTree S) a [ κ S P T ]vl
         ≡
         SuppSTm (incTree (S >>[ P ] T)) (a >>= (κ S P T ,, S⋆))
    l4 a = sym (vs-label-STm (incTree (S >>[ P ] T)) a (κ S P T) (W.κ-Ty S P T q))
      where
        open import Catt.Typing.Structured.Support ops Weak-Rules (weak-tame tame-op) weak-supp
        import Catt.Tree.Insertion.Typing ops Weak-Rules (weak-tame tame-op) as W
