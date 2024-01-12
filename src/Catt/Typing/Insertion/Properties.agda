import Catt.Typing.Rule as R
import Catt.Typing.Insertion as I

module Catt.Typing.Insertion.Properties {index : Set}
                                        (rule : index → R.Rule)
                                        (lift-rule : ∀ i → R.LiftRule rule (rule i))
                                        (susp-rule : ∀ i → R.SuspRule rule (rule i))
                                        (sub-rule : ∀ i → R.SubRule rule (rule i))
                                        (ins : I.HasInsertion rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Tree.Structured.Typing rule
open import Catt.Tree.Structured.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Canonical.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Insertion.Typing rule lift-rule susp-rule sub-rule

open R rule
open I rule

conv-rule : (P : Branch S l)
          → .⦃ _ : has-trunk-height l T ⦄
          → L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆)
          → ConvRule (Insertion Γ S As L P T M)
conv-rule {S = S} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf {A} tty
  = TyConv (stm-to-term-Ty (TySCoh (S >>[ P ] T) (>>=′-Ty AsTy (κ-Ty S P T) TySStar) (label-from-insertion-Ty Lty P Mty l1) TySStar)) l2
  where
    AsTy : Typing-STy ⌊ S ⌋ As
    AsTy = [ coh-ty-ty tty ]

    Lty : Typing-Label Γ (L ,, S⋆)
    Lty = SCoh-Label-Ty tty

    lem : Typing-STm Γ (canonical-comp (ih P) T >>= (M ,, S⋆)) _
    lem = transport-stm-typing (>>=-Ty (TySPath ⌊ P ⌋p) Lty TySStar)
                               (trans≃stm pf (>>=-≃ (canonical-comp′-compat (ih P) T) refl≃l refl≃sty))
                               refl≃sty

    Mty : Typing-Label Γ (M ,, S⋆)
    Mty = SCoh-Label-Ty {S = T} {As = canonical-type (ih P) T} {L = M} (stm-to-term-Ty lem)

    l1 : branch-type S P >>=′ (L ,, S⋆)
         ≈[ Γ ]sty
         canonical-type (ih P) T >>=′ (M ,, S⋆)
    l1 = STy-unique-≃ pf (>>=-Ty (⌊⌋p-Ty P) Lty TySStar) (>>=-Ty (canonical-comp′-Ty (ih P) T) Mty TySStar)

    l3 : As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆)
         ≈[ Γ ]sty
         As >>=′ (L ,, S⋆)
    l3 = begin
      As >>=′ (κ S P T ,, S⋆) >>=′ (L >>l[ P ] M ,, S⋆)
        ≈⟨ reflexive≈sty (>>=′-assoc As (κ S P T ,, S⋆) (L >>l[ P ] M ,, S⋆)) ⟩
      As >>=′ (κ S P T ,, S⋆) ●lt (L >>l[ P ] M ,, S⋆)
        ≈⟨ >>=′-≈ As (label-max-equality-to-equality (κ-comm L P M S⋆ pf)
                                                     (label-comp-Ty (κ-Ty S P T) (label-from-insertion-Ty Lty P Mty l1) TySStar)
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
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-right-unit (label-to-sub (L ,, S⋆)))) ⟩
      sty-to-type As [ label-to-sub (L ,, S⋆) ● idSub ]ty
        ≈⟨ tm-to-ty-prop tty ⟩
      A ∎
      where
        open Reasoning (ty-setoid-≈ Γ)
