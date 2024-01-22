open import Catt.Typing.Rule

module Catt.Typing.Insertion (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Standard
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Tree.Structured.Typing rules

open import Catt.Typing.Insertion.Rule

HasInsertion : Set
HasInsertion = ∀ {m n l n′}
             → {Γ : Ctx m}
             → {X : MaybeTree m}
             → {S : Tree n}
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : Branch S l)
             → {T : Tree n′}
             → .⦃ _ : has-trunk-height l T ⦄
             → (M : Label X T)
             → L ⌊ P ⌋p ≃stm (standard-coh′ (lh P) T >>= (M ,, S⋆))
             → {Cs : STy X}
             → Typing-STm Γ (SCoh S As (L ,, S⋆)) Cs
             → (SCoh S As (L ,, S⋆))
               ≈[ Γ ]stm
               SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆)

HasInsertionRule : Set
HasInsertionRule = InsertionSet ⊆r rules

ins-from-rule : HasInsertionRule → HasInsertion
ins-from-rule p {S = S} As L P {T = T} M pf [ tty ] .get = begin
  stm-to-term (SCoh S As (L ,, S⋆))
    ≈˘⟨ reflexive≈tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get) ⟩
  stm-to-term (SCoh S As (label-to-other L ,, S⋆))
    ≈⟨ Rule≈ _ (p [ Insert _ S As (label-to-other L) P T (label-to-other M) lem ])
             (transport-typing tty (sym≃tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get))) ⟩
  stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (label-to-other L >>l[ P ] label-to-other M ,, S⋆))
    ≈˘⟨ reflexive≈tm (SCoh≃ (S >>[ P ] T)
                            (refl≃sty {As = As >>=′ (κ S P T ,, S⋆)})
                            (label-from-insertion-map stm-to-other L P M)
                            (refl≃sty {As = S⋆}) .get) ⟩
  stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (label-to-other (L >>l[ P ] M) ,, S⋆))
    ≈⟨ reflexive≈tm (stm-to-other-prop (SCoh (S >>[ P ] _) (As >>=′ (κ S P _ ,, S⋆)) (L >>l[ P ] M ,, S⋆)) .get) ⟩
  stm-to-term (SCoh (S >>[ P ] _) (As >>=′ (κ S P _ ,, S⋆)) (L >>l[ P ] M ,, S⋆)) ∎
  where
    lem : label-to-other L ⌊ P ⌋p
          ≃stm
          standard-coh′ (lh P) T >>= (label-to-other M ,, S⋆)
    lem = begin
      < label-to-other L ⌊ P ⌋p >stm
        ≈⟨ ap-≃ (label-to-other-prop L) refl≃p ⟩
      < L ⌊ P ⌋p >stm
        ≈⟨ pf ⟩
      < standard-coh′ (lh P) T >>= (M ,, S⋆) >stm
        ≈˘⟨ >>=-≃ (refl≃stm {a = standard-coh′ (lh P) T}) (label-to-other-prop M) (sty-to-other-prop S⋆) ⟩
      < standard-coh′ (lh P) T >>= (label-to-other M ,, S⋆) >stm ∎
      where
        open Reasoning stm-setoid

    open Reasoning (tm-setoid-≈ _)
