open import Catt.Typing.Base

module Catt.Typing.Insertion {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path
open import Catt.Tree.Insertion


HasInsertion : Set
HasInsertion = ∀ {m n l n′}
             → {Γ : Ctx m}
             → {X : MaybeTree m}
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label X T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → Typing-STy (tree-to-ctx S) As
             → Typing-Label Γ (L ,, S⋆)
             → (SCoh S As (L ,, S⋆)) ≈[ Γ ]stm SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)
