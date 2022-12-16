open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Typing.Insertion (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing index rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path
open import Catt.Tree.Insertion


HasInsertion : Set
HasInsertion = ∀ {m n l n′}
                 → {ΓS : CtxOrTree m}
                 → (S : Tree n)
                 → (As : STy (someTree S))
                 → (L : Label (COT-to-MT ΓS) S)
                 → (P : BranchingPoint S l)
                 → (T : Tree n′)
                 → .⦃ _ : has-linear-height l T ⦄
                 → (M : Label (COT-to-MT ΓS) T)
                 → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
                 → Typing-STy (incTree S) As
                 → Typing-Label ΓS (L ,, S⋆)
                 → (SCoh S As (L ,, S⋆)) ≈[ ΓS ]stm SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)
