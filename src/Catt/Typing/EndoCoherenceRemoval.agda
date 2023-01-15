open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {ΓS : CtxOrTree m}
                        → (S : Tree n)
                        → (s : STm (someTree S))
                        → (As : STy (someTree S))
                        → (L : Label (COT-to-MT ΓS) S)
                        → Typing-STm (incTree S) s As
                        → Typing-STy (incTree S) As
                        → Typing-Label ΓS (L ,, S⋆)
                        → SCoh S (SArr s As s) (L ,, S⋆) ≈[ ΓS ]stm (identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆))
