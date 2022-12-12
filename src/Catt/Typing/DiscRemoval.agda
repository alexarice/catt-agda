open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Typing.DiscRemoval (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Typing index rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n} → {ΓS : CtxOrTree m} → (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ NonZero (tree-dim S) ⦄ → (L : Label (COT-to-MT ΓS) S) → Typing-Label ΓS (L ,, S⋆) → (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ ΓS ]stm L (is-linear-max-path S)
