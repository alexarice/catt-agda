open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval (index : ℕ) (rule : Fin index → Rule) where

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

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n} → {ΓS : CtxOrTree m} → (S : Tree n) → (s : STm (incTree S)) → (As : STy (incTree S))
