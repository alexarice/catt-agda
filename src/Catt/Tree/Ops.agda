open import Catt.Typing.Rule

module Catt.Tree.Ops (ops : Op) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree
open import Catt.Tree.Pasting
open import Catt.Tree.Support

SOp : Set₁
SOp = ∀ {n} (S : Tree n) → TVarSet S → TVarSet S → Set

ops-s : SOp
ops-s S xs ys = ops ⌊ S ⌋ ⦃ tree-to-pd S ⦄ (toVarSet xs) (toVarSet ys)

StandardSOp : SOp → Set
StandardSOp o = ∀ {n} (S : Tree n) (d : ℕ) (p : suc d ≥ tree-dim S)
               → o S (supp-tree-bd d S false) (supp-tree-bd d S true)

standard-op-s : StandardOp ops → StandardSOp ops-s
standard-op-s std S d p = subst₂ (ops ⌊ S ⌋ ⦃ tree-to-pd S ⦄)
                                 (sym (supp-compat′ d S false))
                                 (sym (supp-compat′ d S true))
                                 (std ⌊ S ⌋ ⦃ tree-to-pd S ⦄ d (≤-trans (≤-reflexive (tree-dim-ctx-dim S)) p))
