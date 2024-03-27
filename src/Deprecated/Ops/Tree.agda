open import Catt.Typing.Rule

module Deprecated.Ops.Tree (ops : Op) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree
open import Catt.Tree.Pasting
open import Deprecated.Tree.Support

SOp : Set₁
SOp = ∀ {n} (S : Tree n) → TVarSet S → TVarSet S → Set

ops-s : SOp
ops-s S xs ys = ops ⌊ S ⌋ (toVarSet xs) (toVarSet ys)

StandardSOp : SOp → Set
StandardSOp o = ∀ {n} (S : Tree n) (d : ℕ) (p : suc d ≥ tree-dim S)
               → o S (tree-bd-vs d S false) (tree-bd-vs d S true)

standard-op-s : StandardOp ops → StandardSOp ops-s
standard-op-s std S d p = subst₂ (ops ⌊ S ⌋)
                                 (sym (supp-compat′ d S false))
                                 (sym (supp-compat′ d S true))
                                 (std ⌊ S ⌋ ⦃ tree-to-pd S ⦄ d (≤-trans (≤-reflexive (tree-dim-ctx-dim S)) p))
