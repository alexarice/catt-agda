open import Catt.Typing.Rule

module Catt.Ops.Insertion (ops : Op) where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Support
open import Catt.Tree.Pasting
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support

open import Catt.Ops.Tree ops

InsertionSOp : Set
InsertionSOp = ∀ {n} {l} {m} (S : Tree n)
                           → (P : Branch S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → (lh P ≥ tree-dim T)
                           → (xs : TVarSet S)
                           → (ys : TVarSet S)
                           → ops-s S xs ys
                           → ops ⌊ S >>[ P ] T ⌋
                                 (xs [ κ S P T ]vl)
                                 (ys [ κ S P T ]vl)
