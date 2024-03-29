open import Catt.Typing.Rule

module Catt.Ops.Insertion (ops : Op) where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Support
open import Catt.Tree.Pasting
open import Catt.Tree.Structured.Support

InsertionOp : Set
InsertionOp = ∀ {n} {l} {m} (S : Tree n)
                           → (P : Branch S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → (lh P ≥ tree-dim T)
                           → (xs : VarSet (suc n))
                           → (ys : VarSet (suc n))
                           → ops ⌊ S ⌋ xs ys
                           → ops ⌊ S >>[ P ] T ⌋
                                 (xs [ κ S P T ]vl)
                                 (ys [ κ S P T ]vl)
