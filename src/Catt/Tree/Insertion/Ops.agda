open import Catt.Typing.Base

module Catt.Tree.Insertion.Ops (ops : Op) where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Insertion
open import Catt.Support
open import Catt.Tree.Pasting
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support

open import Catt.Tree.Ops ops

InsertionSOp : Set
InsertionSOp = ∀ {n} {l} {m} (S : Tree n)
                           → (P : Branch S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → (xs : TVarSet S)
                           → (ys : TVarSet S)
                           → ops-s S xs ys
                           → ops ⌊ S >>[ P ] T ⌋
                                 ⦃ tree-to-pd (S >>[ P ] T) ⦄
                                 (TransportVarSet-Label xs (κ S P T))
                                 (TransportVarSet-Label ys (κ S P T))
