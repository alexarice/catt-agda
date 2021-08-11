{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Tree where

open import Catt.Syntax
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Connection
open import Data.Nat
open import Data.List

singleton-ctx : Ctx 1 1
singleton-ctx = ∅ , ⋆

singleton-pd : singleton-ctx ⊢pd₀ 0
singleton-pd = Finish Base

data Tree : Set where
  Node : (l : List Tree) → Tree

tree-to-ctx-len-1 : Tree → ℕ
tree-to-ctx-dim : Tree → ℕ
tree-to-ctx : (T : Tree) → Ctx (suc (tree-to-ctx-len-1 T)) (tree-to-ctx-dim T)
tree-to-pd-dim : Tree → ℕ
tree-to-pd : (T : Tree) → tree-to-ctx T ⊢pd₀ tree-to-pd-dim T

list-to-ctx-len-1 : List Tree → ℕ
list-to-ctx-dim : List Tree → ℕ
list-to-ctx : (l : List Tree) → Ctx (suc (list-to-ctx-len-1 l)) (list-to-ctx-dim l)
list-to-pd-dim : List Tree → ℕ
list-to-pd : (l : List Tree) → list-to-ctx l ⊢pd₀ list-to-pd-dim l

tree-to-ctx-len-1 (Node l) = suc (suc (list-to-ctx-len-1 l))

tree-to-ctx-dim (Node l) = suc (list-to-ctx-dim l)

tree-to-ctx (Node l) = suspCtx (list-to-ctx l)

tree-to-pd-dim (Node l) = suc (list-to-pd-dim l)

tree-to-pd (Node l) = susp-pd (list-to-pd l)

list-to-ctx-len-1 [] = 0
list-to-ctx-len-1 (T ∷ l) = tree-to-ctx-len-1 T + list-to-ctx-len-1 l

list-to-ctx-dim [] = 1
list-to-ctx-dim (T ∷ l) = connect-dim (list-to-ctx l) (pd-focus-tm (list-to-pd l)) (tree-to-ctx T)

list-to-ctx [] = singleton-ctx
list-to-ctx (T ∷ l) = connect-pd (list-to-pd l) (tree-to-ctx T)

list-to-pd-dim [] = 0
list-to-pd-dim (T ∷ l) = connected-dim (list-to-pd l) (tree-to-pd T)

list-to-pd [] = singleton-pd
list-to-pd (T ∷ l) = connect-pd-pd (list-to-pd l) (tree-to-pd T)
