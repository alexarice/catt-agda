{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree where

open import Catt.Syntax
open import Catt.Connection
open import Catt.Suspension
open import Data.Nat
open import Data.Fin using (fromℕ)

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

tree-size : Tree n → ℕ
tree-size {n} T = n

tree-to-ctx : (T : Tree m) → Ctx (suc m)
tree-last-var : (T : Tree n) → Tm (suc n)

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-susp (tree-to-ctx S) (tree-to-ctx T)

tree-fst-var : (T : Tree n) → Tm (suc n)
tree-fst-var T = Var (fromℕ _)

tree-last-var Sing = 0V
tree-last-var (Join S T) = tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

connect-tree-length : (S : Tree n) → (T : Tree m) → ℕ
connect-tree-length {m = m} Sing T = m
connect-tree-length (Join {x} S S′) T = connect-tree-length S′ T + (2 + x)

connect-tree : (S : Tree n) → (T : Tree m) → Tree (connect-tree-length S T)
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)
