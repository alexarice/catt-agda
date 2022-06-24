module Catt.Tree.Boundary where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Label

tree-bd-len : (d : ℕ) → (T : Tree n) → ℕ
tree-bd-len zero T = 0
tree-bd-len (suc d) Sing = 0
tree-bd-len (suc d) (Join S T) = tree-bd-len (suc d) T + (2 + tree-bd-len d S)

tree-bd : (d : ℕ) → (T : Tree n) → Tree (tree-bd-len d T)
tree-bd zero T = Sing
tree-bd (suc d) Sing = Sing
tree-bd (suc d) (Join S T) = Join (tree-bd d S) (tree-bd (suc d) T)

tree-inc-label′ : (d : ℕ) → (T : Tree n) → (b : Bool) → Label-func′ T (tree-bd d T)
tree-inc-label′ zero T false Z = PPHere
tree-inc-label′ zero T true Z = last-path T
tree-inc-label′ (suc d) Sing b Z = Z
tree-inc-label′ (suc d) (Join S T) b ⟦ PHere ⟧ = PPHere
tree-inc-label′ (suc d) (Join S T) b ⟦ PExt Z ⟧ = PPExt (tree-inc-label′ d S b ⟦ Z ⟧)
tree-inc-label′ (suc d) (Join S T) b ⟦ PShift Z ⟧ = PPShift (tree-inc-label′ (suc d) T b ⟦ Z ⟧)

tree-inc-label : (d : ℕ) → (T : Tree n) → (b : Bool) → Label (someTree T) (tree-bd d T) ⋆
tree-inc-label d T b .ap Z = carrier (tree-inc-label′ d T b Z)

tree-inc : (d : ℕ) → (T : Tree n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n) ⋆
tree-inc d T b = label-to-sub (tree-inc-label d T b)
