module Catt.Tree.Boundary where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.ToTerm

tree-bd-len : (d : ℕ) → (T : Tree n) → ℕ
tree-bd-len zero T = 0
tree-bd-len (suc d) Sing = 0
tree-bd-len (suc d) (Join S T) = tree-bd-len (suc d) T + (2 + tree-bd-len d S)

tree-bd : (d : ℕ) → (T : Tree n) → Tree (tree-bd-len d T)
tree-bd zero T = Sing
tree-bd (suc d) Sing = Sing
tree-bd (suc d) (Join S T) = Join (tree-bd d S) (tree-bd (suc d) T)

tree-inc-label′ : (d : ℕ) → (T : Tree n) → (b : Bool) → Label′ T (tree-bd d T)
tree-inc-label′ zero T false Z = PHere
tree-inc-label′ zero T true Z = last-path T
tree-inc-label′ (suc d) Sing b Z = Z
tree-inc-label′ (suc d) (Join S T) b PHere = PHere
tree-inc-label′ (suc d) (Join S T) b (PExt Z) = PExt (tree-inc-label′ d S b Z)
tree-inc-label′ (suc d) (Join S T) b (PShift Z) = PShift (tree-inc-label′ (suc d) T b Z)

tree-inc-label : (d : ℕ) → (T : Tree n) → (b : Bool) → Label-WT (someTree T) (tree-bd d T)
tree-inc-label d T b = SPath ∘ tree-inc-label′ d T b ,, S⋆

tree-inc : (d : ℕ) → (T : Tree n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n) ⋆
tree-inc d T b = label-to-sub (tree-inc-label d T b)

is-linear-bd : (d : ℕ) → (S : Tree n) → .⦃ is-linear S ⦄ → is-linear (tree-bd d S)
is-linear-bd zero S = tt
is-linear-bd (suc d) Sing = tt
is-linear-bd (suc d) (Join S Sing) = inst ⦃ is-linear-bd d S ⦄

disc-inc : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → (b : Bool) → Path T
disc-inc d T b = tree-inc-label′ d T b (is-linear-max-path (tree-bd d T) ⦃ is-linear-bd d T ⦄)
