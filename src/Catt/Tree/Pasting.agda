module Catt.Tree.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Wedge.Pasting
open import Catt.Tree

-- Tree to pd conversion
tree-to-pd : (T : Tree m) → ⌊ T ⌋ ⊢pd
tree-to-pd Sing = Finish Base
tree-to-pd (Join S T) = wedge-susp-pd (tree-to-pd S) (tree-to-pd T)

tree-to-pd-focus-tm : (T : Tree m) → pd-focus-tm (tree-to-pd T) ≃tm tree-last-var T
tree-to-pd-focus-tm Sing = refl≃tm
tree-to-pd-focus-tm (Join S T) = begin
  < pd-focus-tm (wedge-susp-pd (tree-to-pd S) (tree-to-pd T)) >tm
    ≈⟨ wedge-susp-focus-tm (tree-to-pd S) (pd-to-pdb (tree-to-pd T)) ⟩
  < focus-tm (pd-to-pdb (tree-to-pd T)) [ wedge-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (tree-to-pd-focus-tm T) refl≃s ⟩
  < tree-last-var T [ wedge-susp-inc-right (tree-size S) (tree-size T) ]tm >tm ∎
  where
    open Reasoning tm-setoid
