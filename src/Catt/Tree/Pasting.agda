module Catt.Tree.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Pasting
open import Catt.Tree

-- Extendability
n-extendable : ℕ → Tree n → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S Sing) = n-extendable n S
n-extendable (suc n) (Join S T@(Join _ _)) = n-extendable (suc n) T

extend-tree : (n : ℕ) → (T : Tree m) → .⦃ n-extendable n T ⦄ → Tree (2 + m)
extend-tree zero Sing = Join Sing Sing
extend-tree zero (Join S Sing) = Join S (Join Sing Sing)
extend-tree zero (Join S T@(Join _ _)) = Join S (extend-tree zero T)
extend-tree (suc n) (Join S Sing) = Join (extend-tree n S) Sing
extend-tree (suc n) (Join S T@(Join _ _)) = Join S (extend-tree (suc n) T)

join-tree-preserves-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → ⦃ n-extendable n T ⦄ → n-extendable n (Join S T)
join-tree-preserves-extendable zero S T = it
join-tree-preserves-extendable (suc n) S (Join _ _) = it

extended-tree-is-more-extendable : (n : ℕ) → (T : Tree m) → ⦃ _ : n-extendable n T ⦄ → n-extendable (suc n) (extend-tree n T)
extended-tree-is-more-extendable zero Sing = it
extended-tree-is-more-extendable zero (Join S Sing) = it
extended-tree-is-more-extendable zero (Join S T@(Join _ _)) ⦃ x ⦄ = join-tree-preserves-extendable 1 S (extend-tree zero T) ⦃ extended-tree-is-more-extendable zero T ⦄
extended-tree-is-more-extendable (suc n) (Join S Sing) = extended-tree-is-more-extendable n S
extended-tree-is-more-extendable (suc n) (Join S T@(Join _ _)) = join-tree-preserves-extendable (suc (suc n)) S (extend-tree (suc n) T) ⦃ extended-tree-is-more-extendable (suc n) T ⦄

pred-n-extendable : (n : ℕ) → (T : Tree m) → ⦃ n-extendable (suc n) T ⦄ → n-extendable n T
pred-n-extendable zero T = tt
pred-n-extendable (suc n) (Join S Sing) = pred-n-extendable n S
pred-n-extendable (suc n) (Join S T@(Join _ _)) = pred-n-extendable (suc n) T

-- Tree to pd conversion
tree-to-pd : (T : Tree m) → ⌊ T ⌋ ⊢pd
tree-to-pd Sing = Finish Base
tree-to-pd (Join S T) = connect-susp-pd (tree-to-pd S) (tree-to-pd T)

tree-to-pd-focus-tm : (T : Tree m) → pd-focus-tm (tree-to-pd T) ≃tm tree-last-var T
tree-to-pd-focus-tm Sing = refl≃tm
tree-to-pd-focus-tm (Join S T) = begin
  < pd-focus-tm (connect-susp-pd (tree-to-pd S) (tree-to-pd T)) >tm
    ≈⟨ connect-susp-focus-tm (tree-to-pd S) (pd-to-pdb (tree-to-pd T)) ⟩
  < focus-tm (pd-to-pdb (tree-to-pd T)) [ connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (tree-to-pd-focus-tm T) refl≃s ⟩
  < tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm ∎
  where
    open Reasoning tm-setoid
