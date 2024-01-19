module Catt.Tree.Standard where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary

standard-type : (d : ℕ) → (T : Tree n) → STy (someTree T)
standard-term : (d : ℕ) → (T : Tree n) → Tm (suc n)
standard-stm : (d : ℕ) → (T : Tree n) → STm (someTree T)
standard-comp : (d : ℕ) → (T : Tree n) → STm (someTree T)
standard-comp′ : (d : ℕ) → (T : Tree n) → STm (someTree T)
standard-comp-term : (d : ℕ) → (T : Tree n) → Tm (suc n)

standard-type zero T = S⋆
standard-type (suc d) T = SArr (standard-stm d (tree-bd d T) >>= tree-inc-label d T false) (standard-type d T) (standard-stm d (tree-bd d T) >>= tree-inc-label d T true)

standard-term d T = stm-to-term (standard-stm d T)

standard-stm zero Sing = SHere
standard-stm zero (Join S T) = standard-comp zero (Join S T)
standard-stm (suc d) Sing = standard-comp (suc d) Sing
standard-stm (suc d) (Susp T) = SExt (standard-stm d T)
standard-stm (suc d) (Join T (Join T₁ T₂)) = standard-comp (suc d) (Join T (Join T₁ T₂))

standard-comp d T = SCoh T (standard-type d T) (id-label-wt T)

standard-comp′ zero T = standard-comp zero T
standard-comp′ (suc d) Sing = standard-comp (suc d) Sing
standard-comp′ (suc d) (Susp T) = SExt (standard-comp′ d T)
standard-comp′ (suc d) T@(Join _ (Join _ _)) = standard-comp (suc d) T

standard-comp-term d T = stm-to-term (standard-comp d T)

instance
  standard-dim : {d : ℕ} → {T : Tree n} → has-dim d (standard-type d T)
  standard-dim {d = zero} {T} = tt
  standard-dim {d = suc d} {T} = inst

standard-label : (S : Tree n) → .⦃ is-linear S ⦄ → (T : Tree m) → Label (someTree T) S
standard-label S T
  = stm-to-label S (standard-comp′ (tree-dim S) T) (standard-type (tree-dim S) T)
