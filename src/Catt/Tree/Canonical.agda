module Catt.Tree.Canonical where

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

canonical-type : (d : ℕ) → (T : Tree n) → STy (someTree T)
canonical-term : (d : ℕ) → (T : Tree n) → Tm (suc n)
canonical-stm : (d : ℕ) → (T : Tree n) → STm (someTree T)
canonical-comp : (d : ℕ) → (T : Tree n) → STm (someTree T)
canonical-comp′ : (d : ℕ) → (T : Tree n) → STm (someTree T)
canonical-comp-term : (d : ℕ) → (T : Tree n) → Tm (suc n)

canonical-type zero T = S⋆
canonical-type (suc d) T = SArr (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false) (canonical-type d T) (canonical-stm d (tree-bd d T) >>= tree-inc-label d T true)

canonical-term d T = stm-to-term (canonical-stm d T)

canonical-stm zero Sing = SHere
canonical-stm zero (Join S T) = canonical-comp zero (Join S T)
canonical-stm (suc d) Sing = canonical-comp (suc d) Sing
canonical-stm (suc d) (Join T Sing) = SExt (canonical-stm d T)
canonical-stm (suc d) (Join T (Join T₁ T₂)) = canonical-comp (suc d) (Join T (Join T₁ T₂))

canonical-comp d T = SCoh T (canonical-type d T) (id-label-wt T)

canonical-comp′ zero T = canonical-comp zero T
canonical-comp′ (suc d) Sing = canonical-comp (suc d) Sing
canonical-comp′ (suc d) (Join T Sing) = SExt (canonical-comp′ d T)
canonical-comp′ (suc d) T@(Join _ (Join _ _)) = canonical-comp (suc d) T

canonical-comp-term d T = stm-to-term (canonical-comp d T)

instance
  canonical-dim : {d : ℕ} → {T : Tree n} → has-dim d (canonical-type d T)
  canonical-dim {d = zero} {T} = tt
  canonical-dim {d = suc d} {T} = inst

canonical-label : (S : Tree n) → .⦃ is-linear S ⦄ → (T : Tree m) → Label (someTree T) S
canonical-label S T
  = stm-to-label S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T)
