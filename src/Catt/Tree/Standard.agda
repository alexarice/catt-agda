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

standard-sty : (d : ℕ) → (T : Tree n) → STy (someTree T)
standard-stm : (d : ℕ) → (T : Tree n) → STm (someTree T)
standard-coh : (d : ℕ) → (T : Tree n) → STm (someTree T)
standard-coh′ : (d : ℕ) → (T : Tree n) → STm (someTree T)

standard-sty zero T = S⋆
standard-sty (suc d) T = SArr (standard-stm d (tree-bd d T) >>= tree-inc-label d T false) (standard-sty d T) (standard-stm d (tree-bd d T) >>= tree-inc-label d T true)

standard-stm zero Sing = SHere
standard-stm zero (Join S T) = standard-coh zero (Join S T)
standard-stm (suc d) Sing = standard-coh (suc d) Sing
standard-stm (suc d) (Susp T) = SExt (standard-stm d T)
standard-stm (suc d) (Join T (Join T₁ T₂)) = standard-coh (suc d) (Join T (Join T₁ T₂))

standard-coh d T = SCoh T (standard-sty d T) (id-label-wt T)

standard-coh′ zero T = standard-coh zero T
standard-coh′ (suc d) Sing = standard-coh (suc d) Sing
standard-coh′ (suc d) (Susp T) = SExt (standard-coh′ d T)
standard-coh′ (suc d) T@(Join _ (Join _ _)) = standard-coh (suc d) T

instance
  standard-dim : {d : ℕ} → {T : Tree n} → has-dim d (standard-sty d T)
  standard-dim {d = zero} {T} = tt
  standard-dim {d = suc d} {T} = inst

standard-label : (S : Tree n) → .⦃ is-linear S ⦄ → (T : Tree m) → Label (someTree T) S
standard-label S T
  = stm-to-label S (standard-coh′ (tree-dim S) T) (standard-sty (tree-dim S) T)
