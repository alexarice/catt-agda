module Catt.Tree.Canonical.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties
open import Catt.Tree.Boundary

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Support.Properties
open import Catt.Tree.Structured.Construct.Support

open import Tactic.MonoidSolver


supp-canonical-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b)) ≡ supp-tree-bd d T b
supp-canonical-comp-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (canonical-comp d (tree-bd d T) >>= tree-inc-label d T b)) ≡ supp-tree-bd d T b

supp-canonical-lem zero Sing false = refl
supp-canonical-lem zero Sing true = refl
supp-canonical-lem zero (Join S T) false rewrite tEmp-empty S = cong₂ (VSJoin true) DCT-emp DCT-emp
supp-canonical-lem zero (Join S T) true rewrite tEmp-empty S = cong₂ (VSJoin false) DCT-emp (DCT-last-path T)
supp-canonical-lem (suc d) Sing b = refl
supp-canonical-lem (suc d) (Join T Sing) b = begin
  DCT (FVSTm (canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b)))
    ≡⟨ FVSTm-≃ {a = canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b)}
               {b = susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b)}
               l1 ⟩
  DCT (FVSTm (susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡˘⟨ FVSTm-susp (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) ⟩
  supp-tvarset (DCT (FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡⟨ cong supp-tvarset (supp-canonical-lem d T b) ⟩
  supp-tvarset (supp-tree-bd d T b) ∎
  where
    l1 : (canonical-stm d (tree-bd d T) >>=
            label₁ (tree-inc-label (suc d) (susp-tree T) b))
           ≃stm
           susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b)
    l1 = begin
      < canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] [ refl≃ty ] ⟩
      < canonical-stm d (tree-bd d T) >>= susp-label (tree-inc-label d T b) >stm
        ≈˘⟨ >>=-susp-label (canonical-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm ∎
      where
        open Reasoning stm-setoid
    open ≡-Reasoning
supp-canonical-lem (suc d) (Join T (Join T₁ T₂)) b = supp-canonical-comp-lem (suc d) (Join T (Join T₁ T₂)) b

supp-canonical-comp-lem d T b = begin
  DCT (FVLabel-WT (tree-inc-label d T b))
    ≡⟨ cong DCT (tree-inc-label-supp d T b) ⟩
  DCT (supp-tree-bd d T b)
    ≡⟨ DCT-supp-tree-bd d T b ⟩
  supp-tree-bd d T b ∎
  where open ≡-Reasoning

canonical-supp-condition-1 : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≡ d) → supp-condition-s true T (canonical-type d T)
canonical-supp-condition-1 (suc d) T p with cong pred p
... | refl = NonZero-subst (sym p) it ,, supp-canonical-lem (pred (tree-dim T)) T false ,, supp-canonical-lem (pred (tree-dim T)) T true

canonical-supp-condition-2 : (d : ℕ) → (T : Tree n) → (tree-dim T < d) → supp-condition-s false T (canonical-type d T)
canonical-supp-condition-2 (suc d) T p = begin
  DCT (FVSTy (canonical-type d T) ∪t
      FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false)
      ∪t FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ DCT-∪ _ _ ⟩
  DCT
    (FVSTy (canonical-type d T) ∪t
     FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false))
    ∪t
    DCT
    (FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (DCT (FVSTy (canonical-type d T) ∪t
      FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t_) lem ⟩
  DCT (FVSTy (canonical-type d T) ∪t
      FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t tFull
    ≡⟨ ∪t-right-zero (DCT (FVSTy (canonical-type d T)
                     ∪t FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T false))) ⟩
  tFull ∎
  where
    open ≡-Reasoning
    lem : DCT (FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T true)) ≡ tFull
    lem = begin
      DCT (FVSTm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T true))
        ≡⟨ supp-canonical-lem d T true ⟩
      supp-tree-bd d T true
        ≡⟨ supp-tree-bd-full d T true (≤-pred p) ⟩
      tFull ∎

canonical-label-full : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → DCT (FVLabel (canonical-label S T)) ≡ tFull
canonical-label-full S T = begin
  DCT (FVLabel (canonical-label S T))
    ≡⟨ cong DCT (stm-to-label-supp S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T)) ⟩
  DCT (FVSTy (canonical-type (tree-dim S) T) ∪m FVSTm (canonical-comp′ (tree-dim S) T))
    ≡⟨ DCT-∪ (FVSTy (canonical-type (tree-dim S) T)) (FVSTm (canonical-comp′ (tree-dim S) T)) ⟩
  DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t DCT (FVSTm (canonical-comp′ (tree-dim S) T))
    ≡⟨ cong (DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t_) (FVSTm-≃ (canonical-comp′-compat (tree-dim S) T)) ⟩
  DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t DCT (FVSTm (canonical-comp (tree-dim S) T))
    ≡⟨ cong (DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t_) (cong DCT (id-label-wt-full T)) ⟩
  DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t DCT tFull
    ≡⟨ cong (DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t_) DCT-full ⟩
  DCT (FVSTy (canonical-type (tree-dim S) T)) ∪t tFull
    ≡⟨ ∪t-right-zero (DCT (FVSTy (canonical-type (tree-dim S) T))) ⟩
  tFull ∎
  where
    open ≡-Reasoning
