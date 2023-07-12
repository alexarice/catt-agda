module Catt.Tree.Unbiased.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
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
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Boundary

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Label.Support

open import Tactic.MonoidSolver


supp-unbiased-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b)) ≡ supp-tree-bd d T b
supp-unbiased-comp-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (unbiased-comp d (tree-bd d T) >>= tree-inc-label d T b)) ≡ supp-tree-bd d T b

supp-unbiased-lem zero Sing false = refl
supp-unbiased-lem zero Sing true = refl
supp-unbiased-lem zero (Join S T) false rewrite tEmp-empty S = cong₂ (VSJoin true) DCT-emp DCT-emp
supp-unbiased-lem zero (Join S T) true rewrite tEmp-empty S = cong₂ (VSJoin false) DCT-emp (DCT-last-path T)
supp-unbiased-lem (suc d) Sing b = refl
supp-unbiased-lem (suc d) (Join T Sing) b = begin
  DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) b)))
    ≡⟨ FVSTm-≃ {a = unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) b)}
               {b = susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b)}
               l1 ⟩
  DCT (FVSTm (susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡˘⟨ FVSTm-susp (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) ⟩
  supp-tvarset (DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡⟨ cong supp-tvarset (supp-unbiased-lem d T b) ⟩
  supp-tvarset (supp-tree-bd d T b) ∎
  where
    l1 : (unbiased-stm d (tree-bd d T) >>=
            label₁ (tree-inc-label (suc d) (suspTree T) b))
           ≃stm
           susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b)
    l1 = begin
      < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) b) >stm
        ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] [ refl≃ty ] ⟩
      < unbiased-stm d (tree-bd d T) >>= susp-label (tree-inc-label d T b) >stm
        ≈˘⟨ extend-susp-label (unbiased-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm ∎
      where
        open Reasoning stm-setoid
    open ≡-Reasoning
supp-unbiased-lem (suc d) (Join T (Join T₁ T₂)) b = supp-unbiased-comp-lem (suc d) (Join T (Join T₁ T₂)) b

supp-unbiased-comp-lem d T b = begin
  DCT (FVLabel-WT (tree-inc-label d T b))
    ≡⟨ cong DCT (tree-inc-label-supp d T b) ⟩
  DCT (supp-tree-bd d T b)
    ≡⟨ DCT-supp-tree-bd d T b ⟩
  supp-tree-bd d T b ∎
  where open ≡-Reasoning

unbiased-supp-condition-1 : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≡ d) → supp-condition-s true T (unbiased-type d T)
unbiased-supp-condition-1 (suc d) T p with cong pred p
... | refl = NonZero-subst (sym p) it ,, supp-unbiased-lem (pred (tree-dim T)) T false ,, supp-unbiased-lem (pred (tree-dim T)) T true

unbiased-supp-condition-2 : (d : ℕ) → (T : Tree n) → (tree-dim T < d) → supp-condition-s false T (unbiased-type d T)
unbiased-supp-condition-2 (suc d) T p = begin
  DCT (FVSTy (unbiased-type d T) ∪t
      FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)
      ∪t FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ DCT-∪ _ _ ⟩
  DCT
    (FVSTy (unbiased-type d T) ∪t
     FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false))
    ∪t
    DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (DCT (FVSTy (unbiased-type d T) ∪t
      FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t_) lem ⟩
  DCT (FVSTy (unbiased-type d T) ∪t
      FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t tFull
    ≡⟨ ∪t-right-zero (DCT (FVSTy (unbiased-type d T)
                     ∪t FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false))) ⟩
  tFull ∎
  where
    open ≡-Reasoning
    lem : DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true)) ≡ tFull
    lem = begin
      DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
        ≡⟨ supp-unbiased-lem d T true ⟩
      supp-tree-bd d T true
        ≡⟨ supp-tree-bd-full d T true (≤-pred p) ⟩
      tFull ∎

label-from-linear-tree-unbiased-full : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → DCT (FVLabel (label-from-linear-tree-unbiased S T d)) ≡ tFull
label-from-linear-tree-unbiased-full Sing T d = begin
  DCT (FVSTm (unbiased-comp′ d T))
    ≡⟨ FVSTm-≃ (unbiased-comp′-compat d T) ⟩
  DCT (FVSTm (unbiased-comp d T))
    ≡⟨ cong DCT (∪t-left-unit (FVLabel (id-label T))) ⟩
  DCT (FVLabel (id-label T))
    ≡⟨ cong DCT (id-label-full T) ⟩
  DCT tFull
    ≡⟨ DCT-full ⟩
  tFull ∎
  where
    open ≡-Reasoning
label-from-linear-tree-unbiased-full (Join S Sing) T d = begin
  DCT
      (FVSTm
       (unbiased-stm d (tree-bd d T) >>=
        (tree-inc-label d T false))
       ∪t
       FVLabel (label-from-linear-tree-unbiased S T (suc d))
       ∪t
       FVSTm
       (unbiased-stm d (tree-bd d T) >>=
        (tree-inc-label d T true)))
    ≡⟨ DCT-∪ (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)
               ∪t FVLabel (label-from-linear-tree-unbiased S T (suc d))) (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true)) ⟩
  DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)
     ∪t FVLabel (label-from-linear-tree-unbiased S T (suc d)))
    ∪t
    DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (_∪t _) (DCT-∪ (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)) (FVLabel (label-from-linear-tree-unbiased S T (suc d)))) ⟩
  DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false))
    ∪t DCT (FVLabel (label-from-linear-tree-unbiased S T (suc d)))
    ∪t
    DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (λ a → _ ∪t a ∪t _) (label-from-linear-tree-unbiased-full S T (suc d)) ⟩
  DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)) ∪t tFull ∪t
    DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (_∪t (DCT
    (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true)))) (∪t-right-zero (DCT (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false)))) ⟩
  tFull ∪t DCT
             (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ ∪t-left-zero (DCT
                      (FVSTm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true))) ⟩
  tFull ∎
  where
    open ≡-Reasoning
