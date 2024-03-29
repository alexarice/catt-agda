module Deprecated.Tree.Boundary.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties

open import Catt.Support
open import Deprecated.Tree.Support
open import Deprecated.Tree.Structured.Support
open import Deprecated.Tree.Structured.Support.Properties

open import Tactic.MonoidSolver

tree-inc-label-supp′ : (d : ℕ) → (S : Tree n) → (b : Bool) → FVLabel′ (fromPath ∘ tree-inc-label′ d S b) ≡ tree-bd-vs d S b
tree-inc-label-supp′ zero S false = refl
tree-inc-label-supp′ zero S true = refl
tree-inc-label-supp′ (suc d) Sing b = refl
tree-inc-label-supp′ (suc d) (Join S T) b = begin
  VSJoin true tEmp tEmp
  ∪t FVLabel′ (λ x → VSJoin false (fromPath (tree-inc-label′ d S b x)) tEmp)
  ∪t FVLabel′ (λ x → VSJoin false tEmp (fromPath (tree-inc-label′ (suc d) T b x)))
    ≡⟨ cong₂ (λ a b → VSJoin true tEmp tEmp ∪t a ∪t b)
             (FVLabel′-map (fromPath ∘ tree-inc-label′ d S b) (λ a → VSJoin false a tEmp) λ xs ys → cong (VSJoin false (xs ∪t ys)) (sym (∪t-left-unit tEmp)))
             (FVLabel′-map (fromPath ∘ tree-inc-label′ (suc d) T b) (VSJoin false tEmp) (λ xs ys → cong (λ a → VSJoin false a (xs ∪t ys)) (sym (∪t-left-unit tEmp)))) ⟩
  VSJoin true (tEmp ∪t FVLabel′ (fromPath ∘ tree-inc-label′ d S b) ∪t tEmp)
              (tEmp ∪t tEmp ∪t FVLabel′ (fromPath ∘ tree-inc-label′ (suc d) T b))
    ≡⟨ cong₂ (VSJoin true) (solve (∪t-monoid {S = S})) (solve (∪t-monoid {S = T})) ⟩
  VSJoin true (FVLabel′ (fromPath ∘ tree-inc-label′ d S b))
              (FVLabel′ (fromPath ∘ tree-inc-label′ (suc d) T b))
    ≡⟨ cong₂ (VSJoin true) (tree-inc-label-supp′ d S b) (tree-inc-label-supp′ (suc d) T b) ⟩
  VSJoin true (tree-bd-vs d S b) (tree-bd-vs (suc d) T b) ∎
  where
    open ≡-Reasoning

tree-inc-label-supp : (d : ℕ) → (S : Tree n) → (b : Bool) → FVLabel-WT (tree-inc-label d S b) ≡ tree-bd-vs d S b
tree-inc-label-supp d S b = begin
  tEmp ∪t FVLabel′ (λ P → fromPath (tree-inc-label′ d S b P))
    ≡⟨ ∪t-left-unit (FVLabel (λ x → SPath (tree-inc-label′ d S b x))) ⟩
  FVLabel (SPath ∘ tree-inc-label′ d S b)
    ≡⟨ tree-inc-label-supp′ d S b ⟩
  tree-bd-vs d S b ∎
  where
    open ≡-Reasoning

tree-bd-vs-fst : (d : ℕ) → (S : Tree n) → (b : Bool) → Truth (tvarset-fst (tree-bd-vs (suc d) S b))
tree-bd-vs-fst d Sing b = tt
tree-bd-vs-fst d (Join S T) b = tt

DCT-tree-bd-vs : (d : ℕ) → (S : Tree n) → (b : Bool) → DCT (tree-bd-vs d S b) ≡ tree-bd-vs d S b
DCT-tree-bd-vs zero S false = DCT-fst S
DCT-tree-bd-vs zero S true = DCT-last-path S
DCT-tree-bd-vs (suc d) Sing b = refl
DCT-tree-bd-vs (suc d) (Join S T) b
  rewrite Truth-prop (tree-bd-vs-non-empty d S b)
  = cong₂ (VSJoin true) (DCT-tree-bd-vs d S b) (begin
    set-fst-true (DCT (tree-bd-vs (suc d) T b))
      ≡⟨ cong set-fst-true (DCT-tree-bd-vs (suc d) T b) ⟩
    set-fst-true (tree-bd-vs (suc d) T b)
      ≡⟨ tvarset-fst-set-fst (tree-bd-vs (suc d) T b) (tree-bd-vs-fst d T b) ⟩
    tree-bd-vs (suc d) T b ∎)
    where open ≡-Reasoning

tree-bd-vs-full : (d : ℕ) → (S : Tree n) → (b : Bool) → (tree-dim S ≤ d) → tree-bd-vs d S b ≡ tFull
tree-bd-vs-full zero Sing false p = refl
tree-bd-vs-full zero Sing true p = refl
tree-bd-vs-full (suc d) Sing b p = refl
tree-bd-vs-full (suc d) (Join S T) b p
  = cong₂ (VSJoin true)
          (tree-bd-vs-full d S b (≤-trans (m≤n⊔m (pred (tree-dim T)) (tree-dim S)) (≤-pred p)))
          (tree-bd-vs-full (suc d) T b (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))
