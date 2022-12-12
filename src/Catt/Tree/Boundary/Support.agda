module Catt.Tree.Boundary.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Support
open import Catt.Tree
open import Catt.Tree.Support
open import Catt.Tree.Path
open import Catt.Tree.Label
open import Catt.Tree.Label.Support
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Tactic.MonoidSolver

tree-inc-label-supp′ : (d : ℕ) → (S : Tree n) → (b : Bool) → FVLabel′ (fromPath ∘ tree-inc-label′ d S b) ≡ supp-tree-bd d S b
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
  VSJoin true (supp-tree-bd d S b) (supp-tree-bd (suc d) T b) ∎
  where
    open ≡-Reasoning

tree-inc-label-supp : (d : ℕ) → (S : Tree n) → (b : Bool) → FVLabel-WT (tree-inc-label d S b) ≡ supp-tree-bd d S b
tree-inc-label-supp d S b = begin
  tEmp ∪t FVLabel′ (λ P → fromPath (tree-inc-label′ d S b P))
    ≡⟨ ∪t-left-unit (FVLabel (λ x → SPath (tree-inc-label′ d S b x))) ⟩
  FVLabel (SPath ∘ tree-inc-label′ d S b)
    ≡⟨ tree-inc-label-supp′ d S b ⟩
  supp-tree-bd d S b ∎
  where
    open ≡-Reasoning

supp-tree-bd-fst : (d : ℕ) → (S : Tree n) → (b : Bool) → Truth (tvarset-fst (supp-tree-bd (suc d) S b))
supp-tree-bd-fst d Sing b = tt
supp-tree-bd-fst d (Join S T) b = tt

DCT-supp-tree-bd : (d : ℕ) → (S : Tree n) → (b : Bool) → DCT (supp-tree-bd d S b) ≡ supp-tree-bd d S b
DCT-supp-tree-bd zero S false = DCT-fst S
DCT-supp-tree-bd zero S true = DCT-last-path S
DCT-supp-tree-bd (suc d) Sing b = refl
DCT-supp-tree-bd (suc d) (Join S T) b
  rewrite Truth-prop (supp-tree-bd-non-empty d S b)
  = cong₂ (VSJoin true) (DCT-supp-tree-bd d S b) (begin
    set-fst-true (DCT (supp-tree-bd (suc d) T b))
      ≡⟨ cong set-fst-true (DCT-supp-tree-bd (suc d) T b) ⟩
    set-fst-true (supp-tree-bd (suc d) T b)
      ≡⟨ tvarset-fst-set-fst (supp-tree-bd (suc d) T b) (supp-tree-bd-fst d T b) ⟩
    supp-tree-bd (suc d) T b ∎)
    where open ≡-Reasoning
