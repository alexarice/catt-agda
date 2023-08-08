open import Catt.Typing.Rule

module Catt.Tree.Insertion.Support {index : Set}
                                      (rule : index → Rule)
                                      (lift-rule : ∀ i → LiftRule rule (rule i))
                                      (susp-rule : ∀ i → SuspRule rule (rule i))
                                      (sub-rule : ∀ i → SubRule rule (rule i))
                                      (supp-rule : ∀ i → SupportRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Structured.Typing rule
open import Catt.Tree.Structured.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Insertion.Typing rule lift-rule susp-rule sub-rule

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Connection.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Unbiased.Support

open import Catt.Tree.Structured.Support.Typed rule lift-rule susp-rule sub-rule supp-rule

exterior-sub-full : (S : Tree n)
                  → (p : BranchingPoint S d)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height d T ⦄
                  → DCT (FVLabel (exterior-sub-label S p T)) ≡ tFull
exterior-sub-full (Join S₁ S₂) BPHere T = label-between-connect-trees-full (label-from-linear-tree-unbiased (susp-tree S₁) T 0) (id-label S₂) refl≈stm refl≈stm (label-from-linear-tree-unbiased-full (susp-tree S₁) T 0) (trans (cong DCT (id-label-full S₂)) DCT-full)
exterior-sub-full (Join S₁ S₂) (BPExt p) (Join T Sing) = label-between-joins-full (exterior-sub-label S₁ p T) (id-label S₂) (exterior-sub-full S₁ p T) (trans (cong DCT (id-label-full S₂)) DCT-full)
exterior-sub-full (Join S₁ S₂) (BPShift p) T = label-between-joins-full (id-label S₁) (exterior-sub-label S₂ p T) (trans (cong DCT (id-label-full S₁)) DCT-full) (exterior-sub-full S₂ p T)

exterior-sub-boundary-supp : (S : Tree n)
                  → (p : BranchingPoint S d)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height d T ⦄
                  → (q : height-of-branching p ≥ tree-dim T)
                  → (d : ℕ)
                  → (b : Bool)
                  → TransportVarSet-Label (supp-tree-bd d S b) (exterior-sub-label S p T) ≡ toVarSet (supp-tree-bd d (insertion-tree S p T) b)
exterior-sub-boundary-supp S p T q d b = begin
  TransportVarSet-Label (supp-tree-bd d S b)
    (exterior-sub-label S p T)
    ≡˘⟨ cong (λ a → TransportVarSet-Label a (exterior-sub-label S p T)) (trans (sym (FVLabel-WT-⋆ (ap (tree-inc-label d S b)))) (tree-inc-label-supp d S b)) ⟩
  TransportVarSet-Label (FVLabel (ap (tree-inc-label d S b)))
    (exterior-sub-label S p T)
    ≡˘⟨ TransportVarSet-Label-Label (ap (tree-inc-label d S b)) (exterior-sub-label S p T) (exterior-sub-label-Ty S p T q) ⟩
  toVarSet (FVLabel (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆)))
    ≡˘⟨ DCT-toVarSet (FVLabel (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆))) ⟩
  toVarSet
    (DCT
     (FVLabel
      (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆))))
    ≡⟨ cong toVarSet (lem (Bd-Conditions-one-of d p T)) ⟩
  toVarSet (supp-tree-bd d (insertion-tree S p T) b) ∎
  where
    open ≡-Reasoning

    lem : Bd-Conditions d p T → DCT
            (FVLabel
             (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆)))
            ≡ supp-tree-bd d (insertion-tree S p T) b
    lem (Bd-Cond1 x y) = begin
      DCT
        (FVLabel
         (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆)))
        ≡⟨ EqSuppLabel (label-max-equality-to-equality (unbiased-exterior-comm-1 S p T d x y q b) (label-comp-Ty (tree-inc-Ty d S b) (exterior-sub-label-Ty S p T q) TySStar) (label-≃-Ty (insertion-bd-1 S p T d y q) (tree-inc-Ty d (insertion-tree S p T) b))) ⟩
      DCT
        (FVLabel
         (label-≃ (insertion-bd-1 S p T d y q) (ap (tree-inc-label d (insertion-tree S p T) b))))
        ≡⟨ FV-label-comp-full (SPath ∘ (ppath-≃ (insertion-bd-1 S p T d y q))) (ap (tree-inc-label d (insertion-tree S p T) b)) (tree-inc-Ty d (insertion-tree S p T) b) (trans (cong DCT (ppath-≃-full (insertion-bd-1 S p T d y q))) DCT-full) ⟩
      DCT (FVLabel (ap (tree-inc-label d (insertion-tree S p T) b)))
        ≡˘⟨ cong DCT (FVLabel-WT-⋆ (ap (tree-inc-label d (insertion-tree S p T) b))) ⟩
      DCT (FVLabel-WT (tree-inc-label d (insertion-tree S p T) b))
        ≡⟨ cong DCT (tree-inc-label-supp d (insertion-tree S p T) b) ⟩
      DCT (supp-tree-bd d (insertion-tree S p T) b)
        ≡⟨ DCT-supp-tree-bd d (insertion-tree S p T) b ⟩
      supp-tree-bd d (insertion-tree S p T) b ∎
    lem (Bd-Cond2 x) = begin
      DCT
        (FVLabel
         (ap (tree-inc-label d S b) ●l (exterior-sub-label S p T ,, S⋆)))
        ≡⟨ EqSuppLabel (label-max-equality-to-equality (unbiased-exterior-comm-2 S p T d b q x) (label-comp-Ty (tree-inc-Ty d S b) (exterior-sub-label-Ty S p T q) TySStar) (label-comp-Ty (exterior-sub-label-Ty (tree-bd d S) (bd-branching-point S p d _) (tree-bd d T) ⦃ _ ⦄ ((≤-trans (≤-reflexive (tree-dim-bd d T))
                      (≤-trans (⊓-monoʳ-≤ d q)
                               (≤-reflexive (sym (bd-branching-point-height S p d (bd-bp-lem p x)))))))) (label-≃-Ty (insertion-bd-2 S p T d (bd-bp-lem p x)) (tree-inc-Ty d (insertion-tree S p T) b)) TySStar)) ⟩
      DCT
        (FVLabel
          (exterior-sub-label (tree-bd d S)
                              (bd-branching-point S p d (bd-bp-lem p x))
                              (tree-bd d T)
                              ⦃ bd-has-linear-height d _ T (bd-bp-lem p x) ⦄
          ●l (label-wt-≃ (insertion-bd-2 S p T d (bd-bp-lem p x)) (tree-inc-label d (insertion-tree S p T) b))))
        ≡⟨ FV-label-comp-full (exterior-sub-label (tree-bd d S)
                                                              (bd-branching-point S p d (bd-bp-lem p x))
                                                              (tree-bd d T)
                                                              ⦃ _ ⦄) (label-≃ (insertion-bd-2 S p T d _)
                                                                       (proj₁ (tree-inc-label d (insertion-tree S p T) b))) (label-≃-Ty (insertion-bd-2 S p T d (bd-bp-lem p x)) (tree-inc-Ty d (insertion-tree S p T) b)) (exterior-sub-full (tree-bd d S) (bd-branching-point S p d (bd-bp-lem p x)) (tree-bd d T) ⦃ _ ⦄) ⟩
      DCT
        (FVLabel
         (label-≃ (insertion-bd-2 S p T d _)
          (ap (tree-inc-label d (insertion-tree S p T) b))))
        ≡⟨ FV-label-comp-full (SPath ∘ ppath-≃ (insertion-bd-2 S p T d _)) (ap (tree-inc-label d (insertion-tree S p T) b)) (tree-inc-Ty d (insertion-tree S p T) b) (trans (cong DCT (ppath-≃-full (insertion-bd-2 S p T d _))) DCT-full) ⟩
      DCT (FVLabel (ap (tree-inc-label d (insertion-tree S p T) b)))
        ≡˘⟨ cong DCT (FVLabel-WT-⋆ (ap (tree-inc-label d (insertion-tree S p T) b))) ⟩
      DCT (FVLabel-WT (tree-inc-label d (insertion-tree S p T) b))
        ≡⟨ cong DCT (tree-inc-label-supp d (insertion-tree S p T) b) ⟩
      DCT (supp-tree-bd d (insertion-tree S p T) b)
        ≡⟨ DCT-supp-tree-bd d (insertion-tree S p T) b ⟩
      supp-tree-bd d (insertion-tree S p T) b ∎
