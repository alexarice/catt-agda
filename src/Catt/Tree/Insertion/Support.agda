open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Insertion.Support {index : Set}
                                      (rule : index → Rule)
                                      (lift-rule : ∀ i → P.LiftRule rule (rule i))
                                      (susp-rule : ∀ i → P.SuspRule rule (rule i))
                                      (sub-rule : ∀ i → P.SubRule rule (rule i))
                                      (supp-rule : ∀ i → P.SupportRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Connection.Support
open import Catt.Connection.Properties
open import Catt.Suspension.Support
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Connection
open import Catt.Suspension
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Variables
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Catt.Tree.Pasting
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Label.Support
open import Catt.Tree.Label.Support.Typed rule lift-rule susp-rule sub-rule supp-rule
open import Catt.Tree.Unbiased.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Insertion.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Path
open import Catt.Tree.Label.Properties

exterior-sub-full : (S : Tree n)
                  → (p : BranchingPoint S d)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height d T ⦄
                  → DCT (FVLabel (exterior-sub-label S p T)) ≡ tFull
exterior-sub-full (Join S₁ S₂) BPHere T = label-between-connect-trees-full (label-from-linear-tree-unbiased (suspTree S₁) T 0) (id-label S₂) refl≈stm refl≈stm (label-from-linear-tree-unbiased-full (suspTree S₁) T 0) (trans (cong DCT (id-label-full S₂)) DCT-full)
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
  toVarSet (FVLabel (label-comp (ap (tree-inc-label d S b)) (exterior-sub-label S p T ,, S⋆)))
    ≡˘⟨ DCT-toVarSet (FVLabel (label-comp (ap (tree-inc-label d S b)) (exterior-sub-label S p T ,, S⋆))) ⟩
  toVarSet
    (DCT
     (FVLabel
      (label-comp (proj₁ (tree-inc-label d S b))
       (exterior-sub-label S p T ,, S⋆))))
    ≡⟨ cong toVarSet (lem (Bd-Conditions-one-of d p T)) ⟩
  toVarSet (supp-tree-bd d (insertion-tree S p T) b) ∎
  where
    open ≡-Reasoning

    lem : Bd-Conditions d p T → DCT
            (FVLabel
             (label-comp (proj₁ (tree-inc-label d S b))
              (exterior-sub-label S p T ,, S⋆)))
            ≡ supp-tree-bd d (insertion-tree S p T) b
    lem (Bd-Cond1 x y) = begin
      DCT
        (FVLabel
         (label-comp (ap (tree-inc-label d S b))
          (exterior-sub-label S p T ,, S⋆)))
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
         (label-comp (ap (tree-inc-label d S b))
          (exterior-sub-label S p T ,, S⋆)))
        ≡⟨ EqSuppLabel (label-max-equality-to-equality (unbiased-exterior-comm-2 S p T d b q x) (label-comp-Ty (tree-inc-Ty d S b) (exterior-sub-label-Ty S p T q) TySStar) (label-comp-Ty (exterior-sub-label-Ty (tree-bd d S) (bd-branching-point S p d _) (tree-bd d T) ⦃ _ ⦄ ((≤-trans (≤-reflexive (tree-dim-bd d T))
                      (≤-trans (⊓-monoʳ-≤ d q)
                               (≤-reflexive (sym (bd-branching-point-height S p d (bd-bp-lem p x)))))))) (label-≃-Ty (insertion-bd-2 S p T d (bd-bp-lem p x)) (tree-inc-Ty d (insertion-tree S p T) b)) TySStar)) ⟩
      DCT
        (FVLabel
          (label-comp (exterior-sub-label (tree-bd d S)
                                                              (bd-branching-point S p d (bd-bp-lem p x))
                                                              (tree-bd d T)
                                                              ⦃ bd-has-linear-height d _ T (bd-bp-lem p x) ⦄)
                                          (label-wt-≃ (insertion-bd-2 S p T d (bd-bp-lem p x)) (tree-inc-label d (insertion-tree S p T) b))))
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

-- insertion-tree-dim : (S : Tree n)
--                    → (P : Path S)
--                    → .⦃ _ : is-branching-path P ⦄
--                    → (T : Tree m)
--                    → .⦃ _ : has-linear-height (path-length P) T ⦄
--                    → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
--                    → tree-dim S ≡ tree-dim (insertion-tree S P T)
-- insertion-tree-dim (Join S₁ S₂) PHere T ⦃ p = p ⦄ = begin
--   suc (pred (tree-dim S₂) ⊔ tree-dim S₁)
--     ≡˘⟨ ⊔-lem (tree-dim S₁) (tree-dim S₂) ⟩
--   suc (tree-dim S₁) ⊔ tree-dim S₂
--     ≡⟨ cong (_⊔ tree-dim S₂) it ⟩
--   tree-dim T ⊔ tree-dim S₂
--     ≡˘⟨ connect-tree-dim T S₂ ⟩
--   tree-dim (connect-tree T S₂) ∎
--   where
--     open ≡-Reasoning
-- insertion-tree-dim (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = cong (λ - → suc (pred (tree-dim S₂) ⊔ -)) (insertion-tree-dim S₁ P T ⦃ p = cong pred p ⦄)
-- insertion-tree-dim (Join S₁ S₂) (PShift P) T ⦃ p = p ⦄ = cong (λ - → suc (pred - ⊔ tree-dim S₁)) (insertion-tree-dim S₂ P T)

-- exterior-sub-preserve-bd : (d : ℕ)
--                          → (S : Tree n)
--                          → (P : Path S)
--                          → .⦃ _ : is-branching-path P ⦄
--                          → (T : Tree m)
--                          → .⦃ _ : has-linear-height (path-length P) T ⦄
--                          → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
--                          → (b : Bool)
--                          → TransportVarSet (supp-tree-bd d S b) (exterior-sub S P T)
--                          ≡ supp-tree-bd d (insertion-tree S P T) b
-- exterior-sub-preserve-bd zero S P T false = begin
--   TransportVarSet (FVTm (Var (fromℕ _))) (exterior-sub S P T)
--     ≡⟨ TransportVarSet-tm (Var (fromℕ _)) (exterior-sub S P T) ⟩
--   FVTm (Var (fromℕ _) [ exterior-sub S P T ]tm)
--        ≡˘⟨ cong FVTm (≃tm-to-≡ (exterior-sub-fst-var S P T)) ⟩
--   FVTm (Var (fromℕ _))
--     ≡⟨⟩
--   trueAt (fromℕ (insertion-tree-size S P T)) ∎
--   where
--     open ≡-Reasoning
-- exterior-sub-preserve-bd zero S P T true = let
--   instance _ = tree-last-var-is-var S
--   in begin
--   -- TransportVarSet (trueAt (getVarFin (tree-last-var S))) (exterior-sub S P T)
--   --   ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (isVar-supp (tree-last-var S)) ⟩
--   TransportVarSet (FVTm (tree-last-var S)) (exterior-sub S P T)
--     ≡⟨ TransportVarSet-tm (tree-last-var S) (exterior-sub S P T) ⟩
--   FVTm (tree-last-var S [ exterior-sub S P T ]tm)
--     ≡˘⟨ cong FVTm (≃tm-to-≡ (exterior-sub-last-var S P T)) ⟩
--   FVTm (tree-last-var (insertion-tree S P T))
--     ≡⟨⟩
--     -- ≡⟨ isVar-supp (tree-last-var (insertion-tree S P T)) ⦃ tree-last-var-is-var (insertion-tree S P T) ⦄ ⟩
--   supp-tree-bd zero (insertion-tree S P T) true ∎
--   where
--     open ≡-Reasoning
-- exterior-sub-preserve-bd (suc d) (Join S₁ S₂) PHere T b = begin
--   TransportVarSet (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--     (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
--     ∘ sub-between-connects (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
--                            idSub
--                            (tree-last-var T))
--     ≡⟨ TransportVarSet-comp (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b)) (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
--                            idSub
--                            (tree-last-var T)) ⟩
--   TransportVarSet
--     (TransportVarSet
--      (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--      (sub-between-connects
--       (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
--       (tree-last-var T)))
--     (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
--     ≡⟨ cong (λ - → TransportVarSet - (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))))
--          lem ⟩
--   TransportVarSet
--     (connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b))
--     (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)))
--     ≡⟨ connect-tree-to-ctx-supp d T S₂ b ⟩
--   supp-tree-bd (suc d) (connect-tree T S₂) b ∎
--   where
--     l1 : Var (fromℕ _) [ connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub ]tm
--            ≃tm
--          getSnd [ connect-inc-left (tree-last-var T) (tree-size S₂)
--                 ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
--     l1 = begin
--       < Var (fromℕ _) [ connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub ]tm >tm
--         ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ _)}) (id-right-unit (connect-inc-right (tree-last-var T) (tree-size S₂))) ⟩
--       < Var (fromℕ _) [ connect-inc-right (tree-last-var T) _ ]tm >tm
--         ≈˘⟨ connect-inc-fst-var (tree-last-var T) (tree-size S₂) ⟩
--       < tree-last-var T [ connect-inc-left (tree-last-var T) (tree-size S₂) ]tm >tm
--         ≈⟨ sub-action-≃-tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1)) refl≃s ⟩
--       < getSnd [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
--                [ connect-inc-left (tree-last-var T) (tree-size S₂) ]tm >tm
--         ≈˘⟨ assoc-tm (connect-inc-left (tree-last-var T) (tree-size S₂)) (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd ⟩
--       < getSnd [ connect-inc-left (tree-last-var T) (tree-size S₂)
--                ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm >tm ∎
--       where
--         open Reasoning tm-setoid

--     l2 : FVTm (tree-last-var T) ⊆
--            TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
--            (unrestrict (sub-from-linear-tree-unbiased S₁ T 1))
--     l2 = begin
--       FVTm (tree-last-var T)
--         ≤⟨ supp-tree-bd-include-last d T b ⟩
--       supp-tree-bd (suc d) T b
--         ≡˘⟨ sub-from-linear-tree-supp (suc d) (suspTree S₁) b T (sym it) ⟩
--       TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
--         (sub-from-linear-tree-unbiased (suspTree S₁) T 0) ∎
--       where
--         open PReasoning (⊆-poset (suc _))

--     open ≡-Reasoning

--     lem : TransportVarSet
--      (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--      (sub-between-connects
--       (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
--       (tree-last-var T)) ≡ connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b)
--     lem = begin
--       TransportVarSet
--         (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--         (sub-between-connects
--          (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub
--          (tree-last-var T))
--         ≡⟨ sub-between-connect-Transport (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)) idSub (tree-last-var T) (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b) getSnd l1 (suspSuppSndTruth (supp-tree-bd d S₁ b)) l2 ⟩
--       connect-supp
--         (TransportVarSet (suspSupp (supp-tree-bd d S₁ b))
--          (unrestrict (sub-from-linear-tree-unbiased S₁ T 1)))
--         (TransportVarSet (supp-tree-bd (suc d) S₂ b) idSub)
--         ≡⟨ cong₂ connect-supp (sub-from-linear-tree-supp (suc d) (suspTree S₁) b T (sym it)) (TransportVarSet-id (supp-tree-bd (suc d) S₂ b)) ⟩
--       connect-supp (supp-tree-bd (suc d) T b) (supp-tree-bd (suc d) S₂ b) ∎

-- exterior-sub-preserve-bd (suc d) (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ b = begin
--   TransportVarSet
--       (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--       (sub-between-connect-susps (exterior-sub S₁ P T)
--        idSub)
--     ≡⟨ sub-between-connect-susps-Transport (exterior-sub S₁ P T) idSub (supp-tree-bd d S₁ b) (supp-tree-bd (suc d) S₂ b) (id-on-tm (Var (fromℕ _))) ⟩
--   connect-supp
--     (suspSupp (TransportVarSet (supp-tree-bd d S₁ b) (exterior-sub S₁ P T)))
--     (TransportVarSet (supp-tree-bd (suc d) S₂ b) idSub)
--     ≡⟨ cong₂ (λ a → connect-supp (suspSupp a)) (exterior-sub-preserve-bd d S₁ P T ⦃ p = cong pred p ⦄ b) (TransportVarSet-id (supp-tree-bd (suc d) S₂ b)) ⟩
--   connect-supp (suspSupp (supp-tree-bd d (insertion-tree S₁ P T) b))
--       (supp-tree-bd (suc d) S₂ b) ∎
--   where
--     open ≡-Reasoning
-- exterior-sub-preserve-bd (suc d) (Join S₁ S₂) (PShift P) T b = begin
--   TransportVarSet
--       (connect-supp (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b))
--       (sub-between-connect-susps
--        idSub (exterior-sub S₂ P T))
--     ≡⟨ sub-between-connect-susps-Transport idSub (exterior-sub S₂ P T) (supp-tree-bd d S₁ b) (supp-tree-bd (suc d) S₂ b) (sym≃tm (exterior-sub-fst-var S₂ P T)) ⟩
--   connect-supp
--     (suspSupp (TransportVarSet (supp-tree-bd d S₁ b) idSub))
--     (TransportVarSet (supp-tree-bd (suc d) S₂ b) (exterior-sub S₂ P T))
--     ≡⟨ cong₂ (λ a → connect-supp (suspSupp a)) (TransportVarSet-id (supp-tree-bd d S₁ b)) (exterior-sub-preserve-bd (suc d) S₂ P T b) ⟩
--   connect-supp (suspSupp (supp-tree-bd d S₁ b))
--       (supp-tree-bd (suc d) (insertion-tree S₂ P T) b) ∎
--   where
--     open ≡-Reasoning

-- exterior-sub-supp-full : (S : Tree n)
--                        → (P : Path S)
--                        → .⦃ _ : is-branching-path P ⦄
--                        → (T : Tree m)
--                        → .⦃ _ : has-linear-height (path-length P) T ⦄
--                        → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
--                        → FVSub (exterior-sub S P T) ≡ full
-- exterior-sub-supp-full S P T = begin
--   FVSub (exterior-sub S P T)
--     ≡˘⟨ TransportVarSet-full (exterior-sub S P T) ⟩
--   TransportVarSet full (exterior-sub S P T)
--     ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (supp-tree-bd-full (tree-dim S) S false ≤-refl) ⟩
--   TransportVarSet (supp-tree-bd (tree-dim S) S false) (exterior-sub S P T)
--     ≡⟨ exterior-sub-preserve-bd (tree-dim S) S P T false ⟩
--   supp-tree-bd (tree-dim S) (insertion-tree S P T) false
--     ≡⟨ supp-tree-bd-full (tree-dim S) (insertion-tree S P T) false (≤-reflexive (sym (insertion-tree-dim S P T))) ⟩
--   full ∎
--   where
--     open ≡-Reasoning


-- insertion-supp-condition : (b : Bool)
--                          → (A : Ty (suc n))
--                          → (S : Tree n)
--                          → (P : Path S)
--                          → .⦃ _ : is-branching-path P ⦄
--                          → (T : Tree m)
--                          → .⦃ _ : has-linear-height (path-length P) T ⦄
--                          → ⦃ p : height-of-branching P ≡ tree-dim T ⦄
--                          → supp-condition b A (tree-to-ctx S) ⦃ tree-to-pd S ⦄
--                          → supp-condition b (A [ exterior-sub S P T ]ty) (tree-to-ctx (insertion-tree S P T)) ⦃ tree-to-pd (insertion-tree S P T) ⦄
-- insertion-supp-condition false A S P T sc = begin
--   FVTy (A [ exterior-sub S P T ]ty)
--     ≡˘⟨ TransportVarSet-ty A (exterior-sub S P T) ⟩
--   TransportVarSet (FVTy A) (exterior-sub S P T)
--     ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc ⟩
--   TransportVarSet full (exterior-sub S P T)
--     ≡⟨ TransportVarSet-full (exterior-sub S P T) ⟩
--   FVSub (exterior-sub S P T)
--     ≡⟨ exterior-sub-supp-full S P T ⟩
--   full ∎
--   where
--     open ≡-Reasoning
-- insertion-supp-condition true (s ─⟨ A ⟩⟶ t) S P T ⦃ p = p ⦄ (nz ,, sc1 ,, sc2)
--   = NonZero-subst lem nz ,, trans l1 (supp-pred-compat (insertion-tree S P T) false) ,, trans l2 (supp-pred-compat (insertion-tree S P T) true)
--   where
--     open ≡-Reasoning
--     instance _ = tree-to-pd S

--     lem : ctx-dim (tree-to-ctx S) ≡ ctx-dim (tree-to-ctx (insertion-tree S P T))
--     lem = begin
--       ctx-dim (tree-to-ctx S)
--         ≡⟨ tree-dim-ctx-dim S ⟩
--       tree-dim S
--         ≡⟨ insertion-tree-dim S P T ⟩
--       tree-dim (insertion-tree S P T)
--         ≡˘⟨ tree-dim-ctx-dim (insertion-tree S P T) ⟩
--       ctx-dim (tree-to-ctx (insertion-tree S P T)) ∎

--     l1 : FVTy (A [ exterior-sub S P T ]ty) ∪
--            FVTm (s [ exterior-sub S P T ]tm)
--            ≡
--            supp-tree-bd (pred (tree-dim (insertion-tree S P T)))
--            (insertion-tree S P T) false
--     l1 = begin
--       FVTy (A [ exterior-sub S P T ]ty) ∪
--         FVTm (s [ exterior-sub S P T ]tm)
--         ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm s (exterior-sub S P T)) ⟩
--       TransportVarSet (FVTy A) (exterior-sub S P T) ∪
--         TransportVarSet (FVTm s) (exterior-sub S P T)
--         ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm s) (exterior-sub S P T) ⟩
--       TransportVarSet (FVTy A ∪ FVTm s) (exterior-sub S P T)
--         ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc1 ⟩
--       TransportVarSet
--         (pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) false)
--         (exterior-sub S P T)
--         ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (supp-pred-compat S false) ⟩
--       TransportVarSet (supp-tree-bd (pred (tree-dim S)) S false) (exterior-sub S P T)
--         ≡⟨ exterior-sub-preserve-bd (pred (tree-dim S)) S P T false ⟩
--       supp-tree-bd (pred (tree-dim S)) (insertion-tree S P T) false
--         ≡⟨ cong (λ - → supp-tree-bd (pred -) (insertion-tree S P T) false) (insertion-tree-dim S P T) ⟩
--       supp-tree-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) false ∎

--     l2 : FVTy (A [ exterior-sub S P T ]ty) ∪
--            FVTm (t [ exterior-sub S P T ]tm)
--            ≡
--            supp-tree-bd (pred (tree-dim (insertion-tree S P T)))
--            (insertion-tree S P T) true
--     l2 = begin
--       FVTy (A [ exterior-sub S P T ]ty) ∪
--         FVTm (t [ exterior-sub S P T ]tm)
--         ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty A (exterior-sub S P T)) (TransportVarSet-tm t (exterior-sub S P T)) ⟩
--       TransportVarSet (FVTy A) (exterior-sub S P T) ∪
--         TransportVarSet (FVTm t) (exterior-sub S P T)
--         ≡˘⟨ TransportVarSet-∪ (FVTy A) (FVTm t) (exterior-sub S P T) ⟩
--       TransportVarSet (FVTy A ∪ FVTm t) (exterior-sub S P T)
--         ≡⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) sc2 ⟩
--       TransportVarSet
--         (pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) true)
--         (exterior-sub S P T)
--         ≡˘⟨ cong (λ - → TransportVarSet - (exterior-sub S P T)) (supp-pred-compat S true) ⟩
--       TransportVarSet (supp-tree-bd (pred (tree-dim S)) S true) (exterior-sub S P T)
--         ≡⟨ exterior-sub-preserve-bd (pred (tree-dim S)) S P T true ⟩
--       supp-tree-bd (pred (tree-dim S)) (insertion-tree S P T) true
--         ≡⟨ cong (λ - → supp-tree-bd (pred -) (insertion-tree S P T) true) (insertion-tree-dim S P T) ⟩
--       supp-tree-bd (pred (tree-dim (insertion-tree S P T))) (insertion-tree S P T) true ∎
