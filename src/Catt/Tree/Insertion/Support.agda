module Catt.Tree.Insertion.Support where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Boundary

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Construct.Support
open import Catt.Tree.Standard.Support

open ≡-Reasoning

open import Catt.Ops.All

open import Catt.Typing.Weak All

open import Catt.Tree.Boundary.Typing All Weak-Rules (weak-tame all-tame)
open import Catt.Tree.Structured.Typing All Weak-Rules
open import Catt.Tree.Structured.Typing.Properties All Weak-Rules (weak-tame all-tame)
open import Catt.Tree.Insertion.Typing All Weak-Rules (weak-tame all-tame)
open import Catt.Typing.Structured.Support All Weak-Rules (weak-tame all-tame) weak-supp

κ-full : (S : Tree n)
       → (P : Branch S d)
       → (T : Tree m)
       → .⦃ _ : has-trunk-height d T ⦄
       → SuppLabel (incTree (S >>[ P ] T)) (κ S P T) ≡ full
κ-full (Join S₁ S₂) BHere T
  = label-between-++t-full (replace-label (standard-label (Susp S₁) T) SHere)
                           SPath
                           (reflexive≈stm (standard-label-last (Susp S₁) T))
                           refl≈stm
                           lem
                           (id-label-full S₂)
  where
    lem : SuppLabel (incTree T) (replace-label (standard-label (Susp S₁) T) SHere) ≡ full
    lem = begin
      SuppLabel (incTree T) (replace-label (standard-label (Susp S₁) T) SHere)
        ≡⟨ replace-label-supp (standard-label (Susp S₁) T) SHere
                              (reflexive≈stm (sym≃stm (standard-label-fst (Susp S₁) T))) ⟩
      SuppSTm (incTree T) SHere ∪ SuppLabel (incTree T) (standard-label (Susp S₁) T)
        ≡⟨ cong (SuppSTm (incTree T) SHere ∪_) (standard-label-full (Susp S₁) T) ⟩
      SuppSTm (incTree T) SHere ∪ full
        ≡⟨ ∪-right-zero (trueAt (fromℕ _)) ⟩
      full ∎
κ-full (Join S₁ S₂) (BExt P) (Susp T) = label-between-joins-full (κ S₁ P T)
                                                                 (id-label S₂)
                                                                 (κ-full S₁ P T)
                                                                 (id-label-full S₂)
κ-full (Join S₁ S₂) (BShift P) T = label-between-joins-full (id-label S₁)
                                                            (κ S₂ P T)
                                                            (id-label-full S₁)
                                                            (κ-full S₂ P T)

-- κ-boundary-vs : (S : Tree n)
--               → (P : Branch S d)
--               → (T : Tree m)
--               → .⦃ _ : has-trunk-height d T ⦄
--               → (q : lh P ≥ tree-dim T)
--               → (d : ℕ)
--               → (b : Bool)
--               → tree-bd-vs d S b [ κ S P T ]vl ≡ tree-bd-vs d (S >>[ P ] T) b
-- κ-boundary-vs S P T q d b = begin
--   tree-bd-vs d S b [ κ S P T ]vl
--     ≡˘⟨ cong (_[ κ S P T ]vl) (tree-inc-label-supp d S b) ⟩
--   SuppLabel (incTree S) (ap (tree-inc-label d S b)) [ κ S P T ]vl
--     ≡˘⟨ vs-label-Label (incTree (S >>[ P ] T)) (ap (tree-inc-label d S b)) (κ S P T) (κ-Ty S P T q) ⟩
--   SuppLabel (incTree (S >>[ P ] T)) (ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆))
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   tree-bd-vs d (S >>[ P ] T) b ∎
--   where
--     lem : Bd-Conditions d P T
--         → SuppLabel (incTree (S >>[ P ] T)) (ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆))
--           ≡
--           tree-bd-vs d (S >>[ P ] T) b
--     lem (Bd-Cond1 x y) = begin
--       SuppLabel (incTree (S >>[ P ] T)) (ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆))
--         ≡⟨ EqSuppLabel (label-max-equality-to-equality
--                          (bd-κ-comm-1 S P T d x y q b)
--                          (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T q) TySStar)
--                          (label-≃-Ty (insertion-bd-1 S P T d y q) (tree-inc-Ty d (S >>[ P ] T) b))) ⟩
--       SuppLabel (incTree (S >>[ P ] T)) (label-≃ (insertion-bd-1 S P T d y q) (ap (tree-inc-label d (S >>[ P ] T) b)))
--         ≡⟨ SuppLabel-comp-full (incTree (S >>[ P ] T))
--                                (SPath ∘ (ppath-≃ (insertion-bd-1 S P T d y q)))
--                                (ap (tree-inc-label d (S >>[ P ] T) b))
--                                (tree-inc-Ty d (S >>[ P ] T) b)
--                                (ppath-≃-full (insertion-bd-1 S P T d y q)) ⟩
--       SuppLabel (incTree (S >>[ P ] T)) (ap (tree-inc-label d (S >>[ P ] T) b))
--         ≡⟨ {!!} ⟩
--       tree-bd-vs d (S >>[ P ] T) b ∎
--     lem (Bd-Cond2 x) = begin
--       SuppLabel (incTree (S >>[ P ] T)) (ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆))
--         ≡⟨ EqSuppLabel (label-max-equality-to-equality
--                          (bd-κ-comm-2 S P T d b q x)
--                          (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T q) TySStar)
--                          (label-comp-Ty (κ-Ty (tree-bd d S)
--                                               (bd-branch S P d _)
--                                               (tree-bd d T)
--                                               ⦃ _ ⦄
--                                               (bd-branch-lh S P d (bd-branch-lem P x) T q) )
--                                         (label-≃-Ty (insertion-bd-2 S P T d (bd-branch-lem P x))
--                                                     (tree-inc-Ty d (S >>[ P ] T) b))
--                                         TySStar)) ⟩
--       SuppLabel (incTree (S >>[ P ] T))
--        (κ (tree-bd d S) (bd-branch S P d _) (tree-bd d T) ⦃ _ ⦄
--              ●l label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (S >>[ P ] T) b))
--         ≡⟨ {!Supp!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!}
--         ≡⟨ {!!} ⟩
--       {!!} ∎
