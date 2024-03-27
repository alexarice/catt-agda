module Catt.Tree.Boundary.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Structured

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Wedge.Support
open import Catt.Suspension.Support
open import Catt.Tree.Support
open import Catt.Tree.Path.Support
open import Catt.Tree.Structured.Support

open import Catt.Ops.All
open import Catt.Typing.Weak All

open import Catt.Typing All Weak-Rules
open import Catt.Tree.Typing All Weak-Rules (weak-tame all-tame)
open import Catt.Typing.Properties.Support All Weak-Rules weak-supp

open ≡-Reasoning

SuppPath-last : (T : Tree n) → SuppPath (last-path T) ≡ FVTm (tree-last-var T)
SuppPath-last T = begin
  SuppPath (last-path T)
    ≡⟨ SuppPath-to-term (last-path T) ⟩
  SuppTm ⌊ T ⌋ (path-to-term (last-path T))
    ≡⟨ cong (DC ⌊ T ⌋) (FVTm-≃ (last-path-to-term T)) ⟩
  SuppTm ⌊ T ⌋ (tree-last-var T)
    ≡⟨ SuppTmChar′ (tree-last-var-Ty T) TyStar ⟩
  FVTy ⋆ ∪ FVTm (tree-last-var T)
    ≡⟨ ∪-left-unit (FVTm (tree-last-var T)) ⟩
  FVTm (tree-last-var T) ∎

tree-inc-label-supp : (d : ℕ) → (T : Tree n) → (b : Bool)
                    → SuppLabel (incTree T) (ap (tree-inc-label d T b))
                      ≡
                      tree-bd-vs d T b
tree-inc-label-supp zero T false = refl
tree-inc-label-supp zero T true = SuppPath-last T
tree-inc-label-supp (suc d) Sing b = refl
tree-inc-label-supp (suc d) (Join S T) b = begin
  trueAt (fromℕ _)
  ∪ SuppLabel (incTree (Join S T)) (SExt ∘ ap (tree-inc-label d S b))
  ∪ SuppLabel (incTree (Join S T)) (SShift ∘ ap (tree-inc-label (suc d) T b))
    ≡⟨ cong₂ (λ a b → trueAt (fromℕ _) ∪ a ∪ b)
             (SuppLabel-ext (ap (tree-inc-label d S b)) T)
             (SuppLabel-shift (ap (tree-inc-label (suc d) T b)) S) ⟩
  trueAt (fromℕ _) ∪
   wedge-susp-vs
   (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b))))
   (empty {n = suc (tree-size T)})
   ∪
   wedge-susp-vs empty
   (SuppLabel (incTree T) (ap (tree-inc-label (suc d) T b)))
    ≡⟨ cong (_∪ wedge-susp-vs empty (SuppLabel (incTree T) (ap (tree-inc-label (suc d) T b))))
        (sym (trans (lookup-isVar-⊆ (wedge-susp-vs
   (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b))))
   empty) (Var (fromℕ _)) (Truth-prop′ (trans (wedge-susp-vs-fst-var {m = suc (tree-size T)} (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b)))) empty) (susp-vs-fst-var (SuppLabel (incTree S) (ap (tree-inc-label d S b))))))) (∪-comm _ _))) ⟩
  wedge-susp-vs
   (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b))))
   empty
   ∪
   wedge-susp-vs empty
   (SuppLabel (incTree T) (ap (tree-inc-label (suc d) T b)))
    ≡⟨ wedge-vs-∪ (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b))))
                  empty
                  empty
                  (SuppLabel (incTree T) (ap (tree-inc-label (suc d) T b)))
                  get-snd ⟩
  wedge-susp-vs
   (susp-vs (SuppLabel (incTree S) (ap (tree-inc-label d S b))) ∪
    empty)
   (empty ∪
    SuppLabel (incTree T) (ap (tree-inc-label (suc d) T b)))
    ≡⟨ cong₂ wedge-susp-vs (trans (∪-right-unit _) (cong susp-vs (tree-inc-label-supp d S b)))
                           (trans (∪-left-unit _) (tree-inc-label-supp (suc d) T b)) ⟩
  wedge-susp-vs (susp-vs (tree-bd-vs d S b)) (tree-bd-vs (suc d) T b) ∎
