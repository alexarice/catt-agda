module Catt.Tree.Standard.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Boundary
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support
open import Catt.Tree.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Construct.Support

supp-standard-lem : (d : ℕ) → (T : Tree n) → (b : Bool)
                  → SuppSTm (incTree T) (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)
                    ≡
                    tree-bd-vs d T b
supp-standard-coh-lem : (d : ℕ) → (T : Tree n) → (b : Bool)
                      → SuppSTm (incTree T) (standard-coh d (tree-bd d T) >>= tree-inc-label d T b)
                        ≡
                        tree-bd-vs d T b

supp-standard-lem zero S false = refl
supp-standard-lem zero S true = SuppPath-last S
supp-standard-lem (suc d) Sing b = refl
supp-standard-lem (suc d) (Susp T) b = begin
  SuppSTm (incTree (Susp T))
      (standard-stm d (tree-bd d T) >>=
       label₁ (tree-inc-label (suc d) (Susp T) b))
    ≡⟨ SuppSTm-≃ (incTree (Susp T)) l1 ⟩
  SuppSTm (incTree (Susp T)) (SExt (standard-stm d (tree-bd d T) >>= tree-inc-label d T b))
    ≡⟨⟩
  susp-vs (SuppSTm (incTree T) (standard-stm d (tree-bd d T) >>= tree-inc-label d T b))
    ≡⟨ cong susp-vs (supp-standard-lem d T b) ⟩
  susp-vs (tree-bd-vs d T b)
    ≡⟨ lookup-isVar-⊆ (susp-vs (tree-bd-vs d T b)) get-snd (susp-vs-snd-Truth (tree-bd-vs d T b)) ⟩
  susp-vs (tree-bd-vs d T b) ∪ FVTm get-snd ∎
  where
    l1 : (standard-stm d (tree-bd d T) >>=
            label₁ (tree-inc-label (suc d) (Susp T) b))
         ≃stm
         SExt (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)
    l1 = begin
      < standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = standard-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] [ refl≃ty ] ⟩
      < standard-stm d (tree-bd d T) >>= susp-label (tree-inc-label d T b) >stm
        ≈˘⟨ >>=-susp-label (standard-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < SExt (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm ∎
      where
        open Reasoning stm-setoid
    open ≡-Reasoning
supp-standard-lem (suc d) (Join S (Join T₁ T₂)) b = supp-standard-coh-lem (suc d) (Join S (Join T₁ T₂)) b

open ≡-Reasoning

supp-standard-coh-lem d T b = begin
  SuppLabel-WT (incTree T) (tree-inc-label d T b)
    ≡⟨ ∪-left-unit (SuppLabel (incTree T) (ap (tree-inc-label d T b))) ⟩
  SuppLabel (incTree T) (ap (tree-inc-label d T b))
    ≡⟨ tree-inc-label-supp d T b ⟩
  tree-bd-vs d T b ∎

standard-stm-full : (d : ℕ) → (T : Tree m) → (d ≥ tree-dim T) → SuppSTm (incTree T) (standard-stm d T) ≡ full
standard-stm-full zero Sing p = refl
standard-stm-full (suc d) Sing p = refl
standard-stm-full (suc d) (Susp T) p = begin
  susp-vs (SuppSTm (incTree T) (standard-stm d T))
    ≡⟨ cong susp-vs (standard-stm-full d T (≤-pred p)) ⟩
  susp-vs full
    ≡⟨ susp-vs-full ⟩
  full ∎
standard-stm-full (suc d) (Join T (Join T₁ T₂)) p = id-label-wt-full (Join T (Join T₁ T₂))

standard-label-full : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m)
                    → SuppLabel (incTree T) (standard-label S T) ≡ full
standard-label-full S T = begin
  SuppLabel (incTree T) (standard-label S T)
    ≡⟨ stm-to-label-supp (incTree T) S (standard-coh′ (tree-dim S) T) (standard-sty (tree-dim S) T) ⟩
  SuppSTy (incTree T) (standard-sty (tree-dim S) T)
  ∪ SuppSTm (incTree T) (standard-coh′ (tree-dim S) T)
    ≡⟨ cong (SuppSTy (incTree T) (standard-sty (tree-dim S) T) ∪_)
            (SuppSTm-≃ (incTree T) (standard-coh′-compat (tree-dim S) T)) ⟩
  SuppSTy (incTree T) (standard-sty (tree-dim S) T)
  ∪ SuppSTm (incTree T) (standard-coh (tree-dim S) T)
    ≡⟨ cong (SuppSTy (incTree T) (standard-sty (tree-dim S) T) ∪_)
            (id-label-wt-full T) ⟩
  SuppSTy (incTree T) (standard-sty (tree-dim S) T) ∪ full
    ≡⟨ ∪-right-zero (SuppSTy (incTree T) (standard-sty (tree-dim S) T)) ⟩
  full ∎
