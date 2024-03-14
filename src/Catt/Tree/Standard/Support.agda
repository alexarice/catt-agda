module Catt.Tree.Standard.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
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
open import Catt.Tree.Structured.Support.Properties
open import Catt.Tree.Structured.Construct.Support

supp-standard-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)) ≡ tree-bd-vs d T b
supp-standard-coh-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → DCT (FVSTm (standard-coh d (tree-bd d T) >>= tree-inc-label d T b)) ≡ tree-bd-vs d T b

supp-standard-lem zero Sing false = refl
supp-standard-lem zero Sing true = refl
supp-standard-lem zero (Join S T) false rewrite tEmp-empty S = cong₂ (VSJoin true) DCT-emp DCT-emp
supp-standard-lem zero (Join S T) true rewrite tEmp-empty S = cong₂ (VSJoin false) DCT-emp (DCT-last-path T)
supp-standard-lem (suc d) Sing b = refl
supp-standard-lem (suc d) (Susp T) b = begin
  DCT (FVSTm (standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b)))
    ≡⟨ FVSTm-≃ {a = standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b)}
               {b = susp-stm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)}
               l1 ⟩
  DCT (FVSTm (susp-stm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡˘⟨ FVSTm-susp (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) ⟩
  susp-tvarset (DCT (FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)))
    ≡⟨ cong susp-tvarset (supp-standard-lem d T b) ⟩
  susp-tvarset (tree-bd-vs d T b) ∎
  where
    l1 : (standard-stm d (tree-bd d T) >>=
            label₁ (tree-inc-label (suc d) (Susp T) b))
           ≃stm
           susp-stm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b)
    l1 = begin
      < standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = standard-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] [ refl≃ty ] ⟩
      < standard-stm d (tree-bd d T) >>= susp-label (tree-inc-label d T b) >stm
        ≈˘⟨ >>=-susp-label (standard-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < susp-stm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm ∎
      where
        open Reasoning stm-setoid
    open ≡-Reasoning
supp-standard-lem (suc d) (Join T (Join T₁ T₂)) b = supp-standard-coh-lem (suc d) (Join T (Join T₁ T₂)) b

supp-standard-coh-lem d T b = begin
  DCT (FVLabel-WT (tree-inc-label d T b))
    ≡⟨ cong DCT (tree-inc-label-supp d T b) ⟩
  DCT (tree-bd-vs d T b)
    ≡⟨ DCT-tree-bd-vs d T b ⟩
  tree-bd-vs d T b ∎
  where open ≡-Reasoning

standard-supp-condition-1 : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≡ d) → supp-condition-s true T (standard-sty d T)
standard-supp-condition-1 (suc d) T p with cong pred p
... | refl = NonZero-subst (sym p) it ,, supp-standard-lem (pred (tree-dim T)) T false ,, supp-standard-lem (pred (tree-dim T)) T true

standard-supp-condition-2 : (d : ℕ) → (T : Tree n) → (tree-dim T < d) → supp-condition-s false T (standard-sty d T)
standard-supp-condition-2 (suc d) T p = begin
  DCT (FVSTy (standard-sty d T) ∪t
      FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T false)
      ∪t FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ DCT-∪ _ _ ⟩
  DCT
    (FVSTy (standard-sty d T) ∪t
     FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T false))
    ∪t
    DCT
    (FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T true))
    ≡⟨ cong (DCT (FVSTy (standard-sty d T) ∪t
      FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t_) lem ⟩
  DCT (FVSTy (standard-sty d T) ∪t
      FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T false))
      ∪t tFull
    ≡⟨ ∪t-right-zero (DCT (FVSTy (standard-sty d T)
                     ∪t FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T false))) ⟩
  tFull ∎
  where
    open ≡-Reasoning
    lem : DCT (FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T true)) ≡ tFull
    lem = begin
      DCT (FVSTm (standard-stm d (tree-bd d T) >>= tree-inc-label d T true))
        ≡⟨ supp-standard-lem d T true ⟩
      tree-bd-vs d T true
        ≡⟨ tree-bd-vs-full d T true (≤-pred p) ⟩
      tFull ∎

open ≡-Reasoning

standard-label-full : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → DCT (FVLabel (standard-label S T)) ≡ tFull
standard-label-full S T = begin
  DCT (FVLabel (standard-label S T))
    ≡⟨ cong DCT (stm-to-label-supp S (standard-coh′ (tree-dim S) T) (standard-sty (tree-dim S) T)) ⟩
  DCT (FVSTy (standard-sty (tree-dim S) T) ∪m FVSTm (standard-coh′ (tree-dim S) T))
    ≡⟨ DCT-∪ (FVSTy (standard-sty (tree-dim S) T)) (FVSTm (standard-coh′ (tree-dim S) T)) ⟩
  DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t DCT (FVSTm (standard-coh′ (tree-dim S) T))
    ≡⟨ cong (DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t_) (FVSTm-≃ (standard-coh′-compat (tree-dim S) T)) ⟩
  DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t DCT (FVSTm (standard-coh (tree-dim S) T))
    ≡⟨ cong (DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t_) (cong DCT (id-label-wt-full T)) ⟩
  DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t DCT tFull
    ≡⟨ cong (DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t_) DCT-full ⟩
  DCT (FVSTy (standard-sty (tree-dim S) T)) ∪t tFull
    ≡⟨ ∪t-right-zero (DCT (FVSTy (standard-sty (tree-dim S) T))) ⟩
  tFull ∎


standard-stm-full : (d : ℕ) → (T : Tree m) → (d ≥ tree-dim T) → DCT (FVSTm (standard-stm d T)) ≡ tFull
standard-stm-full zero Sing p = refl
standard-stm-full (suc d) Sing p = refl
standard-stm-full (suc d) (Susp T) p = begin
  DCT (FVSTm (susp-stm (standard-stm d T)))
    ≡˘⟨ FVSTm-susp (standard-stm d T) ⟩
  susp-tvarset (DCT (FVSTm (standard-stm d T)))
    ≡⟨ cong susp-tvarset (standard-stm-full d T (≤-pred p)) ⟩
  tFull ∎
standard-stm-full (suc d) (Join T (Join T₁ T₂)) p = begin
  DCT (FVLabel-WT (id-label-wt (Join T (Join T₁ T₂))))
    ≡⟨ cong DCT (id-label-wt-full (Join T (Join T₁ T₂))) ⟩
  DCT tFull
    ≡⟨ DCT-full ⟩
  tFull ∎
