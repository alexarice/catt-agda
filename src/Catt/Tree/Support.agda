module Catt.Tree.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension.Pasting
open import Catt.Wedge
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Tree
open import Catt.Tree.Pasting

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Wedge.Support
open import Catt.Suspension.Support

open import Catt.Ops
open import Catt.Typing.Rule

tree-bd-vs : (d : ℕ) → (T : Tree n) → (b : Bool) → VarSet (suc n)
tree-bd-vs zero T false = FVTm (tree-fst-var T)
tree-bd-vs zero T true = FVTm (tree-last-var T)
tree-bd-vs (suc d) Sing b = full
tree-bd-vs (suc d) (Join S T) b = wedge-susp-vs (susp-vs (tree-bd-vs d S b)) (tree-bd-vs (suc d) T b)

open ≡-Reasoning

tree-bd-vs-compat : (d : ℕ) → (T : Tree n) → (b : Bool)
                  → tree-bd-vs d T b ≡ pd-bd-vs d ⌊ T ⌋ ⦃ tree-to-pd T ⦄ b
tree-bd-vs-compat zero T false = lem ⌊ T ⌋ ⦃ pd-to-pdb (tree-to-pd T) ⦄
  where
    lem : (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → trueAt (fromℕ m) ≡ pdb-bd-vs zero Γ false
    lem (∅ , A) = refl
    lem (∅ , B , A) = ⊥-elim (pdb-odd-length it)
    lem (Γ , C , B , A) with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
    ... | tri≈ ¬a b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
tree-bd-vs-compat zero T true = let
  instance _ = tree-to-pd T
  in begin
  FVTm (tree-last-var T)
    ≡˘⟨ FVTm-≃ (tree-to-pd-focus-tm T) ⟩
  FVTm (pd-focus-tm it)
    ≡˘⟨ FVTm-≃ (pd-right-base it) ⟩
  FVTm (pdb-right-base (pd-to-pdb it))
    ≡⟨ lem ⌊ T ⌋ (pd-to-pdb it) ⟩
  pd-bd-vs zero ⌊ T ⌋ true ∎
  where
    lem : (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → FVTm (pdb-right-base pdb) ≡ pdb-bd-vs zero Γ ⦃ pdb ⦄ true
    lem (∅ , .⋆) Base = refl
    lem (∅ , A) (Restr pdb) = ⊥-elim (NonZero-⊥ (≤-trans (pdb-dim-lem pdb) (≤-reflexive (ty-dim-≃ (pdb-singleton-lem pdb)))))
    lem (∅ , B , A) pdb = ⊥-elim (pdb-odd-length pdb)
    lem (Γ , C , B , A) pdb with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-prefix pdb a) ⟩
      FVTm (wk-tm (wk-tm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ fv-wk-tm (wk-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (FVTm (wk-tm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (fv-wk-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (ewf (FVTm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb))) ⟩
      ewf (ewf (pdb-bd-vs 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true)) ∎
    ... | tri≈ ¬a b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-0-dim pdb (sym b)) ⟩
      FVTm 1V
        ≡˘⟨ cong ewf (cong ewt (drop-var (pdb-right-base (pdb-prefix pdb)) ⦃ pdb-right-base-isVar (pdb-prefix pdb) ⦄)) ⟩
      ewf (ewt (drop (FVTm (pdb-right-base (pdb-prefix pdb)))))
        ≡⟨ cong ewf (cong ewt (cong drop (lem (Γ , C) (pdb-prefix pdb)))) ⟩
      ewf (ewt (drop (pdb-bd-vs 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true))) ∎
tree-bd-vs-compat (suc d) Sing b = refl
tree-bd-vs-compat (suc d) (Join S T) b = let
  instance _ = tree-to-pd S
  instance _ = susp-pd (tree-to-pd S)
  instance _ = tree-to-pd T
  instance _ = tree-to-pd (Join S T)
  in begin
  wedge-susp-vs (susp-vs (tree-bd-vs d S b)) (tree-bd-vs (suc d) T b)
    ≡⟨ cong₂ (λ a b → wedge-susp-vs (susp-vs a) b) (tree-bd-vs-compat d S b) (tree-bd-vs-compat (suc d) T b) ⟩
  wedge-susp-vs (susp-vs (pd-bd-vs d ⌊ S ⌋ b)) (pd-bd-vs (suc d) ⌊ T ⌋ b)
    ≡⟨ wedge-susp-pdb-bd-compat d ⌊ S ⌋ ⌊ T ⌋ ⦃ pd-to-pdb it ⦄ b ⟩
  pd-bd-vs (suc d) (wedge-susp ⌊ S ⌋ ⌊ T ⌋) b ∎

tree-bd-vs-full : (d : ℕ) → (T : Tree n) → (b : Bool) → (d ≥ tree-dim T) → tree-bd-vs d T b ≡ full
tree-bd-vs-full d T b p = begin
  tree-bd-vs d T b
    ≡⟨ tree-bd-vs-compat d T b ⟩
  pd-bd-vs d ⌊ T ⌋ ⦃ tree-to-pd T ⦄ b
    ≡⟨ pd-bd-vs-full d ⌊ T ⌋ ⦃ tree-to-pd T ⦄ b (≤-trans (≤-reflexive (tree-dim-ctx-dim T)) p) ⟩
  full ∎

tree-standard-op : (ops : Op) → StandardOp ops
                 → (T : Tree n) → (d : ℕ) → (p : suc d ≥ tree-dim T)
                 → ops ⌊ T ⌋ (tree-bd-vs d T false) (tree-bd-vs d T true)
tree-standard-op ops std T d p
  = subst₂ (ops ⌊ T ⌋)
           (sym (tree-bd-vs-compat d T false))
           (sym (tree-bd-vs-compat d T true))
           (std ⌊ T ⌋ ⦃ tree-to-pd T ⦄ d (≤-trans (≤-reflexive (tree-dim-ctx-dim T)) p))
