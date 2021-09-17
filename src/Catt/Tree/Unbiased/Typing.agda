{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Tree.Unbiased.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Typing index rule props
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)

NonZero′-subst : n ≡ m → NonZero′ n → NonZero′ m
NonZero′-subst refl x = x

unbiased-term-Ty : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → .(tree-dim T ≡ d) → Typing-Sub (tree-to-ctx T) Γ σ
                 → Typing-Tm Γ (Coh T (unbiased-type d T) σ) (unbiased-type d T [ σ ]ty)
unbiased-type-Ty : (d : ℕ) → (T : Tree n) → .(d ≤ tree-dim T) → Typing-Ty (tree-to-ctx T) (unbiased-type d T)

unbiased-comp-Ty (suc d) T q σty = TyComp ⦃ NonZero′-subst (sym q) it ⦄ (unbiased-type-Ty (suc d) T (≤-reflexive (sym q))) σty (supp-lem false) lem refl≈ty
  where
    open ≡-Reasoning
    supp-lem : (b : Bool) → FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T b ]ty) ∪
           FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≡ supp-bd (pred (tree-dim T)) T b
    supp-lem b = begin
      FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T b ]ty) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
        ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty (unbiased-type d (tree-bd d T)) (tree-inc d T b)) (TransportVarSet-tm (unbiased-term d (tree-bd d T)) (tree-inc d T b)) ⟩
      TransportVarSet (FVTy (unbiased-type d (tree-bd d T))) (tree-inc d T b)
        ∪ TransportVarSet (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
        ≡˘⟨ TransportVarSet-∪ (FVTy (unbiased-type d (tree-bd d T))) (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b) ⟩
      TransportVarSet (FVTy (unbiased-type d (tree-bd d T)) ∪ FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
        ≡⟨ cong (λ - → TransportVarSet - (tree-inc d T b)) (supp-unbiased d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) (≤-reflexive (sym q))))) ⟩
      TransportVarSet full (tree-inc d T b)
        ≡⟨ TransportVarSet-full (tree-inc d T b) ⟩
      FVSub (tree-inc d T b)
        ≡⟨ supp-bd-compat d T b ⟩
      supp-bd d T b ≡˘⟨ cong (λ - → supp-bd - T b) (recompute ((tree-dim T ∸ 1) ≟ (suc d ∸ 1)) (cong pred q)) ⟩
      supp-bd (pred (tree-dim T)) T b ∎

    lem : FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty) ∪
            FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)
            ≡ supp-bd (pred (tree-dim T)) T true
    lem = trans (cong (λ - → FVTy - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm))
                   (sym (≃ty-to-≡ (unbiased-type-inc-lem d T)))) (supp-lem true)


unbiased-term-Ty d T q with is-linear-dec T
... | yes p = TyVarZ (reflexive≈ty (linear-tree-unbiased-lem d T ⦃ p ⦄ q))
... | no p = term-conversion (unbiased-comp-Ty d ⦃ NonZero′-subst q (non-linear-has-no-zero-dim T p) ⦄ T q id-Ty) (reflexive≈ty (id-on-ty (unbiased-type d T)))
  where
    non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero′ (tree-dim T)
    non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
    non-linear-has-no-zero-dim (Join S T) p with tree-dim (Join S T) | join-tree-has-non-zero-dim S T
    ... | zero | q = ⊥-elim (q refl)
    ... | suc d | q = it


unbiased-type-Ty zero T q = TyStar
unbiased-type-Ty (suc d) T q
  = TyArr (apply-sub-tm-typing (unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T false))
          (apply-sub-ty-typing (unbiased-type-Ty d (tree-bd d T) (≤-reflexive (sym (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))))) (tree-inc-Ty d T false))
          (term-conversion (apply-sub-tm-typing (unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T true)) (reflexive≈ty (unbiased-type-inc-lem d T)))
