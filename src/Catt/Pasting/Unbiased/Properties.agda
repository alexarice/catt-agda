{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Unbiased.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Pasting.Tree
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Nat
open import Data.Fin using (fromℕ; Fin; suc; zero; inject₁)
open import Catt.Pasting.Unbiased
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Data.Unit
open import Data.Empty
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties

unbiased-type-on-eq-ctx : (pd : Γ ⊢pd₀ d)
                        → (pd2 : Δ ⊢pd₀ d′)
                        → Γ ≃c Δ
                        → unbiased-type pd ≃ty unbiased-type pd2
unbiased-type-on-eq-ctx pd pd2 p with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl with pd-same-dim pd pd2 p
... | refl with pd-irrelevant pd pd2
... | refl = refl≃ty

unbiased-term-on-eq-ctx : (pd : Γ ⊢pd₀ d)
                        → (pd2 : Δ ⊢pd₀ d)
                        → Γ ≃c Δ
                        → unbiased-term pd ≃tm unbiased-term pd2
unbiased-term-on-eq-ctx pd pd2 p with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl with pd-irrelevant pd pd2
... | refl = refl≃tm

susp-pdb-is-extends : (pdb : Γ ⊢pd[ submax ][ d ])
                    → ⦃ pdb-is-extends pdb ⦄
                    → pdb-is-extends (susp-pdb pdb)
susp-pdb-is-extends Base = tt
susp-pdb-is-extends (Extend pdb p q) = susp-pdb-is-extends pdb

susp-pdb-from-extends : (pdb : Γ ⊢pd[ submax ][ d ])
                      → ⦃ pdb-is-extends (susp-pdb pdb) ⦄
                      → pdb-is-extends pdb
susp-pdb-from-extends Base = tt
susp-pdb-from-extends (Extend pdb p q) = susp-pdb-from-extends pdb

susp-pdb-is-linear : (pdb : Γ ⊢pd[ submax ][ d ])
                   → ⦃ pdb-is-linear pdb ⦄
                   → pdb-is-linear (susp-pdb pdb)
susp-pdb-is-linear Base = tt
susp-pdb-is-linear (Extend pdb p q) = susp-pdb-is-extends pdb
susp-pdb-is-linear (Restr pdb) = susp-pdb-is-linear pdb

susp-pdb-from-linear : (pdb : Γ ⊢pd[ submax ][ d ])
                     → ⦃ pdb-is-linear (susp-pdb pdb) ⦄
                     → pdb-is-linear pdb
susp-pdb-from-linear Base = tt
susp-pdb-from-linear (Extend pdb p q) = susp-pdb-from-extends pdb
susp-pdb-from-linear (Restr pdb) = susp-pdb-from-linear pdb

susp-pd-is-linear : (pd : Γ ⊢pd₀ d)
                  → ⦃ pd-is-linear pd ⦄
                  → pd-is-linear (susp-pd pd)
susp-pd-is-linear (Finish pdb) = susp-pdb-is-linear pdb

susp-pd-from-linear : (pd : Γ ⊢pd₀ d)
                    → ⦃ pd-is-linear (susp-pd pd) ⦄
                    → pd-is-linear pd
susp-pd-from-linear (Finish pdb) = susp-pdb-from-linear pdb

susp-unbiased-type : (pd : Γ ⊢pd₀ d) → unbiased-type (susp-pd pd) ≃ty suspTy (unbiased-type pd)
susp-unbiased-term : (pd : Γ ⊢pd₀ d) → unbiased-term (susp-pd pd) ≃tm suspTm (unbiased-term pd)

susp-unbiased-type {d = zero} (Finish pdb) with zero-dim-pdb-is-Base pdb
... | refl = refl≃ty
susp-unbiased-type {d = suc d} pd = Arr≃ l1 l2 l3
  where
    l1 : unbiased-term (pd-bd-pd (susp-pd pd)) [ pd-src (susp-pd pd) ]tm
         ≃tm suspTm (unbiased-term (pd-bd-pd pd) [ pd-src pd ]tm)
    l1 = begin
      < unbiased-term (pd-bd-pd (susp-pd pd)) [ pd-src (susp-pd pd) ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-on-eq-ctx (pd-bd-pd (susp-pd pd)) (susp-pd (pd-bd-pd pd)) (susp-pd-bd pd)) (susp-pd-src pd) ⟩
      < unbiased-term (susp-pd (pd-bd-pd pd)) [ suspSub (pd-src pd) ]tm >tm
        ≈⟨ sub-action-≃-tm (susp-unbiased-term (pd-bd-pd pd)) refl≃s ⟩
      < suspTm (unbiased-term (pd-bd-pd pd)) [ suspSub (pd-src pd) ]tm >tm
        ≈˘⟨ susp-functorial-tm (pd-src pd) (unbiased-term (pd-bd-pd pd)) ⟩
      < suspTm (unbiased-term (pd-bd-pd pd) [ pd-src pd ]tm) >tm ∎
      where
        open Reasoning tm-setoid
    l2 : unbiased-type (pd-bd-pd (susp-pd pd)) [ pd-src (susp-pd pd) ]ty
         ≃ty suspTy (unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty)
    l2 = begin
      < unbiased-type (pd-bd-pd (susp-pd pd)) [ pd-src (susp-pd pd) ]ty >ty
        ≈⟨ sub-action-≃-ty (unbiased-type-on-eq-ctx (pd-bd-pd (susp-pd pd)) (susp-pd (pd-bd-pd pd)) (susp-pd-bd pd)) (susp-pd-src pd) ⟩
      < (unbiased-type (susp-pd (pd-bd-pd pd)) [ suspSub (pd-src pd) ]ty) >ty
        ≈⟨ sub-action-≃-ty (susp-unbiased-type (pd-bd-pd pd)) refl≃s ⟩
      < suspTy (unbiased-type (pd-bd-pd pd)) [ suspSub (pd-src pd) ]ty
        >ty
        ≈˘⟨ susp-functorial-ty (pd-src pd) (unbiased-type (pd-bd-pd pd)) ⟩
      < suspTy (unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty) >ty ∎
      where
        open Reasoning ty-setoid

    l3 : unbiased-term (pd-bd-pd (susp-pd pd)) [ pd-tgt (susp-pd pd) ]tm
         ≃tm suspTm (unbiased-term (pd-bd-pd pd) [ pd-tgt pd ]tm)
    l3 = begin
      < unbiased-term (pd-bd-pd (susp-pd pd)) [ pd-tgt (susp-pd pd) ]tm
        >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-on-eq-ctx (pd-bd-pd (susp-pd pd)) (susp-pd (pd-bd-pd pd)) (susp-pd-bd pd)) (susp-pd-tgt pd) ⟩
      < unbiased-term (susp-pd (pd-bd-pd pd)) [ suspSub (pd-tgt pd) ]tm >tm
        ≈⟨ sub-action-≃-tm (susp-unbiased-term (pd-bd-pd pd)) refl≃s ⟩
      < suspTm (unbiased-term (pd-bd-pd pd)) [ suspSub (pd-tgt pd) ]tm >tm
        ≈˘⟨ susp-functorial-tm (pd-tgt pd) (unbiased-term (pd-bd-pd pd)) ⟩
      < suspTm (unbiased-term (pd-bd-pd pd) [ pd-tgt pd ]tm) >tm ∎
      where
        open Reasoning tm-setoid

susp-unbiased-term pd with pd-is-linear-dec pd | pd-is-linear-dec (susp-pd pd)
... | yes p | yes q = refl≃tm
... | yes p | no q = ⊥-elim (q (susp-pd-is-linear pd ⦃ p ⦄))
... | no p | yes q = ⊥-elim (p (susp-pd-from-linear pd ⦃ q ⦄))
... | no p | no q = Coh≃ refl≃c (susp-unbiased-type pd) (sym≃s (susp-functorial-id (suc _)))

unbiased-type-from-boundary : (pd : Γ ⊢pd₀ (suc d)) → unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty ≃ty unbiased-type (pd-bd-pd pd) [ pd-tgt pd ]ty
unbiased-type-from-boundary {d = zero} pd = refl≃ty
unbiased-type-from-boundary {d = suc d} pd = Arr≃ l1 l2 l3
  where
    l1 : unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]tm [ pd-src pd ]tm
           ≃tm
         unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]tm [ pd-tgt pd ]tm
    l1 = begin
      < unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]tm [ pd-src pd ]tm >tm
        ≈˘⟨ assoc-tm _ _ (unbiased-term (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd))
          [ pd-src pd ∘ pd-src (pd-bd-pd pd) ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = unbiased-term (pd-bd-pd (pd-bd-pd pd))}) (pd-globular-1 pd) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd))
          [ pd-tgt pd ∘ pd-src (pd-bd-pd pd) ]tm >tm
        ≈⟨ assoc-tm _ _ (unbiased-term (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]tm [ pd-tgt pd ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : unbiased-type (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]ty [ pd-src pd ]ty
           ≃ty
         unbiased-type (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]ty [ pd-tgt pd ]ty
    l2 = begin
      < unbiased-type (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]ty [ pd-src pd ]ty >ty
        ≈˘⟨ assoc-ty _ _ (unbiased-type (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-type (pd-bd-pd (pd-bd-pd pd))
          [ pd-src pd ∘ pd-src (pd-bd-pd pd) ]ty >ty
        ≈⟨ sub-action-≃-ty (refl≃ty {A = unbiased-type (pd-bd-pd (pd-bd-pd pd))}) (pd-globular-1 pd) ⟩
      < unbiased-type (pd-bd-pd (pd-bd-pd pd))
          [ pd-tgt pd ∘ pd-src (pd-bd-pd pd) ]ty >ty
        ≈⟨ assoc-ty _ _ (unbiased-type (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-type (pd-bd-pd (pd-bd-pd pd)) [ pd-src (pd-bd-pd pd) ]ty [ pd-tgt pd ]ty >ty ∎
      where
        open Reasoning ty-setoid

    l3 : unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-tgt (pd-bd-pd pd) ]tm [ pd-src pd ]tm
           ≃tm
         unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-tgt (pd-bd-pd pd) ]tm [ pd-tgt pd ]tm
    l3 = begin
      < unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-tgt (pd-bd-pd pd) ]tm [ pd-src pd ]tm >tm
        ≈˘⟨ assoc-tm _ _ (unbiased-term (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd))
          [ pd-src pd ∘ pd-tgt (pd-bd-pd pd) ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = unbiased-term (pd-bd-pd (pd-bd-pd pd))}) (pd-globular-2 pd) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd))
          [ pd-tgt pd ∘ pd-tgt (pd-bd-pd pd) ]tm >tm
        ≈⟨ assoc-tm _ _ (unbiased-term (pd-bd-pd (pd-bd-pd pd))) ⟩
      < unbiased-term (pd-bd-pd (pd-bd-pd pd)) [ pd-tgt (pd-bd-pd pd) ]tm [ pd-tgt pd ]tm >tm ∎
      where
        open Reasoning tm-setoid

unbiased-type-sphere-fst-var-lem : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ suc d)
                                 → Var (fromℕ _) [ sub-from-sphere (unbiased-type pd) ]tm ≃tm Var (fromℕ n)
unbiased-type-sphere-fst-var-lem {d = zero} pd = begin
  < unbiased-term (pd-bd-pd pd) [ pd-src pd ]tm >tm
    ≈⟨ sub-action-≃-tm (lem (pd-bd-pd pd)) refl≃s ⟩
  < Var (fromℕ _) [ pd-src pd ]tm >tm
    ≈⟨ pd-src-fst-var pd ⟩
  < Var (fromℕ _) >tm ∎
  where
    open Reasoning tm-setoid
    lem : {Γ : Ctx (suc n)} → (pd2 : Γ ⊢pd₀ 0) → unbiased-term pd2 ≃tm Var (fromℕ n)
    lem (Finish Base) = refl≃tm
unbiased-type-sphere-fst-var-lem {d = suc d} pd = begin
  < Var (fromℕ (suc (sphere-size (suc d)))) [ sub-from-sphere (unbiased-type pd) ]tm >tm ≡⟨⟩
  < Var (fromℕ (suc (sphere-size d))) [ sub-from-sphere (unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ (suc (sphere-size d)))}) (sphere-to-subbed-ty (unbiased-type (pd-bd-pd pd)) (pd-src pd)) ⟩
  < Var (fromℕ (suc (sphere-size d))) [ pd-src pd ∘ sub-from-sphere (unbiased-type (pd-bd-pd pd)) ]tm >tm
    ≈⟨ assoc-tm (pd-src pd) (sub-from-sphere (unbiased-type (pd-bd-pd pd))) (Var (fromℕ (suc (sphere-size d)))) ⟩
  < Var (fromℕ (suc (sphere-size d)))
    [ sub-from-sphere (unbiased-type (pd-bd-pd pd)) ]tm
    [ pd-src pd ]tm >tm
    ≈⟨ sub-action-≃-tm (unbiased-type-sphere-fst-var-lem (pd-bd-pd pd)) refl≃s ⟩
  < Var (fromℕ (pd-bd-len-1 pd)) [ pd-src pd ]tm >tm
    ≈⟨ pd-src-fst-var pd ⟩
  < Var (fromℕ _) >tm ∎
  where
    open Reasoning tm-setoid

unbiased-type-disc-fst-var-lem : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ suc d)
                          → Var (fromℕ _) [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub _)) ]tm ≃tm Var (fromℕ n)
unbiased-type-disc-fst-var-lem {Γ = Γ} pd = begin
  < Var (fromℕ _) [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub _)) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ sub-from-sphere (unbiased-type pd [ idSub _ ]ty) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ (suc (sphere-size _)))}) (sphere-to-subbed-ty (unbiased-type pd) (idSub _)) ⟩
  < Var (fromℕ _) [ idSub (ctxLength Γ) ∘ sub-from-sphere (unbiased-type pd) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ _)}) (id-left-unit (sub-from-sphere (unbiased-type pd))) ⟩
  < Var (fromℕ _) [ sub-from-sphere (unbiased-type pd) ]tm >tm
    ≈⟨ unbiased-type-sphere-fst-var-lem pd ⟩
  < Var (fromℕ _) >tm ∎
  where
    open Reasoning tm-setoid

unbiased-type-disc-fst-var-lem′ : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → .(suc l ≡ d)
                          → Var (fromℕ _) [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub _)) ]tm ≃tm Var (fromℕ n)
unbiased-type-disc-fst-var-lem′ {d = suc d} pd p = unbiased-type-disc-fst-var-lem pd

get-right-base-unbiased : (pd : Γ ⊢pd₀ suc d) → get-right-base-tm (unbiased-type pd) ≃tm pd-focus-tm pd
get-right-base-unbiased {d = zero} pd = begin
  < (unbiased-term (pd-bd-pd pd) [ pd-tgt pd ]tm) >tm
    ≈⟨ sub-action-≃-tm (lem (pd-bd-pd pd)) refl≃s ⟩
  < pd-focus-tm (pd-bd-pd pd) [ pd-tgt pd ]tm >tm
    ≈⟨ pd-tgt-foc pd ⟩
  < pd-focus-tm pd >tm ∎
  where
    open Reasoning tm-setoid
    lem : {Γ : Ctx (suc n)} → (pd2 : Γ ⊢pd₀ 0) → unbiased-term pd2 ≃tm pd-focus-tm pd2
    lem (Finish Base) = refl≃tm
get-right-base-unbiased {d = suc d} pd = begin
  < get-right-base-tm (unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty) >tm
    ≈⟨ get-right-base-tm-≃ (unbiased-type-from-boundary pd) ⟩
  < get-right-base-tm (unbiased-type (pd-bd-pd pd) [ pd-tgt pd ]ty) >tm
    ≈⟨ get-right-base-subbed (unbiased-type (pd-bd-pd pd)) (pd-tgt pd) ⟩
  < get-right-base-tm (unbiased-type (pd-bd-pd pd)) [ pd-tgt pd ]tm >tm
    ≈⟨ sub-action-≃-tm (get-right-base-unbiased (pd-bd-pd pd)) refl≃s ⟩
  < pd-focus-tm (pd-bd-pd pd) [ pd-tgt pd ]tm >tm
    ≈⟨ pd-tgt-foc pd ⟩
  < pd-focus-tm pd >tm ∎
  where
    open Reasoning tm-setoid
unbiased-type-disc-foc-lem : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄
                           → pd-focus-tm (Disc-pd d) [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub (suc _))) ]tm
                             ≃tm
                             pd-focus-tm pd
unbiased-type-disc-foc-lem {d = suc d} {Γ = Γ} pd = begin
  < pd-focus-tm (Disc-pd (suc d))
      [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub (suc _))) ]tm >tm
    ≈⟨ sub-action-≃-tm (pd-focus-disc-is-snd d) refl≃s ⟩
  < Var (inject₁ (fromℕ _))
    [ sub-from-disc Γ (Coh Γ (unbiased-type pd) (idSub (suc _))) ]tm >tm ≡⟨⟩
  < Var (inject₁ (fromℕ _))
    [ sub-from-sphere (unbiased-type pd [ idSub _ ]ty) ]tm >tm
    ≈⟨ sub-from-sphere-snd (unbiased-type pd [ idSub _ ]ty) ⟩
  < get-right-base-tm (unbiased-type pd [ idSub (ctxLength Γ) ]ty) >tm
    ≈⟨ get-right-base-tm-≃ (id-on-ty (unbiased-type pd)) ⟩
  < get-right-base-tm (unbiased-type pd) >tm
    ≈⟨ get-right-base-unbiased pd ⟩
  < pd-focus-tm pd >tm ∎
  where
    open Reasoning tm-setoid

pdb-is-extends-to-linear-tree : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ pdb-is-extends pdb ⦄ → is-linear (pdb-to-tree pdb)
pdb-is-extends-lin-height : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ _ : pdb-is-extends pdb ⦄ → d ≡ height-of-linear (pdb-to-tree pdb) ⦃ pdb-is-extends-to-linear-tree pdb ⦄

pdb-is-extends-to-linear-tree Base = tt
pdb-is-extends-to-linear-tree (Extend {d = d} pdb p q) = extend-is-linear {d = d} (pdb-to-tree pdb) ⦃ pdb-is-extends-to-linear-tree pdb ⦄ (pdb-is-extends-lin-height pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄

pdb-is-extends-lin-height Base = refl
pdb-is-extends-lin-height (Extend pdb x x₁) = trans (cong suc (pdb-is-extends-lin-height pdb)) (sym (extend-lin-height-suc (pdb-to-tree pdb) ⦃ pdb-is-extends-to-linear-tree pdb ⦄ (pdb-is-extends-lin-height pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄))

pdb-is-linear-to-linear-tree : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ pdb-is-linear pdb ⦄ → is-linear (pdb-to-tree pdb)
pdb-is-linear-to-linear-tree Base = tt
pdb-is-linear-to-linear-tree (Extend {d = d} pdb p q) = extend-is-linear {d = d} (pdb-to-tree pdb) ⦃ pdb-is-extends-to-linear-tree pdb ⦄ (pdb-is-extends-lin-height pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-is-linear-to-linear-tree (Restr pdb) = pdb-is-linear-to-linear-tree pdb

pd-is-linear-to-linear-tree : (pd : Γ ⊢pd₀ d) → .⦃ pd-is-linear pd ⦄ → is-linear (pd-to-tree pd)
pd-is-linear-to-linear-tree (Finish pdb) = pdb-is-linear-to-linear-tree pdb

unbiased-type-linear-tree : (T : Tree n) → .⦃ _ : is-linear T ⦄ → unbiased-type (tree-to-pd T) ≃ty (tree-to-ctx T) ‼ zero
unbiased-type-linear-tree Sing = refl≃ty
unbiased-type-linear-tree (Join T Sing) = begin
  < unbiased-type (susp-pd (tree-to-pd T)) >ty
    ≈⟨ susp-unbiased-type (tree-to-pd T) ⟩
  < suspTy (unbiased-type (tree-to-pd T)) >ty
    ≈⟨ susp-ty-≃ (unbiased-type-linear-tree T) ⟩
  < suspTy (tree-to-ctx T ‼ zero) >ty
    ≈˘⟨ susp-‼ (tree-to-ctx T) zero ⟩
  < suspCtx (tree-to-ctx T) ‼ zero >ty ∎
  where
    open Reasoning ty-setoid

unbiased-type-linear : (pd : Γ ⊢pd₀ d) → .⦃ pd-is-linear pd ⦄ → unbiased-type pd ≃ty Γ ‼ zero
unbiased-type-linear pd = trans≃ty (unbiased-type-on-eq-ctx pd (tree-to-pd (pd-to-tree pd)) (sym≃c (pd-to-tree-to-ctx pd))) (trans≃ty (unbiased-type-linear-tree (pd-to-tree pd) ⦃ pd-is-linear-to-linear-tree pd ⦄) (‼-≃ zero zero refl (pd-to-tree-to-ctx pd)))
