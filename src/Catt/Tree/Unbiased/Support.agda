{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Support
open import Tactic.MonoidSolver
open import Catt.Suspension
open import Catt.Variables
open import Catt.Connection
open import Catt.Globular
open import Catt.Globular.Properties

supp-unbiased-lem : (d : ℕ) → (T : Tree n) → .(d ≤ tree-dim T) → (b : Bool)
                  → FVTy (unbiased-type d T)
                  ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) ≡ supp-tree-bd d T b
supp-unbiased : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d) → FVTy (unbiased-type d T) ∪ FVTm (unbiased-term d T) ≡ full

supp-unbiased-lem d T p b = begin
  FVTy (unbiased-type d T)
  ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
    ≡⟨ cong (λ - → FVTy - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm))
         (≃ty-to-≡ (unbiased-type-prop d T d ≤-refl b)) ⟩
  FVTy (unbiased-type d (tree-bd d T) [ tree-inc d T b ]ty)
  ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
    ≡˘⟨ cong₂ _∪_ (TransportVarSet-ty (unbiased-type d (tree-bd d T)) (tree-inc d T b)) (TransportVarSet-tm (unbiased-term d (tree-bd d T)) (tree-inc d T b)) ⟩
  TransportVarSet (FVTy (unbiased-type d (tree-bd d T))) (tree-inc d T b)
  ∪ TransportVarSet (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
    ≡˘⟨ TransportVarSet-∪ (FVTy (unbiased-type d (tree-bd d T))) (FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b) ⟩
  TransportVarSet (FVTy (unbiased-type d (tree-bd d T)) ∪ FVTm (unbiased-term d (tree-bd d T))) (tree-inc d T b)
    ≡⟨ cong (λ - → TransportVarSet - (tree-inc d T b)) (supp-unbiased d (tree-bd d T) (tree-dim-bd′ d T p)) ⟩
  TransportVarSet full (tree-inc d T b) ≡⟨ TransportVarSet-full (tree-inc d T b) ⟩
  FVSub (tree-inc d T b) ≡⟨ supp-tree-bd-compat d T b ⟩
  supp-tree-bd d T b ∎
    where
      open ≡-Reasoning

supp-unbiased zero Sing p = refl
supp-unbiased zero (Join S T) ()
supp-unbiased {n} (suc d) T p with is-linear-dec T
... | yes q = trans (cong (_∪ ewt empty) l1) (linear-tree-supp-lem d T ⦃ q ⦄ p)
  where
    open ≡-Reasoning

    l1 : FVTy (unbiased-type (suc d) T) ≡ supp-tree-bd d T false ∪ supp-tree-bd d T true
    l1 = begin
      FVTy (unbiased-type d T)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)
        ≡˘⟨ cong (λ - → - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
          ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)) (∪-idem (FVTy (unbiased-type d T))) ⟩
      FVTy (unbiased-type d T) ∪ FVTy (unbiased-type d T) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
        ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ solve (∪-monoid {suc n}) ⟩
      FVTy (unbiased-type d T)
      ∪ (FVTy (unbiased-type d T)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm))
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ cong (λ - → FVTy (unbiased-type d T) ∪ - ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)) (∪-comm _ _) ⟩
      FVTy (unbiased-type d T)
      ∪ (FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm)
      ∪ FVTy (unbiased-type d T))
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm) ≡⟨ solve (∪-monoid {suc n}) ⟩
      (FVTy (unbiased-type d T)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm))
      ∪ (FVTy (unbiased-type d T)
      ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm))
        ≡⟨ cong₂ _∪_ (supp-unbiased-lem d T (≤-trans (n≤1+n d) (≤-reflexive (sym p))) false) (supp-unbiased-lem d T (≤-trans (n≤1+n d) (≤-reflexive (sym p))) true) ⟩
      supp-tree-bd d T false ∪ supp-tree-bd d T true ∎

... | no q = begin
  FVTy (unbiased-type (suc d) T) ∪ FVSub idSub ≡⟨ cong (FVTy (unbiased-type (suc d) T) ∪_) idSub-supp ⟩
  FVTy (unbiased-type (suc d) T) ∪ full ≡⟨ ∪-right-zero (FVTy (unbiased-type (suc d) T)) ⟩
  full ∎
  where
    open ≡-Reasoning

unbiased-supp-condition : (d : ℕ) → (T : Tree n) → (tree-dim T ≡ suc d) → supp-condition true (unbiased-type (suc d) T) (tree-to-ctx T) ⦃ tree-to-pd T ⦄
unbiased-supp-condition d T p = nz ,, lem false ,, lem true
  where
    open ≡-Reasoning
    instance _ = tree-to-pd T

    nz : NonZero (ctx-dim (tree-to-ctx T))
    nz = NonZero-subst (trans (sym p) (sym (tree-dim-ctx-dim T))) it

    lem : (b : Bool) → FVTy (unbiased-type d T) ∪
           FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≡ pd-bd-supp (pred (ctx-dim (tree-to-ctx T))) (tree-to-ctx T) ⦃ tree-to-pd T ⦄ b
    lem b = begin
      FVTy (unbiased-type d T) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
        ≡⟨ supp-unbiased-lem d T (≤-trans (n≤1+n d) (≤-reflexive (sym p))) b ⟩
      supp-tree-bd d T b
        ≡⟨ cong (λ - → supp-tree-bd - T b) (cong pred (sym p)) ⟩
      supp-tree-bd (pred (tree-dim T)) T b
        ≡⟨ supp-compat (pred (tree-dim T)) T b ⟩
      pd-bd-supp (pred (tree-dim T)) (tree-to-ctx T) b
        ≡˘⟨ cong (λ - → pd-bd-supp (pred -) (tree-to-ctx T) b) (tree-dim-ctx-dim T) ⟩
      pd-bd-supp (pred (ctx-dim (tree-to-ctx T))) (tree-to-ctx T) b ∎

sub-from-linear-tree-supp-lem : (d d′ : ℕ)
                              → (S : Tree n) → .⦃ _ : is-linear S ⦄
                              → (T : Tree m)
                              → (b : Bool)
                              → (tree-dim T ≡ tree-dim S + d′)
                              → FVSub (sub-from-linear-tree-unbiased S T d′ ∘ tree-inc d S b) ≡ supp-tree-bd (d + d′) T b
sub-from-linear-tree-supp-lem zero d′ Sing T false p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub idSub
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) idSub-supp ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-tree-bd-full d′ T false (≤-reflexive p) ⟩
  supp-tree-bd d′ T false ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ Sing T true p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub idSub
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) idSub-supp ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-tree-bd-full d′ T true (≤-reflexive p) ⟩
  supp-tree-bd d′ T true ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ (Join S Sing) T false p = begin
  FVTy (unbiased-type d′ T) ∪ FVTm (getFst [ unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ]tm)
    ≡˘⟨ cong (λ - → FVTy (unbiased-type d′ T) ∪ FVTm -) (≃tm-to-≡ (unrestrict-fst (sub-from-linear-tree-unbiased S T (suc d′)))) ⟩
  FVTy (unbiased-type d′ T) ∪ FVTm (unbiased-term d′ (tree-bd d′ T) [ tree-inc d′ T false ]tm)
    ≡⟨ supp-unbiased-lem d′ T (≤-trans (m≤n+m d′ (suc (tree-dim S))) (≤-reflexive (sym p))) false ⟩
  supp-tree-bd d′ T false ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ (Join S Sing) T true p = begin
  FVTy (unbiased-type d′ T) ∪ (FVTm (getSnd [ unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ]tm))
    ≡˘⟨ cong (λ - → FVTy (unbiased-type d′ T) ∪ FVTm -) (≃tm-to-≡ (unrestrict-snd (sub-from-linear-tree-unbiased S T (suc d′)))) ⟩
  FVTy (unbiased-type d′ T) ∪ FVTm (unbiased-term d′ (tree-bd d′ T) [ tree-inc d′ T true ]tm)
    ≡⟨ supp-unbiased-lem d′ T (≤-trans (m≤n+m d′ (suc (tree-dim S))) (≤-reflexive (sym p))) true ⟩
  supp-tree-bd d′ T true ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem (suc d) d′ Sing T b p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub idSub
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) idSub-supp ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-tree-bd-full (suc d + d′) T b (≤-trans (≤-reflexive p) (m≤n+m d′ (suc d))) ⟩
  supp-tree-bd (suc d + d′) T b ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem (suc d) d′ (Join S Sing) T b p = begin
  FVSub (unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub ∘ suspSub (tree-inc d S b)))
    ≡⟨ cong FVSub (≃s-to-≡ lem) ⟩
  FVSub (unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b))
    ≡⟨ unrestrict-supp (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b) ⟩
  FVSub (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b)
    ≡⟨ sub-from-linear-tree-supp-lem d (suc d′) S T b (trans p (sym (+-suc (tree-dim S) d′))) ⟩
  supp-tree-bd (d + suc d′) T b
    ≡⟨ cong (λ - → supp-tree-bd - T b) (+-suc d d′) ⟩
  supp-tree-bd (suc d + d′) T b ∎
  where
    lem : unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub ∘ suspSub (tree-inc d S b))
       ≃s unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b)
    lem = begin
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub ∘ suspSub (tree-inc d S b)) >s
        ≈⟨ sub-action-≃-sub (id-left-unit (unrestrict (suspSubRes (tree-inc d S b)))) refl≃s ⟩
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ suspSub (tree-inc d S b) >s
        ≈˘⟨ unrestrict-comp (sub-from-linear-tree-unbiased S T (suc d′)) (tree-inc d S b) ⟩
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b) >s ∎
      where
        open Reasoning sub-setoid
    open ≡-Reasoning

sub-from-linear-tree-supp : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → (b : Bool) → (T : Tree m)
                          → tree-dim T ≡ tree-dim S
                          → TransportVarSet (supp-tree-bd d S b) (sub-from-linear-tree-unbiased S T 0) ≡ supp-tree-bd d T b
sub-from-linear-tree-supp d S b T p = begin
  TransportVarSet (supp-tree-bd d S b)
    (sub-from-linear-tree-unbiased S T 0)
    ≡˘⟨ cong
         (λ - → TransportVarSet - (sub-from-linear-tree-unbiased S T 0)) (supp-tree-bd-compat d S b) ⟩
  TransportVarSet (FVSub (tree-inc d S b))
    (sub-from-linear-tree-unbiased S T 0)
    ≡⟨ TransportVarSet-sub (tree-inc d S b) (sub-from-linear-tree-unbiased S T 0) ⟩
  FVSub (sub-from-linear-tree-unbiased S T 0 ∘ tree-inc d S b)
    ≡⟨ sub-from-linear-tree-supp-lem d 0 S T b (trans p (sym (+-identityʳ (tree-dim S)))) ⟩
  supp-tree-bd (d + 0) T b
    ≡⟨ cong (λ - → supp-tree-bd - T b) (+-identityʳ d) ⟩
  supp-tree-bd d T b ∎
  where
    open ≡-Reasoning
