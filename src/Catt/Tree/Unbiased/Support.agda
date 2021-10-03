{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Support where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Data.Nat
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Support
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool using (Bool; true; false)
open import Tactic.MonoidSolver
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Suspension
open import Data.Fin using (fromℕ)
open import Catt.Variables
open import Catt.Connection
import Relation.Binary.Reasoning.Setoid as Reasoning

supp-unbiased-lem : (d : ℕ) → (T : Tree n) → .(suc d ≤ tree-dim T) → (b : Bool)
                  → FVTy (unbiased-type d T)
                  ∪ FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) ≡ supp-bd d T b
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
    ≡⟨ cong (λ - → TransportVarSet - (tree-inc d T b)) (supp-unbiased d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) p))) ⟩
  TransportVarSet full (tree-inc d T b) ≡⟨ TransportVarSet-full (tree-inc d T b) ⟩
  FVSub (tree-inc d T b) ≡⟨ supp-bd-compat d T b ⟩
  supp-bd d T b ∎
    where
      open ≡-Reasoning

supp-unbiased zero Sing p = refl
supp-unbiased zero (Join S T) p with .(join-tree-has-non-zero-dim S T (sym p))
... | ()
supp-unbiased {n} (suc d) T p with is-linear-dec T
... | yes q = trans (cong (_∪ ewt empty) l1) (linear-tree-supp-lem d T ⦃ q ⦄ p)
  where
    open ≡-Reasoning

    l1 : FVTy (unbiased-type (suc d) T) ≡ supp-bd d T false ∪ supp-bd d T true
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
        ≡⟨ cong₂ _∪_ (supp-unbiased-lem d T (≤-reflexive (sym p)) false) (supp-unbiased-lem d T (≤-reflexive (sym p)) true) ⟩
      supp-bd d T false ∪ supp-bd d T true ∎

... | no q = begin
  FVTy (unbiased-type (suc d) T) ∪ FVSub (idSub _) ≡⟨ cong (FVTy (unbiased-type (suc d) T) ∪_) (idSub-supp (suc _)) ⟩
  FVTy (unbiased-type (suc d) T) ∪ full ≡⟨ ∪-right-zero (FVTy (unbiased-type (suc d) T)) ⟩
  full ∎
  where
    open ≡-Reasoning

unbiased-supp-condition : (d : ℕ) → (T : Tree n) → (tree-dim T ≡ suc d) → supp-condition true (unbiased-type (suc d) T) T
unbiased-supp-condition d T p = nz ,, lem false ,, lem true
  where
    open ≡-Reasoning

    nz : NonZero′ (tree-dim T)
    nz = NonZero′-subst (sym p) it

    lem : (b : Bool) → FVTy (unbiased-type d T) ∪
           FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≡ supp-bd (pred (tree-dim T)) T b
    lem b = begin
      FVTy (unbiased-type d T) ∪
        FVTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
        ≡⟨ supp-unbiased-lem d T (≤-reflexive (sym p)) b ⟩
      supp-bd d T b
        ≡⟨ cong (λ - → supp-bd - T b) (cong pred (sym p)) ⟩
      supp-bd (pred (tree-dim T)) T b ∎

sub-from-linear-tree-supp-lem : (d d′ : ℕ)
                              → (S : Tree n) → .⦃ _ : is-linear S ⦄
                              → (T : Tree m)
                              → (b : Bool)
                              → (tree-dim T ≡ tree-dim S + d′)
                              → FVSub (sub-from-linear-tree-unbiased S T d′ ∘ tree-inc d S b) ≡ supp-bd (d + d′) T b
sub-from-linear-tree-supp-lem zero d′ Sing T false p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub (idSub _)
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) (idSub-supp _) ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-bd-full d′ T false (≤-reflexive p) ⟩
  supp-bd d′ T false ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ Sing T true p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub (idSub _)
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) (idSub-supp _) ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-bd-full d′ T true (≤-reflexive p) ⟩
  supp-bd d′ T true ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ (Join S Sing) T false p = begin
  FVTy (unbiased-type d′ T) ∪ FVTm (getFst [ unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ]tm)
    ≡˘⟨ cong (λ - → FVTy (unbiased-type d′ T) ∪ FVTm -) (≃tm-to-≡ (unrestrict-fst (sub-from-linear-tree-unbiased S T (suc d′)))) ⟩
  FVTy (unbiased-type d′ T) ∪ FVTm (unbiased-term d′ (tree-bd d′ T) [ tree-inc d′ T false ]tm)
    ≡⟨ supp-unbiased-lem d′ T (≤-trans (m≤n+m (suc d′) (tree-dim S)) (≤-reflexive (trans (+-suc (tree-dim S) d′) (sym p)))) false ⟩
  supp-bd d′ T false ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem zero d′ (Join S Sing) T true p = begin
  FVTy (unbiased-type d′ T) ∪ (FVTm (getSnd [ unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ]tm))
    ≡˘⟨ cong (λ - → FVTy (unbiased-type d′ T) ∪ FVTm -) (≃tm-to-≡ (unrestrict-snd (sub-from-linear-tree-unbiased S T (suc d′)))) ⟩
  FVTy (unbiased-type d′ T) ∪ FVTm (unbiased-term d′ (tree-bd d′ T) [ tree-inc d′ T true ]tm)
    ≡⟨ supp-unbiased-lem d′ T (≤-trans (m≤n+m (suc d′) (tree-dim S)) (≤-reflexive (trans (+-suc (tree-dim S) d′) (sym p)))) true ⟩
  supp-bd d′ T true ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem (suc d) d′ Sing T b p = begin
  FVTy (unbiased-type d′ T) ∪ FVSub (idSub _)
    ≡⟨ cong (FVTy (unbiased-type d′ T) ∪_) (idSub-supp _) ⟩
  FVTy (unbiased-type d′ T) ∪ full
    ≡⟨ ∪-right-zero (FVTy (unbiased-type d′ T)) ⟩
  full
    ≡˘⟨ supp-bd-full (suc d + d′) T b (≤-trans (≤-reflexive p) (m≤n+m d′ (suc d))) ⟩
  supp-bd (suc d + d′) T b ∎
  where
    open ≡-Reasoning
sub-from-linear-tree-supp-lem (suc d) d′ (Join S Sing) T b p = begin
  FVSub (unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub _ ∘ suspSub (tree-inc d S b)))
    ≡⟨ cong FVSub (≃s-to-≡ lem) ⟩
  FVSub (unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b))
    ≡⟨ unrestrict-supp (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b) ⟩
  FVSub (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b)
    ≡⟨ sub-from-linear-tree-supp-lem d (suc d′) S T b (trans p (sym (+-suc (tree-dim S) d′))) ⟩
  supp-bd (d + suc d′) T b
    ≡⟨ cong (λ - → supp-bd - T b) (+-suc d d′) ⟩
  supp-bd (suc d + d′) T b ∎
  where
    lem : unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub _ ∘ suspSub (tree-inc d S b))
       ≃s unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b)
    lem = begin
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ (idSub _ ∘ suspSub (tree-inc d S b)) >s
        ≈⟨ sub-action-≃-sub (id-left-unit (unrestrict (suspSubRes (tree-inc d S b)))) refl≃s ⟩
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′)) ∘ suspSub (tree-inc d S b) >s
        ≈˘⟨ unrestrict-comp (sub-from-linear-tree-unbiased S T (suc d′)) (tree-inc d S b) ⟩
      < unrestrict (sub-from-linear-tree-unbiased S T (suc d′) ∘ tree-inc d S b) >s ∎
      where
        open Reasoning sub-setoid
    open ≡-Reasoning

-- sub-from-linear-tree-supp-lem zero zero Sing Sing false p q = refl
-- sub-from-linear-tree-supp-lem zero zero Sing Sing true p q = refl
-- sub-from-linear-tree-supp-lem zero zero Sing (Join T₁ T₂) b p q with tree-dim T₂
-- sub-from-linear-tree-supp-lem zero zero Sing (Join T₁ T₂) b () q | zero
-- sub-from-linear-tree-supp-lem zero zero Sing (Join T₁ T₂) b () q | suc x
-- sub-from-linear-tree-supp-lem zero zero (Join S Sing) T false p q = begin
--   empty ∪ FVTm (Var (fromℕ _) [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)
--     ≡⟨ ∪-left-unit (FVTm (Var (fromℕ _) [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)) ⟩
--   FVTm (Var (fromℕ _) [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)
--     ≡˘⟨ cong FVTm (≃tm-to-≡ (unrestrict-fst (sub-from-linear-tree-unbiased S T 1))) ⟩
--   FVTm (unbiased-term 0 (tree-bd 0 T) [ tree-inc 0 T false ]tm) ≡⟨⟩
--   supp-bd zero T false ∎
--   where
--     open ≡-Reasoning
-- sub-from-linear-tree-supp-lem zero zero (Join S Sing) T true p q = let
--   instance _ = tree-last-var-is-var T
--   in begin
--   empty ∪ FVTm (getSnd [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)
--     ≡⟨ ∪-left-unit (FVTm (getSnd [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)) ⟩
--   FVTm (getSnd [ unrestrict (sub-from-linear-tree-unbiased S T 1) ]tm)
--     ≡˘⟨ cong FVTm (≃tm-to-≡ (unrestrict-snd (sub-from-linear-tree-unbiased S T 1))) ⟩
--   FVTm (unbiased-term 0 (tree-bd 0 T) [ tree-inc 0 T true ]tm) ≡⟨⟩
--   FVTm (tree-last-var T)
--     ≡⟨ isVar-supp (tree-last-var T) ⟩
--   trueAt (getVarFin (tree-last-var T)) ∎
--   where
--     open ≡-Reasoning
-- sub-from-linear-tree-supp-lem (suc d) d′ Sing T b p q = {!!}
-- sub-from-linear-tree-supp-lem (suc d) d′ (Join S Sing) T b p q = {!!}

sub-from-linear-tree-supp : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → (b : Bool) → (T : Tree m)
                          → tree-dim T ≡ tree-dim S
                          → TransportVarSet (supp-bd d S b) (sub-from-linear-tree-unbiased S T 0) ≡ supp-bd d T b
sub-from-linear-tree-supp d S b T p = begin
  TransportVarSet (supp-bd d S b)
    (sub-from-linear-tree-unbiased S T 0)
    ≡˘⟨ cong
         (λ - → TransportVarSet - (sub-from-linear-tree-unbiased S T 0)) (supp-bd-compat d S b) ⟩
  TransportVarSet (FVSub (tree-inc d S b))
    (sub-from-linear-tree-unbiased S T 0)
    ≡⟨ TransportVarSet-sub (tree-inc d S b) (sub-from-linear-tree-unbiased S T 0) ⟩
  FVSub (sub-from-linear-tree-unbiased S T 0 ∘ tree-inc d S b)
    ≡⟨ sub-from-linear-tree-supp-lem d 0 S T b (trans p (sym (+-identityʳ (tree-dim S)))) ⟩
  supp-bd (d + 0) T b
    ≡⟨ cong (λ - → supp-bd - T b) (+-identityʳ d) ⟩
  supp-bd d T b ∎
  where
    open ≡-Reasoning
