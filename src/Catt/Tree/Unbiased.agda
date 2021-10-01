{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased where

open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Catt.Discs
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Catt.Suspension

unbiased-type : (d : ℕ) → (T : Tree n) → Ty (suc n)
unbiased-term : (d : ℕ) → (T : Tree n) → Tm (suc n)
unbiased-comp : (d : ℕ) → (T : Tree n) → Sub (suc n) m ⋆ → Tm m

unbiased-type zero T = ⋆
unbiased-type (suc d) T = (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty ⟩⟶ (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)

unbiased-term d T with is-linear-dec T
... | yes p = 0V
... | no p = unbiased-comp d T (idSub _)

unbiased-comp d T σ = Coh T (unbiased-type d T) σ

unbiased-type-dim : (d : ℕ) → (T : Tree n) → ty-dim (unbiased-type d T) ≡ d
unbiased-type-dim zero T = refl
unbiased-type-dim (suc d) T = cong suc (trans (sym (sub-dim (tree-inc d T false) (unbiased-type d (tree-bd d T)))) (unbiased-type-dim d (tree-bd d T)))

unbiased-comp-dim : (d : ℕ) → (T : Tree n) → (σ : Sub (suc n) m ⋆) → (Δ : Ctx m) → tm-height Δ (unbiased-comp d T σ) ≡ d
unbiased-comp-dim d T σ Δ = trans (sym (sub-dim σ (unbiased-type d T))) (unbiased-type-dim d T)

sub-from-disc-unbiased : (d : ℕ) → Tree m → Sub (disc-size d) (suc m) ⋆
sub-from-disc-unbiased d T = sub-from-disc d (unbiased-type d T) (unbiased-type-dim d T) (unbiased-comp d T (idSub _))

sub-from-sphere-unbiased : (d : ℕ) → (T : Tree m) → Sub (sphere-size d) (suc m) ⋆
sub-from-sphere-unbiased d T = sub-from-sphere d (unbiased-type d T) (unbiased-type-dim d T)

unbiased-type′ : (d : ℕ) → (T : Tree n) → Ty (suc n)
unbiased-term′ : (d : ℕ) → (T : Tree n) → Tm (suc n)
unbiased-comp′ : (d : ℕ) → (T : Tree n) → Tm (suc n)

unbiased-term′ d T with is-linear-dec T
... | yes p = 0V
... | no p = unbiased-comp′ d T

unbiased-comp′ d T = Coh T (unbiased-type′ d T) (idSub _)

unbiased-type′ zero T = ⋆
unbiased-type′ (suc d) T = (unbiased-term′ d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type′ d T ⟩⟶ (unbiased-term′ d (tree-bd d T) [ tree-inc d T true ]tm)

sub-from-linear-tree-unbiased : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → Sub (suc n) (suc m) (unbiased-type′ d T)
sub-from-linear-tree-unbiased Sing T d = ⟨ ⟨⟩ , (unbiased-comp d T (idSub _)) ⟩
sub-from-linear-tree-unbiased (Join S Sing) T d = unrestrict (sub-from-linear-tree-unbiased S T (suc d))
