{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Tree
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

unbiased-type : (d : ℕ) → (T : Tree n) → Ty (suc n)
unbiased-term : (d : ℕ) → (T : Tree n) → Tm (suc n)

unbiased-type zero T = ⋆
unbiased-type (suc d) T = (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty ⟩⟶ (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)

unbiased-term d T with is-linear-dec T
... | yes p = 0V
... | no p = Coh T (unbiased-type d T) (idSub _)

unbiased-type-dim : (d : ℕ) → (T : Tree n) → ty-dim (unbiased-type d T) ≡ d
unbiased-type-dim zero T = refl
unbiased-type-dim (suc d) T = cong suc (trans (sym (sub-dim (tree-inc d T false) (unbiased-type d (tree-bd d T)))) (unbiased-type-dim d (tree-bd d T)))
