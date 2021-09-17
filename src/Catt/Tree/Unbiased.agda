{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased where

open import Catt.Syntax
open import Catt.Tree
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary

unbiased-type : (d : ℕ) → (T : Tree n) → Ty (suc n) d
unbiased-term : (d : ℕ) → (T : Tree n) → Tm (suc n)

unbiased-type zero T = ⋆
unbiased-type (suc d) T = (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty ⟩⟶ (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)

unbiased-term d T with is-linear-dec T
... | yes p = 0V
... | no p = Coh T (unbiased-type d T) (idSub _)
