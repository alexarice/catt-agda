{-# OPTIONS --safe --without-K #-}

module Catt.Examples.WhiskerL where

open import Catt.Base
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Catt.Examples.Base
open import Catt.Examples.Composition

private
  variable
    n dim′-1 dim-1 : ℕ

whisker-l-ctx : (dim′-1 dim-1 : ℕ) → Ctx (3 + dim-1 * 2 + (4 + (dim′-1 * 2)))
whisker-l-ctx dim′-1 dim-1 = build-disk-on-ctx (2-comp dim′-1) (suc dim-1)

whisker-l-pd : (dim′-1 dim-1 : ℕ) → (whisker-l-ctx dim′-1 dim-1) ⊢pd₀ (suc dim-1 + suc dim′-1)
whisker-l-pd dim′-1 dim-1 = Finish (proj₂ (proj₂ γ))
  where
    γ : Σ[ submax ∈ ℕ ] Σ[ x ∈ Term _ ] whisker-l-ctx dim′-1 dim-1 ⊢pd x ∷ ⋆
                [ submax ][ suc dim-1 + suc dim′-1 ]
    γ = reduce-to-0 (build-disk-on-ctx-pd (2-comp-pdb dim′-1) (suc dim-1))

whisker-l : TermAndType n (suc dim′-1) → TermAndType n (suc dim-1 + suc dim′-1) → TermAndType n (suc dim-1 + suc dim′-1)
whisker-l {n} {dim′-1} {dim-1} A B = (Coh (whisker-l-ctx dim′-1 dim-1) {!!} {!!}) ,, {!!}
