{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax.Properties where

open import Catt.Syntax

open import Relation.Binary.PropositionalEquality
-- open import Catt.Dimension
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat

sub-dim : (σ : Sub n m ⋆) → (A : Ty n) → ty-dim A ≡ ty-dim (A [ σ ]ty)
sub-dim σ ⋆ = refl
sub-dim σ (s ─⟨ A ⟩⟶ t) = cong suc (sub-dim σ A)
