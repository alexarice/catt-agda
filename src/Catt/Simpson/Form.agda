{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.Form where

open import Data.Nat
open import Data.Nat.Properties
open import Catt.Fin
open import Data.List using (List; []; map) renaming (_∷_ to _::_)
open import Data.List.NonEmpty renaming (map to maptf)
open import Catt.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    n dim submax dim′ dim″ pdd : ℕ

data Form : ℕ → ℕ → ℕ → Set where
  Base : Term n → Ty n dim → Form n dim zero
  Com : List (Form n (suc dim′) dim′) → Form n dim dim′ → List (Form n (suc dim′) dim′) → Form n dim (suc dim′)

TopForm : ℕ → ℕ → Set
TopForm n zero = Form n 0 0
TopForm n (suc dim) = List⁺ (Form n (suc dim) dim)

get-tgt-of-form : Form n (suc dim) dim′ → Form n dim dim′
get-tgt-of-form (Base _ (t ─⟨ A ⟩⟶ u)) = Base u A
get-tgt-of-form (Com before focus after) = Com before (get-tgt-of-form focus) after

get-tgt-full : ∀ x → Form n (suc x + dim) dim → Form n dim dim
get-tgt-full zero f = get-tgt-of-form f
get-tgt-full {dim = dim} (suc x) f = get-tgt-full x (get-tgt-of-form f)

get-src-of-form : Form n (suc dim) dim′ → Form n dim dim′
get-src-of-form (Base _ (t ─⟨ A ⟩⟶ u)) = Base t A
get-src-of-form (Com before focus after) = Com before (get-src-of-form focus) after

get-src-full : ∀ x → Form n (suc x + dim) dim → Form n dim dim
get-src-full zero f = get-src-of-form f
get-src-full {dim = dim} (suc x) f = get-src-full x (get-src-of-form f)

to-top-form : Form n dim dim → TopForm n dim
to-top-form (Base x A) = Base x A
to-top-form (Com before focus after) = after ++⁺ focus ∷ before
