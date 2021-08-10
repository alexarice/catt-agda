{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.Form.Typing where

import Catt.Simpson.Form
open import Catt.Base
open import Data.Nat
open import Data.List using (List; []; map) renaming (_∷_ to _::_)
open import Data.List.NonEmpty renaming (map to maptf; _∷_ to _∷n_)
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Relation.Binary.PropositionalEquality

private
  variable
    n dim dim′ : ℕ

mutual
  TypedListBefore : Ctx n → TopForm n dim → List (Form n (suc dim) dim) → Set
  TypedListBefore Γ tf [] = ⊤
  TypedListBefore Γ tf (x :: xs) = Γ ⊢f x × to-top-form (get-tgt-of-form x) ≡ tf × TypedListBefore Γ (to-top-form (get-src-of-form x)) xs

  TypedListAfter : Ctx n → TopForm n dim → List (Form n (suc dim) dim) → Set
  TypedListAfter Γ tf [] = ⊤
  TypedListAfter Γ tf (x :: []) = Γ ⊢f x × to-top-form (get-src-of-form x) ≡ tf
  TypedListAfter Γ tf (x :: y :: xs) = Γ ⊢f x × to-top-form (get-src-of-form x) ≡ to-top-form (get-tgt-of-form y) × TypedListAfter Γ tf (y :: xs)

  data _⊢f_ (Γ : Ctx n) : Form n dim dim′ → Set where
    TypeFormBase : {x : Term n} → {A : Ty n (suc dim)} → Γ ⊢ x ∷ A → Γ ⊢f Base x A
    TypeFormCom : ∀ {i} →
                  (before : List (Form n (suc dim) dim)) →
                  (focus : Form n (suc i + dim) dim) →
                  (after : List (Form n (suc dim) dim)) →
                  Γ ⊢f focus →
                  TypedListBefore Γ (to-top-form (get-src-full i focus)) before →
                  TypedListAfter Γ (to-top-form (get-tgt-full i focus)) after →
                  Γ ⊢f Com before focus after
