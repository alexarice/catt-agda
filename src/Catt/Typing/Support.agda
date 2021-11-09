{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toℕ)

module Catt.Typing.Support (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Data.Nat
open import Catt.Support
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
import Catt.Typing.Properties.Base as P
import Catt.Typing as T
open import Catt.Typing index rule

open Rule

modifyRule : Rule → Rule
modifyRule r .Args = Σ[ a ∈ r .Args ] SuppTm (r .tgtCtx a) (r .lhs a) ≡ SuppTm (r .tgtCtx a) (r .rhs a)
modifyRule r .len (a ,, p) = r .len a
modifyRule r .tgtCtx (a ,, p) = r .tgtCtx a
modifyRule r .lhs (a ,, p) = r .lhs a
modifyRule r .rhs (a ,, p) = r .rhs a

lift-modify : (∀ i a → P.LiftRule index rule {i} a) → ∀ i a → P.LiftRule index (λ i → modifyRule (rule i)) {i} a
lift-modify p i (fst ,, snd) {A} {C} x = {!!}
  where
    test : P.LiftRule index rule fst
    test = p i fst
