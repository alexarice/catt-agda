{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : (i : Fin index) → Catt. index rule i) where

open import Catt.Typing.Properties.Base index rule public

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
