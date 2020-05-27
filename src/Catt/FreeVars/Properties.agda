{-# OPTIONS --without-K --safe #-}

module Catt.FreeVars.Properties where

open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Catt.FreeVars
open import Data.Bool.Properties
open import Data.Vec
open import Data.Vec.Properties

_≡fv?_ : ∀ {n} → DecidableEquality (FVSet n)
_≡fv?_ = ≡-dec _≟_
