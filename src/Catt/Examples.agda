{-# OPTIONS --without-K --safe #-}

module Catt.Examples where

open import Catt.Base
open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns

singleton : Ctx 1
singleton zero = ⋆

pd-singleton : PD singleton 0
pd-singleton = Finish (Base singleton)

id-on-x : Term 1
id-on-x = Coh singleton (Var 0F ─⟨ ⋆ ⟩⟶ Var 0F) {!!}
