{-# OPTIONS --without-K --safe #-}

module Catt.Examples where

open import Catt.Base
open import Data.Nat
open import Catt.Fin

singleton : Ctx 1
singleton .get i = ⋆

singleton-typed : TypedCtx
singleton-typed .size = 1
singleton-typed .ctx = singleton
singleton-typed .typing-ctx = TypeCtxStep singleton (TypeTyStar (TypeCtxBase _))

pd-singleton : singleton ⊢pd₀ 0
pd-singleton = Finish (Base singleton)

id-on-x : Term 1
id-on-x = Coh singleton (Var (fromℕ 0) ─⟨ ⋆ ⟩⟶ Var (fromℕ 0)) (id-sub 1)
