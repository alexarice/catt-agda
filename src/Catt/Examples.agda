{-# OPTIONS --without-K --safe #-}

module Catt.Examples where

open import Catt.Base
open import Data.Nat
open import Catt.Fin
open import Relation.Binary.PropositionalEquality

singleton : Ctx 1
singleton = ∅ , ⋆

singleton-type : singleton ⊢
singleton-type = TypeCtxStep ∅ (TypeTyStar TypeCtxBase)

singleton-typed : TypedCtx
singleton-typed .size = 1
singleton-typed .ctx = singleton
singleton-typed .typing-ctx = singleton-type

pd-singleton : singleton ⊢pd₀ 0
pd-singleton = Finish Base

id-on-x : Term 1
id-on-x = Coh singleton (Var (fromℕ 0) ─⟨ ⋆ ⟩⟶ Var (fromℕ 0)) (id-sub 1)

id-on-x-type : singleton ⊢ id-on-x ∷ Var (fromℕ 0) ─⟨ ⋆ ⟩⟶ Var (fromℕ 0)
id-on-x-type = TypeTermCoh pd-singleton (TypeTyArr (TypeTermVar (fromℕ 0) singleton-type) (TypeTermVar (fromℕ 0) singleton-type)) refl singleton-type (TypeSubStep TypeSubEmpty (TypeTyStar TypeCtxBase) (TypeTermVar (fromℕ 0) singleton-type))
