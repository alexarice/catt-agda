{-# OPTIONS --without-K --safe #-}

module Catt.FreeVars where

open import Data.Nat hiding (_+_)
open import Catt.Fin
open import Data.Unit
open import Data.Vec hiding (drop)
open import Data.Empty
open import Catt.Syntax
open import Data.Bool
open import Relation.Binary.PropositionalEquality

private
  variable
    n m dim : ℕ

FVSet : ℕ → Set
FVSet = Vec Bool

empty : FVSet n
empty = replicate false

full : FVSet n
full = replicate true

ewt : FVSet n → FVSet (suc n)
ewt xs = true ∷ xs

ewf : FVSet n → FVSet (suc n)
ewf xs = false ∷ xs

drop : FVSet (suc n) → FVSet (suc n)
drop (x ∷ xs) = false ∷ xs

trueAt : Fin n → FVSet n
trueAt (fromℕ n) = true ∷ empty
trueAt (inject i) = false ∷ trueAt i

infixl 60 _∪_
_∪_ : FVSet n → FVSet n → FVSet n
(f ∪ g) = zipWith _∨_ f g

FVCtx : Ctx n → FVSet n
FVTerm : Term n → FVSet n
FVTy : Ty n dim → FVSet n
FVSub : Sub m n → FVSet m

FVCtx Γ = full

FVTy ⋆ = empty
FVTy (x ─⟨ A ⟩⟶ y) = FVTy A ∪ FVTerm x ∪ FVTerm y

FVTerm (Var i) = trueAt i
FVTerm (Coh Γ A σ) = FVSub σ

FVSub ⟨⟩ = empty
FVSub ⟨ σ , t ⟩ = FVSub σ ∪ FVTerm t
