{-# OPTIONS --without-K --safe #-}

module Catt.FreeVars where

open import Data.Nat hiding (_+_)
open import Catt.Fin
open import Catt.Vec.Functional
open import Data.Unit
open import Data.Empty
open import Catt.Syntax
open import Data.Bool
open import Relation.Binary.PropositionalEquality

private
  variable
    n m : ℕ

FVSet : ℕ → Set
FVSet n = Vector Bool n

empty : FVSet n
empty .get f = false

full : FVSet n
full .get f = true

ewf : FVSet n → FVSet (suc n)
ewf xs = add xs false

ewt : FVSet n → FVSet (suc n)
ewt xs = add xs true

drop : FVSet (suc n) → FVSet (suc n)
drop f = ewf (front f)

infixl 60 _∪_
_∪_ : FVSet n → FVSet n → FVSet n
(f ∪ g) .get n = get f n ∨ get g n

FVCtx : Ctx n → FVSet n
FVTerm : Term n → FVSet n
FVTy : Ty n → FVSet n
FVSub : Sub m n → FVSet m

FVCtx Γ = full

FVTy ⋆ = empty
FVTy (x ─⟨ A ⟩⟶ y) = FVTy A ∪ FVTerm x ∪ FVTerm y

FVTerm (Var x) .get i = sameF x i
FVTerm (Coh Γ A σ) = FVSub σ

FVSub ⟨⟩ = empty
FVSub ⟨ σ , t ⟩ = FVSub σ ∪ FVTerm t

_≡fv_ : FVSet n → FVSet n → Set
f ≡fv g = ∀ i → get f i ≡ get g i
