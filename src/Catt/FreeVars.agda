{-# OPTIONS --without-K --safe #-}

module Catt.FreeVars where

open import Data.Nat hiding (_+_)
open import Catt.Fin
open import Catt.Vec.Functional
open import Data.Unit
open import Data.Empty
open import Catt.Syntax
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

private
  variable
    n m : ℕ

FVSet : ℕ → Set₁
FVSet n = Vector Set n

empty : FVSet n
empty .get f = ⊥

full : FVSet n
full .get f = ⊤

ewf : FVSet n → FVSet (suc n)
ewf xs = add xs ⊤

ewt : FVSet n → FVSet (suc n)
ewt xs = add xs ⊥

drop : FVSet (suc n) → FVSet (suc n)
drop f = ewf (front f)

infixl 60 _∪_
_∪_ : FVSet n → FVSet n → FVSet n
(f ∪ g) .get n = get f n ⊎ get g n

FVCtx : Ctx n → FVSet n
FVTerm : Term n → FVSet n
FVTy : Ty n → FVSet n
FVSub : Sub m n → FVSet m

FVCtx Γ = full

FVTy ⋆ = empty
FVTy (x ─⟨ A ⟩⟶ y) = FVTy A ∪ FVTerm x ∪ FVTerm y

FVTerm (Var f) .get g = f ≡ g
FVTerm (Coh Γ A σ) = FVSub σ

FVSub {n = n} σ .get i = Σ[ j ∈ Fin n ] get (FVTerm (get σ j)) i

sameB : ∀ {a} → Set a → Set a → Set a
sameB a b = (a → b) × (b → a)

_≡fv_ : FVSet n → FVSet n → Set
f ≡fv g = ∀ i → sameB (get f i) (get g i)
