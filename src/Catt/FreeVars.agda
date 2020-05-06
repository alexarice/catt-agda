{-# OPTIONS --without-K --safe #-}

module Catt.FreeVars where

open import Data.Nat hiding (_+_)
open import Data.Fin hiding (_+_)
open import Data.Bool
open import Catt.Syntax

private
  variable
    n m : ℕ

FVSet : ℕ → Set
FVSet n = Fin n → Bool

empty : FVSet n
empty n = false

full : FVSet n
full n = true

ewf : FVSet n → FVSet (suc n)
ewf f = helper f false

ewt : FVSet n → FVSet (suc n)
ewt f = helper f true

sameF : Fin n → Fin n → Bool
sameF zero zero = true
sameF zero (suc g) = false
sameF (suc f) zero = false
sameF (suc f) (suc g) = sameF f g

sameB : Bool → Bool → Bool
sameB false b = not b
sameB true b = b

bigAnd : (Fin n → Bool) → Bool
bigAnd {zero} f = true
bigAnd {suc n} f = f zero ∧ bigAnd λ x → f (suc x)

isEqual : FVSet n → FVSet n → Bool
isEqual f g = bigAnd (λ x → sameB (f x) (g x))

infixl 4 _∪_
_∪_ : FVSet n → FVSet n → FVSet n
(f ∪ g) n = f n ∨ g n

Union : (Fin n → FVSet m) → FVSet m
Union {zero} f = empty
Union {suc n} f = (Union (λ x → f (suc x))) ∪ f zero

FVCtx : Ctx n → FVSet n
FVTerm : Term n → FVSet n
FVTy : Ty n → FVSet n
FVSub : Substitution m n → FVSet m

FVCtx Γ = full

FVTy ⋆ = empty
FVTy (x ─⟨ A ⟩⟶ y) = FVTy A ∪ FVTerm x ∪ FVTerm y

FVTerm (Var f) g = sameF f g
FVTerm (Coh Γ A σ) = FVSub σ
FVTerm (Comp Γ A t u σ) = FVSub σ

FVSub σ = Union (λ x → FVTerm (σ x))
