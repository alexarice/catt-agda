{-# OPTIONS --without-K --safe #-}

module Catt.Support where

open import Data.Nat hiding (_+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec hiding (drop ; [_])
open import Catt.Syntax
open import Catt.Syntax.Properties
-- open import Catt.Dimension
open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.Unit
open import Catt.Globular

-- record VarSet (Γ : Ctx n) : Set where
--   constructor [_]v
--   field
--     get : Vec Bool (ctxLength Γ)

VarSet : ℕ → Set
VarSet = Vec Bool

empty : VarSet n
empty = replicate false

full : VarSet n
full = replicate true

pattern ewt xs = true ∷ xs
pattern ewf xs = false ∷ xs
pattern emp = []

drop : VarSet n → VarSet n
drop {zero} [] = []
drop {suc n} (x ∷ v) = false ∷ v

trueAt : Fin n → VarSet n
trueAt {n = suc n} zero = ewt empty
trueAt {n = suc n} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet n → VarSet n → VarSet n
(f ∪ g) = zipWith _∨_ f g

FVCtx : (Γ : Ctx n) → VarSet n
FVTm : (t : Tm n) → VarSet n
FVTy : (A : Ty n d′) → VarSet n
FVSub : (σ : Sub n m) → VarSet m

FVCtx Γ = full
FVTm (Var i) = trueAt i
FVTm (Coh Δ A σ) = FVSub σ
FVTy ⋆ = empty
FVTy (s ─⟨ A ⟩⟶ t) = FVTy A ∪ FVTm s ∪ FVTm t
FVSub ⟨⟩ = empty
FVSub ⟨ σ , t ⟩ = FVSub σ ∪ FVTm t

TransportVarSet : VarSet n → Sub n m → VarSet m
TransportVarSet xs ⟨⟩ = empty
TransportVarSet (ewf xs) ⟨ σ , t ⟩ = TransportVarSet xs σ
TransportVarSet (ewt xs) ⟨ σ , t ⟩ = TransportVarSet xs σ ∪ FVTm t
