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

ewt : VarSet n → VarSet (suc n)
ewt xs = true ∷ xs

ewf : VarSet n → VarSet (suc n)
ewf xs = false ∷ xs

drop : VarSet n → VarSet n
drop {zero} [] = []
drop {suc n} (x ∷ v) = false ∷ v

trueAt : Fin n → VarSet n
trueAt {n = suc n} zero = ewt empty
trueAt {n = suc n} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet n → VarSet n → VarSet n
(f ∪ g) = zipWith _∨_ f g


-- supp : (x : Syntax) → VarSet (syntax-ctx x)
-- supp = wfRec _ (λ y → VarSet (syntax-ctx y)) γ
--   where
--     γ : (x : Syntax) →
--         ((y : Syntax) → y ≺⁺ x → VarSet (syntax-ctx y)) →
--         VarSet (syntax-ctx x)
--     γ (Context Γ) rec = full
--     γ (Type ⋆) rec = empty
--     γ (Type (s ─⟨ A ⟩⟶ t) ⦃ c = TyDimS ⦄) rec = rec (Type A) [ ty2 ]p ∪ rec (Term s) [ ty1 ]p ∪ rec (Term t) [ ty3 ]p
--     γ (Term (Var {Γ = Γ} i) ⦃ c = TmDimV ⦄) rec = (trueAt i) ∪ (rec (Type (Γ ‼ i) ⦃ c = lookupD Γ i ⦄) [ (dim ≤-refl) ]p)
--     γ (Term (Coh Δ A σ) ⦃ c = TmDimC ⦄) rec = rec (Substitution σ) [ tm3 ]p
--     γ (Substitution ⟨⟩) rec = empty
--     γ (Substitution ⟨ σ , t ⟩ ⦃ c = SubDimS ⦄) rec = (rec (Substitution σ) [ sub1 ]p) ∪ (rec (Term t) [ sub2 ]p)

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

-- suppCtx : (Γ : Ctx n) → VarSet Γ
-- suppTm : (t : Tm Γ) → VarSet Γ
-- suppTy : (A : Ty Γ d′) → VarSet Γ
-- suppSub : (σ : Sub Δ Γ) → VarSet Γ

-- suppCtx Γ = supp (Context Γ)
-- suppTm t = supp (Term t)
-- suppTy A = supp (Type A)
-- suppSub σ = supp (Substitution σ)

data _≃vs_ : VarSet n → VarSet n → Set where
  ≃VEmp : [] ≃vs []
  ≃VTrue : ∀ {xs ys : VarSet n} → xs ≃vs ys → ewt xs ≃vs ewt ys
  ≃VFalse : ∀ {xs ys : VarSet n} → xs ≃vs ys → ewf xs ≃vs ewf ys
