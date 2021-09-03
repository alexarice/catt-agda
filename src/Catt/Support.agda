{-# OPTIONS --without-K --safe #-}

module Catt.Support where

open import Data.Nat hiding (_+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec hiding (drop ; [_])
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Dimension
open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.Unit

record VarSet (Γ : Ctx) : Set where
  constructor [_]v
  field
    get : Vec Bool (ctxLength Γ)

empty : VarSet Γ
empty = [ replicate false ]v

full : VarSet Γ
full = [ replicate true ]v

ewt : {A : Ty Γ d} → VarSet Γ → VarSet (Γ , A)
ewt [ xs ]v = [ true ∷ xs ]v

ewf : {A : Ty Γ d} → VarSet Γ → VarSet (Γ , A)
ewf [ xs ]v = [ false ∷ xs ]v

drop : VarSet Γ → VarSet Γ
drop {∅} [ [] ]v = [ [] ]v
drop {_ , _} [ x ∷ v ]v = [ false ∷ v ]v

trueAt : Fin (ctxLength Γ) → VarSet Γ
trueAt {Γ = Γ , A} zero = ewt empty
trueAt {Γ = Γ , A} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet Γ → VarSet Γ → VarSet Γ
([ f ]v ∪ [ g ]v) = [ zipWith _∨_ f g ]v


supp : (x : Syntax) → VarSet (syntax-ctx x)
supp = wfRec _ (λ y → VarSet (syntax-ctx y)) γ
  where
    γ : (x : Syntax) →
        ((y : Syntax) → y ≺⁺ x → VarSet (syntax-ctx y)) →
        VarSet (syntax-ctx x)
    γ (Context Γ) rec = full
    γ (Type ⋆) rec = empty
    γ (Type (s ─⟨ A ⟩⟶ t) ⦃ c = TyDimS ⦄) rec = rec (Type A) [ ty2 ]p ∪ rec (Term s) [ ty1 ]p ∪ rec (Term t) [ ty3 ]p
    γ (Term (Var {Γ = Γ} i) ⦃ c = TmDimV ⦄) rec = (trueAt i) ∪ (rec (Type (Γ ‼ i) ⦃ c = lookupD Γ i ⦄) [ (dim ≤-refl) ]p)
    γ (Term (Coh Δ A σ) ⦃ c = TmDimC ⦄) rec = rec (Substitution σ) [ tm3 ]p
    γ (Substitution ⟨⟩) rec = empty
    γ (Substitution ⟨ σ , t ⟩ ⦃ c = SubDimS ⦄) rec = (rec (Substitution σ) [ sub1 ]p) ∪ (rec (Term t) [ sub2 ]p)

suppCtx : (Γ : Ctx) → ⦃ _ : CtxDim Γ d ⦄ → VarSet Γ
suppTm : .⦃ _ : CtxDim Γ d ⦄ → (t : Tm Γ) → ⦃ TmDim t n ⦄ → VarSet Γ
suppTy : .⦃ _ : CtxDim Γ d ⦄ → (A : Ty Γ d′) → ⦃ TyDim A n ⦄ → VarSet Γ
suppSub : .⦃ _ : CtxDim Δ d′ ⦄ → .⦃ _ : CtxDim Γ d ⦄ → (σ : Sub Δ Γ) → ⦃ _ : SubDim σ n ⦄ → VarSet Γ

suppCtx Γ = supp (Context Γ)
suppTm t = supp (Term t)
suppTy A = supp (Type A)
suppSub σ = supp (Substitution σ)

data _≃vs_ : VarSet Γ → VarSet Γ → Set where
  ≃VEmp : _≃vs_ {Γ = ∅} [ [] ]v [ [] ]v
  ≃VTrue : ∀ {xs ys : VarSet Γ} → xs ≃vs ys → ewt {A = A} xs ≃vs ewt ys
  ≃VFalse : ∀ {xs ys : VarSet Γ} → xs ≃vs ys → ewf {A = A} xs ≃vs ewf ys
