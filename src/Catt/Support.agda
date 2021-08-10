{-# OPTIONS --without-K --safe #-}

module Catt.Support where

open import Data.Nat hiding (_+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec hiding (drop)
open import Data.Wrap renaming ([_] to [_]w)
open import Catt.Syntax
open import Catt.Dimension
open import Data.Bool
open import Data.Fin

VarSet′ : Ctx → Set
VarSet′ Γ = Vec Bool (ctxLength Γ)

VarSet = Wrap VarSet′

empty : VarSet Γ
empty = [ replicate false ]w

full : VarSet Γ
full = [ replicate true ]w

ewt : {A : Ty Γ n} → VarSet Γ → VarSet (Γ , A)
ewt [ xs ]w = [ true ∷ xs ]w

ewf : {A : Ty Γ n} → VarSet Γ → VarSet (Γ , A)
ewf [ xs ]w = [ false ∷ xs ]w

drop : VarSet Γ → VarSet Γ
drop {∅} [ [] ]w = [ [] ]w
drop {Γ , A} [ x ∷ v ]w = [ false ∷ v ]w

trueAt : Fin (ctxLength Γ) → VarSet Γ
trueAt {Γ , A} zero = ewt empty
trueAt {Γ , A} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet Γ → VarSet Γ → VarSet Γ
([ f ]w ∪ [ g ]w) = [ zipWith _∨_ f g ]w

supp : (x : Syntax) → VarSet (syntax-ctx x)
supp = wfRec _ (λ y → VarSet (syntax-ctx y)) γ
  where
    γ : (x : Syntax) →
        ((y : Syntax) → y ≺⁺ x → VarSet (syntax-ctx y)) →
        VarSet (syntax-ctx x)
    γ (Context Γ) rec = full
    γ (Type ⋆) rec = empty
    γ (Type (s ─⟨ A ⟩⟶ t)) rec = rec (Type A) [ ty2 ]p ∪ rec (Term s) [ ty1 ]p ∪ rec (Term t) [ ty3 ]p
    γ (Term (Var {Γ} i)) rec = (trueAt i) ∪ (rec (Type (Γ ‼ i)) [ (dim ≤-refl) ]p)
    γ (Term (Coh Δ A σ)) rec = rec (Substitution σ) [ tm3 ]p
    γ (Substitution ⟨⟩) rec = empty
    γ (Substitution ⟨ σ , t ⟩) rec = (rec (Substitution σ) [ sub1 ]p) ∪ (rec (Term t) [ sub2 ]p)

suppCtx : (Γ : Ctx) → VarSet Γ
suppTm : Tm Γ n → VarSet Γ
suppTy : Ty Γ n → VarSet Γ
suppSub : Sub Δ Γ → VarSet Γ

suppCtx Γ = supp (Context Γ)
suppTm t = supp (Term t)
suppTy A = supp (Type A)
suppSub σ = supp (Substitution σ)
