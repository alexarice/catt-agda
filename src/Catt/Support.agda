{-# OPTIONS --without-K --safe #-}

module Catt.Support where

open import Data.Nat hiding (_+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec hiding (drop ; [_])
open import Catt.Syntax
open import Catt.Dimension
open import Data.Bool
open import Data.Fin

record VarSet (Γ : Ctx n) : Set where
  constructor [_]v
  field
    get : Vec Bool (ctxLength Γ)

empty : VarSet Γ
empty = [ replicate false ]v

full : VarSet Γ
full = [ replicate true ]v

ewt : {A : Ty Γ n} → VarSet Γ → VarSet (Γ , A)
ewt [ xs ]v = [ true ∷ xs ]v

ewf : {A : Ty Γ n} → VarSet Γ → VarSet (Γ , A)
ewf [ xs ]v = [ false ∷ xs ]v

drop : VarSet Γ → VarSet Γ
drop {zero} [ [] ]v = [ [] ]v
drop {suc _} [ x ∷ v ]v = [ false ∷ v ]v

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
    γ (Type (s ─⟨ A ⟩⟶ t)) rec = rec (Type A) [ ty2 ]p ∪ rec (Term s) [ ty1 ]p ∪ rec (Term t) [ ty3 ]p
    γ (Term (Var {Γ = Γ} i)) rec = (trueAt i) ∪ (rec (Type (Γ ‼ i)) [ (dim ≤-refl) ]p)
    γ (Term (Coh Δ A p σ)) rec = rec (Substitution σ) [ tm3 ]p
    γ (Substitution ⟨⟩) rec = empty
    γ (Substitution ⟨ σ , t ⟩) rec = (rec (Substitution σ) [ sub1 ]p) ∪ (rec (Term t) [ sub2 ]p)

suppCtx : (Γ : Ctx n) → VarSet Γ
suppTm : Tm Γ n → VarSet Γ
suppTy : Ty Γ n → VarSet Γ
suppSub : Sub Δ Γ → VarSet Γ

suppCtx Γ = supp (Context Γ)
suppTm t = supp (Term t)
suppTy A = supp (Type A)
suppSub σ = supp (Substitution σ)
