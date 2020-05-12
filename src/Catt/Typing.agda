{-# OPTIONS --without-K --safe #-}

module Catt.Typing where

open import Data.Nat hiding (_+_)
open import Data.Fin hiding (_+_; pred)
open import Data.Fin.Patterns
open import Data.Bool
open import Catt.Syntax
open import Catt.FreeVars

private
  variable
    n m l dim submax : ℕ

data TypeCtx : Ctx n → Set
data TypeTy : Ctx n → Ty n → Set
data TypeTerm : Ctx n → Term n → Ty n → Set
data TypeSub : Ctx m → Ctx n → Substitution m n → Set
data PD : Ctx n → ℕ → Set

FVSrc : {Γ : Ctx n} → PD Γ dim → FVSet n
FVTgt : {Γ : Ctx n} → PD Γ dim → FVSet n

infixr 9 _[_]ty _[_]tm
_[_]ty : Ty n → Substitution m n → Ty m
_[_]tm : Term n → Substitution m n → Term m
infixl 4 _∘_
_∘_ : Substitution l m → Substitution m n → Substitution l n

data TypeCtx where
  TypeCtxEmpty : (Γ : Ctx 0) → TypeCtx Γ
  TypeCtxStep : {Γ : Ctx n} → {A : Ty n} → TypeTy Γ A → TypeCtx (extendC Γ A)

data TypeTy where
  TypeTyStar : {Γ : Ctx n} → TypeCtx Γ → TypeTy Γ ⋆
  TypeTyArr : {Γ : Ctx n} → {A : Ty n} → {t u : Term n} → TypeTerm Γ t A → TypeTerm Γ u A → TypeTy Γ (t ─⟨ A ⟩⟶ u)

data TypeTerm where
  TypeTermVar : {Γ : Ctx n} → (x : Fin n) → TypeTerm Γ (Var x) (Γ x)
  TypeTermCoh : {Γ : Ctx n} →
                {pd : PD Γ dim} →
                {A : Ty n} →
                TypeTy Γ A →
                {Δ : Ctx m} →
                {σ : Substitution m n} →
                TypeSub Δ Γ σ →
                T (isEqual (FVCtx Γ) (FVTy A)) →
                TypeTerm Δ (Coh Γ A σ) (A [ σ ]ty)
  TypeTermComp : {Γ : Ctx n} →
                 {pd : PD Γ dim} →
                 {A : Ty n} →
                 {t u : Term n} →
                 TypeTy Γ (t ─⟨ A ⟩⟶ u) →
                 TypeTerm Γ t A →
                 TypeTerm Γ u A →
                 T (isEqual (FVSrc pd) (FVTerm t)) →
                 T (isEqual (FVTgt pd) (FVTerm u)) →
                 {Δ : Ctx m} →
                 {σ : Substitution m n} →
                 TypeTerm Δ (Comp Γ A t u σ) ((t ─⟨ A ⟩⟶ u) [ σ ]ty)




data TypeSub where
  TypeSubEmpty : {Δ : Ctx m} {Γ : Ctx 0} (σ : Substitution m 0) → TypeSub Δ Γ σ
  TypeSubStep : {Δ : Ctx m} {Γ : Ctx n} {σ : Substitution m n} → TypeSub Δ Γ σ → {A : Ty n} → TypeTy Γ A → {t : Term m} → TypeTerm Δ t (A [ σ ]ty) → TypeSub Δ (extendC Γ A) (extendS σ t)

⋆ [ σ ]ty = ⋆
(t ─⟨ A ⟩⟶ u) [ σ ]ty = (t [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (u [ σ ]tm)

Var x [ σ ]tm = σ x
Coh Γ A τ [ σ ]tm = Coh Γ A (σ ∘ τ)
Comp Γ A t u τ [ σ ]tm = Comp Γ A t u (σ ∘ τ)

(τ ∘ σ) x = (σ x) [ τ ]tm

data PDB : Ctx n → Term n → Ty n → ℕ → Set where
  Base : (Γ : Ctx 1) → PDB Γ (Var 0F) ⋆ 0
  Extend : {Γ : Ctx n} →
           {A : Ty n} →
           {x : Term n} →
           PDB Γ x A submax →
           PDB (extendC (extendC Γ A) ((liftTerm x) ─⟨ (liftType A) ⟩⟶ (Var (fromℕ n)))) (Var zero) ((liftTerm (liftTerm x)) ─⟨ (liftType (liftType A)) ⟩⟶ (Var (inject₁ (fromℕ n)))) (pred submax)
  Restr : {Γ : Ctx n} →
          {f x y : Term n} →
          {A : Ty n} →
          PDB Γ f (x ─⟨ A ⟩⟶ y) submax →
          PDB Γ y A (suc submax)

data PD where
  Finish : {Γ : Ctx n} → {x : Term n} → {dim : ℕ} → PDB Γ x ⋆ dim → PD Γ dim

FVSrc-b : {Γ : Ctx n} → {x : Term n} → {A : Ty n} → PDB Γ x A submax → FVSet n
FVSrc-b (Base _) = empty
FVSrc-b (Extend {submax = zero} pdb) = ewf (ewf full)
FVSrc-b (Extend {submax = suc zero} pdb) = ewf (ewf (FVSrc-b pdb))
FVSrc-b (Extend {submax = suc (suc _)} pdb) = ewt (ewt (FVSrc-b pdb))
FVSrc-b (Restr pdb) = FVSrc-b pdb

drop′ : FVSet (suc n) → FVSet (suc n)
drop′ f = ewf (λ x → f (inject₁ x))

drop : FVSet n → FVSet n
drop {zero} f = f
drop {suc n} f = drop′ f

FVTgt-b : {Γ : Ctx n} → {x : Term n} → {A : Ty n} → PDB Γ x A submax → FVSet n
FVTgt-b (Base _) = empty
FVTgt-b (Extend {submax = zero} pdb) = ewf (ewt (drop full))
FVTgt-b (Extend {submax = suc zero} pdb) = ewf (ewt (drop (FVTgt-b pdb)))
FVTgt-b (Extend {submax = suc (suc s)} pdb) = ewt (ewt (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc (Finish pdb) = FVSrc-b pdb
FVTgt (Finish pdb) = FVTgt-b pdb
