{-# OPTIONS --without-K --safe #-}

module Catt.Typing where

open import Data.Nat
open import Catt.Fin
open import Data.Bool
open import Catt.Syntax
open import Catt.Pasting
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)

private
  variable
    n m l pdd dim submax : ℕ

data _⊢ : Ctx n → Set
data _⊢_ : Ctx n → Ty n dim → Set
data _⊢_∷_ : Ctx n → Term n → Ty n dim → Set
data _⊢_::_ : Ctx m → Sub m n → Ctx n → Set

data _⊢ where
  TypeCtxBase : ∅ ⊢
  TypeCtxStep : (Γ : Ctx n) → {A : Ty n dim} → Γ ⊢ A → Γ , A ⊢

data _⊢_ where
  TypeTyStar : {Γ : Ctx n} → Γ ⊢ → Γ ⊢ ⋆
  TypeTyArr : {Γ : Ctx n} → {A : Ty n dim} → {t u : Term n} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ (t ─⟨ A ⟩⟶ u)

data _⊢_∷_ where
  TypeTermVar : {Γ : Ctx n} → (x : Fin n) → Γ ⊢ → Γ ⊢ (Var x) ∷ proj₂ (Γ ‼ x)
  TypeTermCoh : {Γ : Ctx (suc n)} →
                (pd : Γ ⊢pd₀ pdd) →
                {A : Ty (suc n) (suc dim)} →
                Γ ⊢ A →
                FVCtx Γ ≡ FVTy A →
                {Δ : Ctx m} →
                {σ : Sub m (suc n)} →
                Δ ⊢ →
                Δ ⊢ σ :: Γ →
                Δ ⊢ (Coh Γ A σ) ∷ A [ σ ]ty
  TypeTermComp : {Γ : Ctx (suc n)} →
                 (pd : Γ ⊢pd₀ pdd) →
                 {A : Ty (suc n) dim} →
                 {t u : Term (suc n)} →
                 Γ ⊢ (t ─⟨ A ⟩⟶ u) →
                 FVSrc pd ≡ FVTerm t →
                 FVTgt pd ≡ FVTerm u →
                 {Δ : Ctx m} →
                 {σ : Sub m (suc n)} →
                 Δ ⊢ →
                 Δ ⊢ σ :: Γ →
                 Δ ⊢ (Coh Γ (t ─⟨ A ⟩⟶ u) σ) ∷ t ─⟨ A ⟩⟶ u [ σ ]ty

data _⊢_::_ where
  TypeSubEmpty : {Δ : Ctx m} → Δ ⊢ ⟨⟩ :: ∅
  TypeSubStep : {Δ : Ctx m} {Γ : Ctx n} {σ : Sub m n} → Δ ⊢ σ :: Γ → {A : Ty n dim} → Γ ⊢ A → {t : Term m} → Δ ⊢ t ∷ (A [ σ ]ty) → Δ ⊢ ⟨ σ , t ⟩ :: Γ , A



FVSrc-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n) dim} → Γ ⊢pd x ∷ A [ submax ][ pdd ] → FVSet (suc n)
FVSrc-b Base = empty
FVSrc-b (ExtendM pdb) = ewf (ewf full)
FVSrc-b (Extend {submax = zero} pdb) = ewf (ewf (FVSrc-b pdb))
FVSrc-b (Extend {submax = (suc _)} pdb) = ewt (ewt (FVSrc-b pdb))
FVSrc-b (Restr pdb) = FVSrc-b pdb

FVTgt-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n) dim} → Γ ⊢pd x ∷ A [ submax ][ pdd ] → FVSet (suc n)
FVTgt-b Base = empty
FVTgt-b (ExtendM pdb) = ewf (ewt (drop full))
FVTgt-b (Extend {submax = zero} pdb) = ewf (ewt (drop (FVTgt-b pdb)))
FVTgt-b (Extend {submax = (suc s)} pdb) = ewt (ewt (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc (Finish pdb) = FVSrc-b pdb
FVTgt (Finish pdb) = FVTgt-b pdb
