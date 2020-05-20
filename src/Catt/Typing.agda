{-# OPTIONS --without-K --safe #-}

module Catt.Typing where

open import Data.Nat hiding (_+_)
open import Catt.Fin
open import Data.Bool
open import Catt.Syntax
open import Catt.FreeVars
open import Relation.Binary.PropositionalEquality

private
  variable
    n m l dim submax : ℕ

data _⊢ : Ctx n → Set
data _⊢_ : Ctx n → Ty n → Set
data _⊢_∷_ : Ctx n → Term n → Ty n → Set
data _⊢_::_ : Ctx m → Sub m n → Ctx n → Set
data _⊢pd₀_ : Ctx n → ℕ → Set

FVSrc : {Γ : Ctx n} → Γ ⊢pd₀ dim → FVSet n
FVTgt : {Γ : Ctx n} → Γ ⊢pd₀ dim → FVSet n

data _⊢ where
  TypeCtxBase : ∅ ⊢
  TypeCtxStep : (Γ : Ctx n) → {A : Ty n} → Γ ⊢ A → Γ , A ⊢

data _⊢_ where
  TypeTyStar : {Γ : Ctx n} → Γ ⊢ → Γ ⊢ ⋆
  TypeTyArr : {Γ : Ctx n} → {A : Ty n} → {t u : Term n} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ (t ─⟨ A ⟩⟶ u)

data _⊢_∷_ where
  TypeTermVar : {Γ : Ctx n} → (x : Fin n) → Γ ⊢ → Γ ⊢ (Var x) ∷ Γ ‼ x
  TypeTermCoh : {Γ : Ctx (suc n)} →
                (pd : Γ ⊢pd₀ dim) →
                {A : Ty (suc n)} →
                Γ ⊢ A →
                FVCtx Γ ≡ FVTy A →
                {Δ : Ctx m} →
                {σ : Sub m (suc n)} →
                Δ ⊢ →
                Δ ⊢ σ :: Γ →
                Δ ⊢ (Coh Γ A σ) ∷ A [ σ ]ty
  TypeTermComp : {Γ : Ctx (suc n)} →
                 (pd : Γ ⊢pd₀ dim) →
                 {A : Ty (suc n)} →
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
  TypeSubStep : {Δ : Ctx m} {Γ : Ctx n} {σ : Sub m n} → Δ ⊢ σ :: Γ → {A : Ty n} → Γ ⊢ A → {t : Term m} → Δ ⊢ t ∷ (A [ σ ]ty) → Δ ⊢ ⟨ σ , t ⟩ :: Γ , A

data _⊢pd_∷_[_] : Ctx (suc n) → Term (suc n) → Ty (suc n) → ℕ → Set where
  Base : ∅ , ⋆ ⊢pd (Var (fromℕ 0)) ∷ ⋆ [ 0 ]
  Extend : {Γ : Ctx (suc n)} →
           {A : Ty (suc n)} →
           {x : Term (suc n)} →
           Γ ⊢pd x ∷ A [ submax ] →
           Γ , A , liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ _) ⊢pd (Var (fromℕ _)) ∷ liftTerm (liftTerm x) ─⟨ liftType (liftType A) ⟩⟶ Var (inject (fromℕ _)) [ pred submax ]
  Restr : {Γ : Ctx (suc n)} →
          {f x y : Term (suc n)} →
          {A : Ty (suc n)} →
          Γ ⊢pd f ∷ (x ─⟨ A ⟩⟶ y) [ submax ] →
          Γ ⊢pd y ∷ A [ suc submax ]

data _⊢pd₀_ where
  Finish : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {dim : ℕ} → Γ ⊢pd x ∷ ⋆ [ dim ] → Γ ⊢pd₀ dim

FVSrc-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n)} → Γ ⊢pd x ∷ A [ submax ] → FVSet (suc n)
FVSrc-b Base = empty
FVSrc-b (Extend {submax = zero} pdb) = ewf (ewf full)
FVSrc-b (Extend {submax = suc zero} pdb) = ewf (ewf (FVSrc-b pdb))
FVSrc-b (Extend {submax = suc (suc _)} pdb) = ewt (ewt (FVSrc-b pdb))
FVSrc-b (Restr pdb) = FVSrc-b pdb

FVTgt-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n)} → Γ ⊢pd x ∷ A [ submax ] → FVSet (suc n)
FVTgt-b Base = empty
FVTgt-b (Extend {submax = zero} pdb) = ewf (ewt (drop full))
FVTgt-b (Extend {submax = suc zero} pdb) = ewf (ewt (drop (FVTgt-b pdb)))
FVTgt-b (Extend {submax = suc (suc s)} pdb) = ewt (ewt (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc (Finish pdb) = FVSrc-b pdb
FVTgt (Finish pdb) = FVTgt-b pdb
