{-# OPTIONS --without-K --safe #-}

module Catt.Typing where

open import Data.Nat hiding (_+_)
open import Catt.Fin
open import Catt.Vec.Functional
open import Data.Bool
open import Catt.Syntax
open import Catt.FreeVars
open import Relation.Binary.PropositionalEquality
open import Catt.Syntax.Equality
open import Data.Unit

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

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub m n → Ty m
_[_]tm : Term n → Sub m n → Term m
infixl 31 _∘_
_∘_ : Sub l m → Sub m n → Sub l n

data _⊢ where
  TypeCtxBase : (Γ : Ctx 0) → Γ ⊢
  TypeCtxStep : (Γ : Ctx (suc n)) → front Γ ⊢ last Γ → Γ ⊢

data _⊢_ where
  TypeTyStar : {Γ : Ctx n} → Γ ⊢ → Γ ⊢ ⋆
  TypeTyArr : {Γ : Ctx n} → {A : Ty n} → {t u : Term n} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ (t ─⟨ A ⟩⟶ u)

data _⊢_∷_ where
  TypeTermVar : {Γ : Ctx n} → {A : Ty n} → (x : Fin n) → Γ ⊢ → Γ ‼ x ≡ty A → Γ ⊢ (Var x) ∷ A
  TypeTermCoh : {Γ : Ctx (suc n)} →
                (pd : Γ ⊢pd₀ dim) →
                {A : Ty (suc n)} →
                Γ ⊢ A →
                FVCtx Γ ≡fv FVTy A →
                {Δ : Ctx m} →
                {σ : Sub m (suc n)} →
                Δ ⊢ →
                Δ ⊢ σ :: Γ →
                {B : Ty m} →
                B ≡ty A [ σ ]ty →
                Δ ⊢ (Coh Γ A σ) ∷ B
  TypeTermComp : {Γ : Ctx (suc n)} →
                 (pd : Γ ⊢pd₀ dim) →
                 {A : Ty (suc n)} →
                 {t u : Term (suc n)} →
                 Γ ⊢ (t ─⟨ A ⟩⟶ u) →
                 FVSrc pd ≡fv FVTerm t →
                 FVTgt pd ≡fv FVTerm u →
                 {Δ : Ctx m} →
                 {σ : Sub m (suc n)} →
                 Δ ⊢ →
                 Δ ⊢ σ :: Γ →
                 {B : Ty m} →
                 B ≡ty t ─⟨ A ⟩⟶ u [ σ ]ty →
                 Δ ⊢ (Coh Γ (t ─⟨ A ⟩⟶ u) σ) ∷ B

data _⊢_::_ where
  TypeSubEmpty : {Δ : Ctx m} {Γ : Ctx 0} (σ : Sub m 0) → Δ ⊢ σ :: Γ
  TypeSubStep : {Δ : Ctx m} {Γ : Ctx (suc n)} {σ : Sub m (suc n)} → Δ ⊢ front σ :: front Γ → front Γ ⊢ last Γ → Δ ⊢ (last σ) ∷ (last Γ [ front σ ]ty) → Δ ⊢ σ :: Γ

⋆ [ σ ]ty = ⋆
(t ─⟨ A ⟩⟶ u) [ σ ]ty = (t [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (u [ σ ]tm)

Var x [ σ ]tm = get σ x
Coh Γ A τ [ σ ]tm = Coh Γ A (σ ∘ τ)

(τ ∘ σ) .get x = get σ x [ τ ]tm

data _⊢pd_∷_[_] : Ctx (suc n) → Term (suc n) → Ty (suc n) → ℕ → Set where
  Base : (Γ : Ctx 1) → Γ ⊢pd (Var (fromℕ 0)) ∷ ⋆ [ 0 ]
  Extend : {Γ : Ctx (suc (suc (suc n)))} →
           {A : Ty (suc n)} →
           {x : Term (suc n)} →
           front (front Γ) ⊢pd x ∷ A [ submax ] →
           last {A = Ty} (front Γ) ≡ty A →
           last {A = Ty} Γ ≡ty liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ _) →
           Γ ⊢pd (Var (fromℕ _)) ∷ liftTerm (liftTerm x) ─⟨ liftType (liftType A) ⟩⟶ Var (inject (fromℕ _)) [ pred submax ]
  Restr : {Γ : Ctx (suc n)} →
          {f x y : Term (suc n)} →
          {A : Ty (suc n)} →
          Γ ⊢pd f ∷ (x ─⟨ A ⟩⟶ y) [ submax ] →
          Γ ⊢pd y ∷ A [ suc submax ]

data _⊢pd₀_ where
  Finish : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {dim : ℕ} → Γ ⊢pd x ∷ ⋆ [ dim ] → Γ ⊢pd₀ dim

FVSrc-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n)} → Γ ⊢pd x ∷ A [ submax ] → FVSet (suc n)
FVSrc-b (Base _) = empty
FVSrc-b (Extend {submax = zero} pdb p q) = ewf (ewf full)
FVSrc-b (Extend {submax = suc zero} pdb p q) = ewf (ewf (FVSrc-b pdb))
FVSrc-b (Extend {submax = suc (suc _)} pdb p q) = ewt (ewt (FVSrc-b pdb))
FVSrc-b (Restr pdb) = FVSrc-b pdb

FVTgt-b : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n)} → Γ ⊢pd x ∷ A [ submax ] → FVSet (suc n)
FVTgt-b (Base _) = empty
FVTgt-b (Extend {submax = zero} pdb p q) = ewf (ewt (drop full))
FVTgt-b (Extend {submax = suc zero} pdb p q) = ewf (ewt (drop (FVTgt-b pdb)))
FVTgt-b (Extend {submax = suc (suc s)} pdb p q) = ewt (ewt (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc (Finish pdb) = FVSrc-b pdb
FVTgt (Finish pdb) = FVTgt-b pdb
