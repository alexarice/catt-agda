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

data _⊢ : Ctx n → Set
data _⊢_ : Ctx n → Ty n → Set
data _⊢_∷_ : Ctx n → Term n → Ty n → Set
data _⊢_::_ : Ctx m → Sub m n → Ctx n → Set
data _⊢pd₀_ : Ctx n → ℕ → Set

FVSrc : {Γ : Ctx n} → Γ ⊢pd₀ dim → FVSet n
FVTgt : {Γ : Ctx n} → Γ ⊢pd₀ dim → FVSet n

infixr 9 _[_]ty _[_]tm
_[_]ty : Ty n → Sub m n → Ty m
_[_]tm : Term n → Sub m n → Term m
infixl 25 _∘_
_∘_ : Sub l m → Sub m n → Sub l n

data _⊢ where
  TypeCtxEmpty : (Γ : Ctx 0) → Γ ⊢
  TypeCtxStep : {Γ : Ctx n} → {A : Ty n} → Γ ⊢ A → Γ , A ⊢

data _⊢_ where
  TypeTyStar : {Γ : Ctx n} → Γ ⊢ → Γ ⊢ ⋆
  TypeTyArr : {Γ : Ctx n} → {A : Ty n} → {t u : Term n} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ (t ─⟨ A ⟩⟶ u)

data _⊢_∷_ where
  TypeTermVar : {Γ : Ctx n} → (x : Fin n) → Γ ⊢ → Γ ⊢ (Var x) ∷ ctx-get Γ x
  TypeTermCoh : {Γ : Ctx n} →
                {pd : Γ ⊢pd₀ dim} →
                {A : Ty n} →
                Γ ⊢ A →
                {Δ : Ctx m} →
                {σ : Sub m n} →
                Δ ⊢ σ :: Γ →
                T (isEqual (FVCtx Γ) (FVTy A)) →
                Δ ⊢ (Coh Γ A σ) ∷ (A [ σ ]ty)
  TypeTermComp : {Γ : Ctx n} →
                 {pd : Γ ⊢pd₀ dim} →
                 {A : Ty n} →
                 {t u : Term n} →
                 Γ ⊢ (t ─⟨ A ⟩⟶ u) →
                 Γ ⊢ t ∷ A →
                 Γ ⊢ u ∷ A →
                 T (isEqual (FVSrc pd) (FVTerm t)) →
                 T (isEqual (FVTgt pd) (FVTerm u)) →
                 {Δ : Ctx m} →
                 {σ : Sub m n} →
                 Δ ⊢ (Comp Γ A t u σ) ∷ ((t ─⟨ A ⟩⟶ u) [ σ ]ty)




data _⊢_::_ where
  TypeSubEmpty : {Δ : Ctx m} {Γ : Ctx 0} (σ : Sub m 0) → Δ ⊢ σ :: Γ
  TypeSubStep : {Δ : Ctx m} {Γ : Ctx n} {σ : Sub m n} → Δ ⊢ σ :: Γ → {A : Ty n} → Γ ⊢ A → {t : Term m} → Δ ⊢ t ∷ (A [ σ ]ty) → Δ ⊢ ⟨ σ , t ⟩ :: Γ , A

⋆ [ σ ]ty = ⋆
(t ─⟨ A ⟩⟶ u) [ σ ]ty = (t [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (u [ σ ]tm)

Var x [ σ ]tm = sub-get σ x
Coh Γ A τ [ σ ]tm = Coh Γ A (σ ∘ τ)
Comp Γ A t u τ [ σ ]tm = Comp Γ A t u (σ ∘ τ)

τ ∘ ⟨⟩ = ⟨⟩
τ ∘ ⟨ σ , x ⟩ = ⟨ τ ∘ σ , x [ τ ]tm ⟩

data _⊢pd_∷_[_] : Ctx n → Term n → Ty n → ℕ → Set where
  Base : (Γ : Ctx 1) → Γ ⊢pd (Var 0F) ∷ ⋆ [ 0 ]
  Extend : {Γ : Ctx n} →
           {A : Ty n} →
           {x : Term n} →
           Γ ⊢pd x ∷ A [ submax ] →
           Γ , A , liftTerm x ─⟨ liftType A ⟩⟶ Var 0F ⊢pd (Var zero) ∷ liftTerm (liftTerm x) ─⟨ liftType (liftType A) ⟩⟶ Var 1F [ pred submax ]
  Restr : {Γ : Ctx n} →
          {f x y : Term n} →
          {A : Ty n} →
          Γ ⊢pd f ∷ (x ─⟨ A ⟩⟶ y) [ submax ] →
          Γ ⊢pd y ∷ A [ suc submax ]

data _⊢pd₀_ where
  Finish : {Γ : Ctx n} → {x : Term n} → {dim : ℕ} → Γ ⊢pd x ∷ ⋆ [ dim ] → Γ ⊢pd₀ dim

FVSrc-b : {Γ : Ctx n} → {x : Term n} → {A : Ty n} → Γ ⊢pd x ∷ A [ submax ] → FVSet n
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

FVTgt-b : {Γ : Ctx n} → {x : Term n} → {A : Ty n} → Γ ⊢pd x ∷ A [ submax ] → FVSet n
FVTgt-b (Base _) = empty
FVTgt-b (Extend {submax = zero} pdb) = ewf (ewt (drop full))
FVTgt-b (Extend {submax = suc zero} pdb) = ewf (ewt (drop (FVTgt-b pdb)))
FVTgt-b (Extend {submax = suc (suc s)} pdb) = ewt (ewt (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc (Finish pdb) = FVSrc-b pdb
FVTgt (Finish pdb) = FVTgt-b pdb
