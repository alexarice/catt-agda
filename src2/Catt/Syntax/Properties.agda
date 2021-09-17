{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax.Properties where

open import Catt.Syntax

open import Relation.Binary.PropositionalEquality
-- open import Catt.Dimension
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat

-- lift-dim-ty : .⦃ _ : CtxDim Γ n ⦄ → {A : Ty Γ m} → ⦃ TyDim A d ⦄ → ⦃ _ : TyDim B d′ ⦄ → TyDim (liftType {A = B} A) d
-- lift-dim-tm : .⦃ _ : CtxDim Γ n ⦄ → {t : Tm Γ} → ⦃ TmDim t d ⦄ → ⦃ _ : TyDim A d′ ⦄ → TmDim (liftTerm {A = A} t) d
-- lift-dim-sub : .⦃ _ : CtxDim Γ n ⦄ → .⦃ _ : CtxDim Δ m ⦄ → {σ : Sub Γ Δ} → ⦃ SubDim σ d ⦄ → ⦃ _ : TyDim B d′ ⦄ → SubDim (liftSub {A = B} σ) d

-- lift-dim-ty {A = ⋆} ⦃ TyDimB ⦄ = TyDimB
-- lift-dim-ty {A = s ─⟨ A ⟩⟶ t} ⦃ TyDimS ⦄ = TyDimS ⦃ _ ⦄ ⦃ lift-dim-tm {t = s} ⦄ ⦃ lift-dim-ty ⦄ ⦃ lift-dim-tm  ⦄

-- lift-dim-tm {Γ = Γ} {t = Var i} ⦃ TmDimV ⦄ = TmDimV
-- lift-dim-tm {t = Coh Δ A σ} ⦃ TmDimC ⦄ = TmDimC ⦃ _ ⦄ ⦃ it ⦄ ⦃ it ⦄ ⦃ lift-dim-sub ⦄

-- lift-dim-sub {σ = ⟨⟩} ⦃ SubDimB ⦄ = SubDimB
-- lift-dim-sub {σ = ⟨ σ , t ⟩} ⦃ SubDimS ⦄ = SubDimS ⦃ _ ⦄ ⦃ _ ⦄ ⦃ lift-dim-sub ⦄ ⦃ it ⦄ ⦃ lift-dim-tm ⦄

-- lookupD : (Γ : Ctx n) → ⦃ _ : CtxDim Γ d ⦄ → (i : Fin (ctxLength Γ)) → TyDim (Γ ‼ i) (lookupDim Γ i)
-- lookupD (Γ , A) ⦃ CtxDimS ⦄ zero = lift-dim-ty
-- lookupD (Γ , A) ⦃ CtxDimS ⦄ (suc i) = lift-dim-ty ⦃ it ⦄ ⦃ lookupD Γ i ⦄

-- lift-subbed-ty : {A : Ty Γ} {t : Tm (Δ , C)} → (B : Ty Γ) → (σ : Sub Γ Δ ⋆) → ((liftType {A = A} B) [ ⟨ liftSub σ , t ⟩ ]ty) ⦃ TyDimB ⦄ ≡ liftType (B [ σ ]ty)


-- lift-subbed-tm : {A : Ty Γ} {t : Tm (Δ , C)} (s : Tm Γ) → (σ : Sub Γ Δ ⋆) → ((liftTerm {A = A} s) [ ⟨ liftSub σ , t ⟩ ]tm) ⦃ TyDimB ⦄ ≡ liftTerm (s [ σ ]tm)
-- lift-subbed-sub : (τ : Sub Υ Γ ⋆) → (σ : Sub Γ Δ ⋆) → (⟨_,_⟩ (liftSub σ) {A = A} t ∘ liftSub τ) ⦃ TyDimB ⦄ ≡ liftSub (σ ∘ τ)
-- lift-subbed-var : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ ⋆) → (Var i [ liftSub {A = A} σ ]tm) ⦃ TyDimB ⦄ ≡ liftTerm (Var i [ σ ]tm)

-- lift-subbed-ty ⋆ σ = refl
-- lift-subbed-ty {A = A} {t = t′} (s ─⟨ B ⟩⟶ t) σ
--   rewrite lift-subbed-tm {A = A} {t = t′} s σ
--   rewrite lift-subbed-ty {A = A} {t = t′} B σ
--   rewrite lift-subbed-tm {A = A} {t = t′} t σ
--   = {!!} -- refl

-- lift-subbed-tm (Var i) σ = lift-subbed-var i σ
-- lift-subbed-tm {A = A} {t = t} (Coh Δ B τ) σ
--   rewrite lift-subbed-sub {A = A} {t = t} τ σ
--   = {!!}

-- lift-subbed-var zero ⟨ σ , t ⟩ = refl
-- lift-subbed-var (suc i) ⟨ σ , t ⟩ = lift-subbed-var i σ

-- lift-subbed-sub ⟨⟩ σ = refl
-- lift-subbed-sub {A = A} {t = t′} ⟨ τ , t ⟩ σ
--   rewrite lift-subbed-sub {A = A} {t = t′} τ σ
--   rewrite lift-subbed-tm {A = A} {t = t′} t σ
--   = {!!} -- refl


-- arr-equality : s ≡ s′ → A ≡ A′ → t ≡ t′ → s ─⟨ A ⟩⟶ t ≡ s′ ─⟨ A′ ⟩⟶ t′
-- arr-equality refl refl refl = refl

-- sub-equality : σ ≡ σ′ → t ≡ t′ → ⟨_,_⟩ σ {A} t ≡ ⟨ σ′ , t′ ⟩
-- sub-equality refl refl = refl

-- coh-equality : A ≡ A′ → σ ≡ σ′ → Coh Δ A σ ≡ Coh Δ A′ σ′
-- coh-equality refl refl = refl

-- sub-action-≡-ty : {σ : Sub Γ Δ} → A ≡ B → A [ σ ]ty ≡ B [ σ ]ty
-- sub-action-≡-ty refl = refl

-- sub-action-≡-tm : {σ : Sub Γ Δ} → s ≡ t → s [ σ ]tm ≡ t [ σ ]tm
-- sub-action-≡-tm refl = refl

-- sub-action-≡-sub : {σ : Sub Γ Δ} → τ ≡ μ → σ ∘ τ ≡ σ ∘ μ
-- sub-action-≡-sub refl = refl

sub-from-function : ((i : Fin n) → Tm m) → Sub n m
sub-from-function {n = zero} f = ⟨⟩
sub-from-function {n = suc n} f = ⟨ (sub-from-function (λ i → f (suc i))) , f zero ⟩
