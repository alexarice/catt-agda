{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax.Properties where

open import Catt.Syntax
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat

lift-subbed-ty : {A : Ty Γ d′} {t : Tm (Δ , C) (suc d′)} (B : Ty Γ d) → (σ : Sub Γ Δ) → (liftType {A = A} B) [ ⟨ liftSub σ , t ⟩ ]ty ≡ liftType (B [ σ ]ty)
lift-subbed-tm : {A : Ty Γ d′} {t : Tm (Δ , C) (suc d′)} (s : Tm Γ d) → (σ : Sub Γ Δ) → (liftTerm {A = A} s) [ ⟨ liftSub σ , t ⟩ ]tm ≡ liftTerm (s [ σ ]tm)
lift-subbed-sub : (τ : Sub Υ Γ) → (σ : Sub Γ Δ) → ⟨_,_⟩ (liftSub σ) {A = A} t ∘ liftSub τ ≡ liftSub (σ ∘ τ)
lift-subbed-var : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → Var i [ liftSub {A = A} σ ]tm ≡ liftTerm (Var i [ σ ]tm)

lift-subbed-ty ⋆ σ = refl
lift-subbed-ty {A = A} {t = t′} (s ─⟨ B ⟩⟶ t) σ
  rewrite lift-subbed-tm {A = A} {t = t′} s σ
  rewrite lift-subbed-ty {A = A} {t = t′} B σ
  rewrite lift-subbed-tm {A = A} {t = t′} t σ
  = refl

lift-subbed-tm (Var i) σ = lift-subbed-var i σ
lift-subbed-tm {A = A} {t = t} (Coh Δ B q τ) σ
  rewrite lift-subbed-sub {A = A} {t = t} τ σ
  = refl

lift-subbed-var zero ⟨ σ , t ⟩ = refl
lift-subbed-var (suc i) ⟨ σ , t ⟩ = lift-subbed-var i σ

lift-subbed-sub ⟨⟩ σ = refl
lift-subbed-sub {A = A} {t = t′} ⟨ τ , t ⟩ σ
  rewrite lift-subbed-sub {A = A} {t = t′} τ σ
  rewrite lift-subbed-tm {A = A} {t = t′} t σ
  = refl

arr-equality : s ≡ s′ → A ≡ A′ → t ≡ t′ → s ─⟨ A ⟩⟶ t ≡ s′ ─⟨ A′ ⟩⟶ t′
arr-equality refl refl refl = refl

sub-equality : σ ≡ σ′ → t ≡ t′ → ⟨_,_⟩ σ {A} t ≡ ⟨ σ′ , t′ ⟩
sub-equality refl refl = refl

coh-equality : .{p : ctx-dim Δ ≤ ty-dim A} → .{q : ctx-dim Δ ≤ ty-dim A′} → A ≡ A′ → σ ≡ σ′ → Coh Δ A p σ ≡ Coh Δ A′ q σ′
coh-equality refl refl = refl
