{-# OPTIONS --safe --without-K #-}

module Catt.Syntax.Properties where

open import Catt.Syntax
open import Catt.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality

private
  variable
    n m l o : ℕ

lift-sub-ap-ty : (A : Ty n) → (σ : Sub m n) → A [ liftSub σ ]ty ≡ liftType (A [ σ ]ty)
lift-sub-ap-tm : (t : Term n) → (σ : Sub m n) → t [ liftSub σ ]tm ≡ liftTerm (t [ σ ]tm)
lift-sub-ap-sub-right : (σ : Sub m n) → (τ : Sub l m) → σ ∘ liftSub τ ≡ liftSub (σ ∘ τ)
sub-extend-ap-ty : (A : Ty n) → (σ : Sub m n) → (t : Term m) → liftType A [ ⟨ σ , t ⟩ ]ty ≡ A [ σ ]ty
sub-extend-ap-tm : (u : Term n) → (σ : Sub m n) → (t : Term m) → liftTerm u [ ⟨ σ , t ⟩ ]tm ≡ u [ σ ]tm
sub-extend-sub : (σ : Sub m n) → (τ : Sub l m) → (t : Term l) → liftSub σ ∘ ⟨ τ , t ⟩ ≡ σ ∘ τ
sub-comp-ap-ty : (A : Ty n) → (σ : Sub m n) → (τ : Sub l m) → A [ σ ∘ τ ]ty ≡ A [ σ ]ty [ τ ]ty
sub-comp-ap-tm : (t : Term n) → (σ : Sub m n) → (τ : Sub l m) → t [ σ ∘ τ ]tm ≡ t [ σ ]tm [ τ ]tm
sub-comp-transitive : (σ : Sub m n) → (τ : Sub l m) → (θ : Sub o l) → (σ ∘ τ) ∘ θ ≡ σ ∘ (τ ∘ θ)

lift-sub-ap-ty ⋆ σ = refl
lift-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ
  rewrite lift-sub-ap-tm t σ
  rewrite lift-sub-ap-ty A σ
  rewrite lift-sub-ap-tm u σ = refl

lift-sub-ap-tm (Var (fromℕ n)) ⟨ σ , t ⟩ = refl
lift-sub-ap-tm (Var (inject i)) ⟨ σ , t ⟩ = lift-sub-ap-tm (Var i) σ
lift-sub-ap-tm (Coh Γ A τ) σ rewrite lift-sub-ap-sub-right τ σ = refl

lift-sub-ap-sub-right ⟨⟩ τ = refl
lift-sub-ap-sub-right ⟨ σ , t ⟩ τ
  rewrite lift-sub-ap-sub-right σ τ
  rewrite lift-sub-ap-tm t τ = refl

sub-extend-ap-ty ⋆ σ t = refl
sub-extend-ap-ty (t ─⟨ A ⟩⟶ u) σ x
  rewrite sub-extend-ap-tm t σ x
  rewrite sub-extend-ap-ty A σ x
  rewrite sub-extend-ap-tm u σ x = refl

sub-extend-ap-tm (Var x) σ t = refl
sub-extend-ap-tm (Coh Γ A τ) σ t
  rewrite sub-extend-sub τ σ t = refl

sub-extend-sub ⟨⟩ τ x = refl
sub-extend-sub ⟨ σ , t ⟩ τ x
  rewrite sub-extend-sub σ τ x
  rewrite sub-extend-ap-tm t τ x = refl

sub-comp-ap-ty ⋆ σ τ = refl
sub-comp-ap-ty (t ─⟨ A ⟩⟶ u) σ τ
  rewrite sub-comp-ap-tm t σ τ
  rewrite sub-comp-ap-ty A σ τ
  rewrite sub-comp-ap-tm u σ τ = refl

sub-comp-ap-tm (Var (fromℕ n)) ⟨ σ , t ⟩ τ = refl
sub-comp-ap-tm (Var (inject i)) ⟨ σ , t ⟩ τ = sub-comp-ap-tm (Var i) σ τ
sub-comp-ap-tm (Coh Γ A θ) σ τ
  rewrite sub-comp-transitive θ σ τ = refl

sub-comp-transitive ⟨⟩ τ θ = refl
sub-comp-transitive ⟨ σ , t ⟩ τ θ
  rewrite sub-comp-transitive σ τ θ
  rewrite sub-comp-ap-tm t τ θ = refl
