{-# OPTIONS --safe --without-K #-}

module Catt.Syntax.Properties where

open import Catt.Syntax
open import Catt.Syntax.Dimension
open import Catt.Fin
open import Catt.Fin.Properties
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Data.Nat.Properties

private
  variable
    n m l o dim : ℕ

lift-sub-ap-ty : (A : Ty n dim) → (σ : Sub m n) → A [ liftSub σ ]ty ≡ liftType (A [ σ ]ty)
lift-sub-ap-tm : (t : Term n) → (σ : Sub m n) → t [ liftSub σ ]tm ≡ liftTerm (t [ σ ]tm)
lift-sub-ap-sub-right : (σ : Sub m n) → (τ : Sub l m) → σ ∘ liftSub τ ≡ liftSub (σ ∘ τ)
sub-extend-ap-ty : (A : Ty n dim) → (σ : Sub m n) → (t : Term m) → liftType A [ ⟨ σ , t ⟩ ]ty ≡ A [ σ ]ty
sub-extend-ap-tm : (u : Term n) → (σ : Sub m n) → (t : Term m) → liftTerm u [ ⟨ σ , t ⟩ ]tm ≡ u [ σ ]tm
sub-extend-sub : (σ : Sub m n) → (τ : Sub l m) → (t : Term l) → liftSub σ ∘ ⟨ τ , t ⟩ ≡ σ ∘ τ
sub-comp-ap-ty : (A : Ty n dim) → (σ : Sub m n) → (τ : Sub l m) → A [ σ ∘ τ ]ty ≡ A [ σ ]ty [ τ ]ty
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

_≡ctx?_ : ∀ {n} → DecidableEquality (Ctx n)
_≡ty?_ : ∀ {n} {dim} → DecidableEquality (Ty n dim)
_≡tm?_ : ∀ {n} → DecidableEquality (Term n)
_≡sub?_ : ∀ {m n} → DecidableEquality (Sub m n)

∅ ≡ctx? ∅ = yes refl
(Γ , A) ≡ctx? (Δ , B) with Γ ≡ctx? Δ | ty-dim A ≟ ty-dim B
... | no p | q = no (λ where refl → p refl)
... | yes p | no q = no (λ where refl → q refl)
... | yes p | yes q with subst (Ty _) q A ≡ty? B
... | yes a rewrite p rewrite q rewrite a = yes refl
... | no a = no (λ where refl → a (cong (λ x → subst (Ty _) x A) (≡-irrelevant q refl)))



⋆ ≡ty? ⋆ = yes refl
(t ─⟨ A ⟩⟶ u) ≡ty? (t′ ─⟨ B ⟩⟶ u′) with t ≡tm? t′ | A ≡ty? B | u ≡tm? u′
... | yes p | yes q | yes refl rewrite p rewrite q = yes refl
... | yes p | yes q | no r = no (λ where refl → r refl)
... | yes p | no q | r = no (λ where refl → q refl)
... | no p | q | r = no (λ where refl → p refl)

Var i ≡tm? Var j = map′ (cong Var) (λ where refl → refl) (i ≡f? j)
Var x ≡tm? Coh Γ A σ = no λ ()
Coh Γ A σ ≡tm? Var x = no λ ()
Coh {n} {dim} Γ A σ ≡tm? Coh {m} {dim′} Γ′ A′ σ′ with n ≟ m | dim ≟ dim′
... | no a | b = no (λ where refl → a refl)
... | yes a | no b = no λ where refl → b refl
... | yes a | yes b with subst Ctx a Γ ≡ctx? Γ′ | subst₂ Ty a (cong suc b) A ≡ty? A′ | subst (Sub _) a σ ≡sub? σ′
... | yes q | yes r | yes s rewrite a rewrite b rewrite q rewrite r rewrite s = yes refl
... | yes q | yes r | no s = no λ where refl → s (cong (λ x → subst (Sub _) x σ) (≡-irrelevant a refl))
... | yes q | no r | s = no λ where refl → r (cong₂ (λ x y → subst₂ Ty x y A) (≡-irrelevant a refl) (≡-irrelevant (cong suc b) refl))
... | no q | r | s = no λ where refl → q (cong (λ x → subst Ctx x Γ) (≡-irrelevant a refl))

⟨⟩ ≡sub? ⟨⟩ = yes refl
⟨ σ , t ⟩ ≡sub? ⟨ τ , u ⟩ with σ ≡sub? τ | t ≡tm? u
... | yes p | yes refl rewrite p = yes refl
... | yes p | no q = no λ where refl → q refl
... | no p | q = no λ where refl → p refl
