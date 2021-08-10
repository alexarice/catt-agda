{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Congruence where

open import Catt.Syntax
open import Data.Nat

record PreCongruence : Set₁ where
  field
    _∼tm_ : Tm → Tm → Set

  data _∼ty_ : Ty → Ty → Set where
    ∼Star : ⋆ ∼ty ⋆
    ∼Arr : s ∼tm s′ → A ∼ty A′ → t ∼tm t′ → s ─⟨ A ⟩⟶ t ∼ty s′ ─⟨ A′ ⟩⟶ t′

  data _∼ctx_ : Ctx → Ctx → Set where
    ∼CEmp : ∅ ∼ctx ∅
    ∼CExt : Γ ∼ctx Γ′ → A ∼ty A′ → Γ , A ∼ctx Γ′ , A′

  data _∼sub_ : Sub → Sub → Set where
    ∼Emp : ⟨⟩ ∼sub ⟨⟩
    ∼Ext : σ ∼sub σ′ → t ∼tm t′ → ⟨ σ , t ⟩ ∼sub ⟨ σ′ , t′ ⟩

record Congruence : Set₁ where
  field
    rel : PreCongruence

  open PreCongruence rel public

  field
    structural-coherence : A ∼ty A′ → σ ∼sub σ′ → Coh Δ A σ ∼tm Coh Δ A′ σ′
    var-refl : (n : ℕ) → Var n ∼tm Var n
    tm-sym : s ∼tm t → t ∼tm s
    tm-trans : s ∼tm t → t ∼tm u → s ∼tm u
    inv-refl : Invalid ∼tm Invalid

  tm-refl : (s : Tm) → s ∼tm s
  ty-refl : (A : Ty) → A ∼ty A
  sub-refl : (σ : Sub) → σ ∼sub σ

  tm-refl Invalid = inv-refl
  tm-refl (Var n) = var-refl n
  tm-refl (Coh Δ A σ) = structural-coherence (ty-refl A) (sub-refl σ)

  ty-refl ⋆ = ∼Star
  ty-refl (s ─⟨ A ⟩⟶ t) = ∼Arr (tm-refl s) (ty-refl A) (tm-refl t)

  sub-refl ⟨⟩ = ∼Emp
  sub-refl ⟨ σ , x ⟩ = ∼Ext (sub-refl σ) (tm-refl x)

  ty-sym : A ∼ty B → B ∼ty A
  sub-sym : σ ∼sub τ → τ ∼sub σ

  ty-sym ∼Star = ∼Star
  ty-sym (∼Arr p q r) = ∼Arr (tm-sym p) (ty-sym q) (tm-sym r)

  sub-sym ∼Emp = ∼Emp
  sub-sym (∼Ext p q) = ∼Ext (sub-sym p) (tm-sym q)

  ty-trans : A ∼ty B → B ∼ty C → A ∼ty C
  sub-trans : σ ∼sub τ → τ ∼sub μ → σ ∼sub μ

  ty-trans ∼Star q = q
  ty-trans (∼Arr p q r) (∼Arr p′ q′ r′) = ∼Arr (tm-trans p p′) (ty-trans q q′) (tm-trans r r′)

  sub-trans ∼Emp q = q
  sub-trans (∼Ext p q) (∼Ext p′ q′) = ∼Ext (sub-trans p p′) (tm-trans q q′)


data syntactic-equality : Tm → Tm → Set where
  InvalidEq : syntactic-equality Invalid Invalid
  VarEq : (n : ℕ) → syntactic-equality (Var n) (Var n)
