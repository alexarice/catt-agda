{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

variable
  n n′ m m′ l l′ d d′ : ℕ

data Ctx : Set
data Ty : Ctx → ℕ → Set
data Tm : Ctx → Set
data Sub : Ctx → (Δ : Ctx) → Set


variable
  Γ Γ′ Δ Δ′ Υ : Ctx
  A A′ B C : Ty Γ d
  s s′ t t′ u : Tm Γ
  σ σ′ τ μ : Sub Γ Δ

infixl 25 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ d) → Ctx

ctxLength : (Γ : Ctx) → ℕ
ctxLength ∅ = 0
ctxLength (Γ , A) = suc (ctxLength Γ)

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ 0
  _─⟨_⟩⟶_ : (s : Tm Γ) → (A : Ty Γ n) → (t : Tm Γ) → Ty Γ (suc n)

data Sub where
  ⟨⟩ : Sub ∅ Δ
  ⟨_,_⟩ : (σ : Sub Γ Δ) → {A : Ty Γ n} → (t : Tm Δ) → Sub (Γ , A) Δ

data Tm where
  Var : (i : (Fin (ctxLength Γ))) → Tm Γ
  Coh : (Δ : Ctx) → (A : Ty Δ d) → (σ : Sub Δ Γ) → Tm Γ

pattern 0V {Γ} = Var {Γ = Γ} 0F
pattern 1V {Γ} = Var {Γ = Γ} 1F
pattern 2V {Γ} = Var {Γ = Γ} 2F
pattern 3V {Γ} = Var {Γ = Γ} 3F
pattern 4V {Γ} = Var {Γ = Γ} 4F
pattern 5V {Γ} = Var {Γ = Γ} 5F
pattern 6V {Γ} = Var {Γ = Γ} 6F
pattern 7V {Γ} = Var {Γ = Γ} 7F
pattern 8V {Γ} = Var {Γ = Γ} 8F
pattern 9V {Γ} = Var {Γ = Γ} 9F

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

liftTerm : Tm Γ → Tm (Γ , A)
liftType : Ty Γ d → Ty (Γ , A) d
liftSub : Sub Δ Γ → Sub Δ (Γ , A)

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

ty-dim : Ty Γ d → ℕ
ty-dim {d = d} A = d

ty-base : (A : Ty Γ (suc d)) → Ty Γ d
ty-base (s ─⟨ A ⟩⟶ t) = A

-- ty-base-dim : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TyDim (ty-base A) (suc d)
-- ty-base-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-src : (A : Ty Γ (suc d)) → Tm Γ
ty-src (s ─⟨ A ⟩⟶ t) = s

-- ty-src-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-src A) (suc (suc d))
-- ty-src-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-tgt : (A : Ty Γ (suc d)) → Tm Γ
ty-tgt (s ─⟨ A ⟩⟶ t) = t

-- ty-tgt-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-tgt A) (suc (suc d))
-- ty-tgt-dim ⦃ x = TyDimS ⦄ = it

-- ty-height-dec : (A : Ty Γ) → (d : ℕ) → Dec (TyHeight A d)
-- ty-height-dec ⋆ zero = yes TyHeightB
-- ty-height-dec ⋆ (suc d) = no (λ ())
-- ty-height-dec (s ─⟨ A ⟩⟶ t) zero = no (λ ())
-- ty-height-dec (s ─⟨ A ⟩⟶ t) (suc d) with ty-height-dec A d
-- ... | yes p = yes (TyHeightS ⦃ p ⦄)
-- ... | no p = no (λ where TyHeightS → p it)

-- get-ty-height : (A : Ty Γ) → TyHeight A (ty-dim A)
-- get-ty-height ⋆ = TyHeightB
-- get-ty-height (s ─⟨ A ⟩⟶ t) = TyHeightS ⦃ get-ty-height A ⦄

-- lift-ty-height : ⦃ TyHeight C d ⦄ → TyHeight (liftType {A = A} C) d
-- lift-ty-height {C = ⋆} {A = _} ⦃ TyHeightB ⦄ = TyHeightB
-- lift-ty-height {C = s ─⟨ C ⟩⟶ t} {A = _} ⦃ TyHeightS ⦄ = TyHeightS ⦃ lift-ty-height ⦄


infixr 30 _[_]ty _[_]tm
_[_]ty : Ty Γ d → Sub Γ Δ → Ty Δ d
_[_]tm : Tm Γ → Sub Γ Δ → Tm Δ

infixl 31 _∘_
_∘_ : Sub Δ Υ → Sub Γ Δ → Sub Γ Υ

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A τ [ σ ]tm = Coh Δ A (σ ∘ τ)
-- Coh (susp-ctx-n (sub-level σ) Δ) (susp-ty-n (sub-level σ) A) (susp-adjoint-full (σ ∘ τ))

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

idSub : (Γ : Ctx) → Sub Γ Γ
idSub ∅ = ⟨⟩
idSub (Γ , A) = ⟨ liftSub (idSub Γ) , Var zero ⟩

lookupHeight : (Γ : Ctx) → (i : Fin (ctxLength Γ)) → ℕ
lookupHeight (Γ , A) zero = ty-dim A
lookupHeight (Γ , A) (suc i) = lookupHeight Γ i

infix 45 _‼_
_‼_ : (Γ : Ctx) → (i : Fin (ctxLength Γ)) → Ty Γ (lookupHeight Γ i)
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)
