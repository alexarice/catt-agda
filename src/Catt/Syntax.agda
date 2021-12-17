{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax where

open import Catt.Syntax.Base public
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (not) renaming (T to Truth)
open import Catt.Suspension
open import Relation.Nullary
open import Data.Empty

record NonZero′ (n : ℕ) : Set where
  field
    nonZero : Truth (not (n ≡ᵇ 0))

-- Instances

instance
  nonZero : ∀ {n} → NonZero′ (suc n)
  nonZero = _

NonZero′-subst : n ≡ m → NonZero′ n → NonZero′ m
NonZero′-subst refl x = x

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

liftTerm : Tm n → Tm (suc n)
liftType : Ty n → Ty (suc n)
liftSub : Sub n m A → Sub n (suc m) (liftType A)

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

liftTerm (Var i) = Var (suc i)
liftTerm (Coh S A σ) = Coh S A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

-- ty-base : (A : Ty n (suc d)) → Ty n d
-- ty-base (s ─⟨ A ⟩⟶ t) = A

-- ty-base-dim : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TyDim (ty-base A) (suc d)
-- ty-base-dim {d = _} ⦃ x = TyDimS ⦄ = it

-- ty-src : (A : Ty n (suc d)) → Tm n
-- ty-src (s ─⟨ A ⟩⟶ t) = s

-- ty-src-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-src A) (suc (suc d))
-- ty-src-dim {d = _} ⦃ x = TyDimS ⦄ = it

-- ty-tgt : (A : Ty n (suc d)) → Tm n
-- ty-tgt (s ─⟨ A ⟩⟶ t) = t

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

sub-type : Sub n m A → Ty m
sub-type {A = A} σ = A

sl : Sub n m A → ℕ
sl σ = ty-dim (sub-type σ)

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub n m A → Ty m
_[_]tm : Tm n → Sub n m A → Tm m

infixl 31 _∘_
_∘_ : (σ : Sub n l A) → Sub m n B → Sub m l (B [ σ ]ty)

⋆ [ σ ]ty = sub-type σ
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
_[_]tm {A = ⋆} (Coh T B τ) σ = Coh T B (σ ∘ τ)
_[_]tm {A = s ─⟨ A ⟩⟶ t} (Coh T B τ) σ = _[_]tm {A = A} (Coh (suspTree T) (suspTy B) (suspSub τ)) (unrestrict σ)
-- Coh (n-fold-suspTree (sl σ) T) (n-fold-suspTy (sl σ) A) ((full-unrestrict σ) ∘ (n-fold-suspSub (sl σ) τ))

-- Coh Δ A (σ ∘ τ)
-- Coh (susp-ctx-n (sub-level σ) Δ) (susp-ty-n (sub-level σ) A) (susp-adjoint-full (σ ∘ τ))

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

idSub : {n : ℕ} → Sub n n ⋆
idSub {zero} = ⟨⟩
idSub {suc n} = ⟨ liftSub idSub , Var zero ⟩

lookupHeight : (Γ : Ctx n) → (i : Fin n) → ℕ
lookupHeight (Γ , A) zero = ty-dim A
lookupHeight (Γ , A) (suc i) = lookupHeight Γ i

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)

ctx-proj₁ : Ctx (suc n) → Ctx n
ctx-proj₁ (Γ , A) = Γ

ctx-proj₂ : Ctx (suc n) → Ty n
ctx-proj₂ (Γ , A) = A

replaceSub : Sub (1 + n) m A → Tm m → Sub (1 + n) m A
replaceSub ⟨ σ , _ ⟩ t = ⟨ σ , t ⟩

-- sub-from-function : ((i : Fin n) → Tm m) → Sub n m
-- sub-from-function {n = zero} f = ⟨⟩
-- sub-from-function {n = suc n} f = ⟨ (sub-from-function (λ i → f (suc i))) , f zero ⟩
