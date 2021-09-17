{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (not) renaming (T to Truth)

record NonZero′ (n : ℕ) : Set where
  field
    nonZero : Truth (not (n ≡ᵇ 0))

-- Instances

instance
  nonZero : ∀ {n} → NonZero′ (suc n)
  nonZero = _

variable
  n n′ m m′ l l′ d d′ d″ : ℕ

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

data Ctx : ℕ → Set
data Ty : ℕ → ℕ → Set
data Tm : ℕ → Set
data Sub : ℕ → ℕ → Set


variable
  S S′ T T′ U U′ : Tree n
  Γ Γ′ Δ Δ′ Υ Θ : Ctx n
  A A′ B C D : Ty n d
  s s′ t t′ u : Tm n
  σ σ′ τ μ : Sub n m

infixl 25 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx n) → (A : Ty n d) → Ctx (suc n)

ctxLength : (Γ : Ctx n) → ℕ
ctxLength {n = n} Γ = n

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty n 0
  _─⟨_⟩⟶_ : (s : Tm n) → (A : Ty n d) → (t : Tm n) → Ty n (suc d)

data Sub where
  ⟨⟩ : Sub 0 n
  ⟨_,_⟩ : (σ : Sub n m) → (t : Tm m) → Sub (suc n) m

data Tm where
  Var : (i : (Fin n)) → Tm n
  Coh : (S : Tree n) → (A : Ty (suc n) d) → (σ : Sub (suc n) m) → Tm m

pattern 0V {n} = Var {n} 0F
pattern 1V {n} = Var {n} 1F
pattern 2V {n} = Var {n} 2F
pattern 3V {n} = Var {n} 3F
pattern 4V {n} = Var {n} 4F
pattern 5V {n} = Var {n} 5F
pattern 6V {n} = Var {n} 6F
pattern 7V {n} = Var {n} 7F
pattern 8V {n} = Var {n} 8F
pattern 9V {n} = Var {n} 9F

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

liftTerm : Tm n → Tm (suc n)
liftType : Ty n d → Ty (suc n) d
liftSub : Sub n m → Sub n (suc m)

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

liftTerm (Var i) = Var (suc i)
liftTerm (Coh S A σ) = Coh S A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

ty-dim : Ty n d → ℕ
ty-dim {d = d} A = d

ty-base : (A : Ty n (suc d)) → Ty n d
ty-base (s ─⟨ A ⟩⟶ t) = A

-- ty-base-dim : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TyDim (ty-base A) (suc d)
-- ty-base-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-src : (A : Ty n (suc d)) → Tm n
ty-src (s ─⟨ A ⟩⟶ t) = s

-- ty-src-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-src A) (suc (suc d))
-- ty-src-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-tgt : (A : Ty n (suc d)) → Tm n
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
_[_]ty : Ty n d → Sub n m → Ty m d
_[_]tm : Tm n → Sub n m → Tm m

infixl 31 _∘_
_∘_ : Sub n l → Sub m n → Sub m l

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A τ [ σ ]tm = Coh Δ A (σ ∘ τ)
-- Coh (susp-ctx-n (sub-level σ) Δ) (susp-ty-n (sub-level σ) A) (susp-adjoint-full (σ ∘ τ))

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

idSub : (n : ℕ) → Sub n n
idSub zero = ⟨⟩
idSub (suc n) = ⟨ liftSub (idSub n) , Var zero ⟩

lookupHeight : (Γ : Ctx n) → (i : Fin n) → ℕ
lookupHeight (Γ , A) zero = ty-dim A
lookupHeight (Γ , A) (suc i) = lookupHeight Γ i

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n (lookupHeight Γ i)
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)

sub-from-function : ((i : Fin n) → Tm m) → Sub n m
sub-from-function {n = zero} f = ⟨⟩
sub-from-function {n = suc n} f = ⟨ (sub-from-function (λ i → f (suc i))) , f zero ⟩
