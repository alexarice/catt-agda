{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax.Base where

open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Fin.Patterns
open import Data.Bool.Base using (T ; not)
open import Relation.Nullary

variable
  n n′ m m′ l l′ d d′ : ℕ

-- record NonZero′ (n : ℕ) : Set where
--   field
--     nonZero : T (not (n ≡ᵇ 0))

-- -- Instances

-- instance
--   nonZero : ∀ {n} → NonZero′ (suc n)
--   nonZero = _

data Ctx : Set
data Ty : Ctx → Set
data TyHeight : {Γ : Ctx} → Ty Γ → ℕ → Set
data Tm : Ctx → Set
data Sub : Ctx → (Δ : Ctx) → (A : Ty Δ) → Set


variable
  Γ Γ′ Δ Δ′ Υ : Ctx
  A A′ B C : Ty Γ
  s s′ t t′ u : Tm Γ
  σ σ′ τ μ : Sub Γ Δ A

infixl 25 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ) → Ctx

ctxLength : (Γ : Ctx) → ℕ
ctxLength ∅ = 0
ctxLength (Γ , A) = suc (ctxLength Γ)

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ
  _─⟨_⟩⟶_ : (s : Tm Γ) → (A : Ty Γ) → (t : Tm Γ) → Ty Γ

-- Weaker version of being well dimensioned
data TyHeight where
  instance TyHeightB : TyHeight {Γ = Γ} ⋆ 0
  instance TyHeightS : ⦃ TyHeight A n ⦄ → TyHeight (s ─⟨ A ⟩⟶ t) (suc n)

data Sub where
  ⟨⟩ : Sub ∅ Δ A
  ⟨_,_⟩ : (σ : Sub Γ Δ B) → {A : Ty Γ} → (t : Tm Δ) → Sub (Γ , A) Δ B

data Tm where
  Var : (i : (Fin (ctxLength Γ))) → Tm Γ
  Coh : (Δ : Ctx) → (A : Ty Δ) → (σ : Sub Δ Γ ⋆) → Tm Γ

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
liftType : Ty Γ → Ty (Γ , A)
liftSub : Sub Δ Γ B → Sub Δ (Γ , A) (liftType B)

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

ty-dim : Ty Γ → ℕ
ty-dim ⋆ = 0
ty-dim (s ─⟨ A ⟩⟶ t) = suc (ty-dim A)

ty-base : (A : Ty Γ) → .⦃ TyHeight A (suc d) ⦄ → Ty Γ
ty-base (s ─⟨ A ⟩⟶ t) = A

ty-base-height : (A : Ty Γ) → ⦃ _ : TyHeight A (suc d) ⦄ → TyHeight (ty-base A) d
ty-base-height (s ─⟨ A ⟩⟶ t) ⦃ TyHeightS ⦄ = it

-- ty-base-dim : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TyDim (ty-base A) (suc d)
-- ty-base-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-src : (A : Ty Γ) → .⦃ TyHeight A (suc d) ⦄ → Tm Γ
ty-src (s ─⟨ A ⟩⟶ t) = s

-- ty-src-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-src A) (suc (suc d))
-- ty-src-dim {d = _} ⦃ x = TyDimS ⦄ = it

ty-tgt : (A : Ty Γ) → .⦃ TyHeight A (suc d) ⦄ → Tm Γ
ty-tgt (s ─⟨ A ⟩⟶ t) = t

-- ty-tgt-dim  : .⦃ _ : CtxDim Γ d′ ⦄ → ⦃ x : TyDim {Γ = Γ} A (suc (suc d)) ⦄ → TmDim (ty-tgt A) (suc (suc d))
-- ty-tgt-dim ⦃ x = TyDimS ⦄ = it

ty-height-dec : (A : Ty Γ) → (d : ℕ) → Dec (TyHeight A d)
ty-height-dec ⋆ zero = yes TyHeightB
ty-height-dec ⋆ (suc d) = no (λ ())
ty-height-dec (s ─⟨ A ⟩⟶ t) zero = no (λ ())
ty-height-dec (s ─⟨ A ⟩⟶ t) (suc d) with ty-height-dec A d
... | yes p = yes (TyHeightS ⦃ p ⦄)
... | no p = no (λ where TyHeightS → p it)

get-ty-height : (A : Ty Γ) → TyHeight A (ty-dim A)
get-ty-height ⋆ = TyHeightB
get-ty-height (s ─⟨ A ⟩⟶ t) = TyHeightS ⦃ get-ty-height A ⦄

lift-ty-height : ⦃ TyHeight C d ⦄ → TyHeight (liftType {A = A} C) d
lift-ty-height {C = ⋆} {A = _} ⦃ TyHeightB ⦄ = TyHeightB
lift-ty-height {C = s ─⟨ C ⟩⟶ t} {A = _} ⦃ TyHeightS ⦄ = TyHeightS ⦃ lift-ty-height ⦄
