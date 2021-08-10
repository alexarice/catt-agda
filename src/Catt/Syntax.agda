{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin

variable
  n m : ℕ

data Ctx : Set
data Ty : Ctx → ℕ → Set
data Tm : Ctx → ℕ → Set
data Sub : Ctx → Ctx → Set

variable
  Γ Γ′ Δ Υ : Ctx
  A A′ B C : Ty Γ n
  s s′ t t′ u : Tm Γ n
  σ σ′ τ μ : Sub Γ Δ

infixl 25 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ n) → Ctx

ctxLength : Ctx → ℕ
ctxLength ∅ = 0
ctxLength (Γ , A) = suc (ctxLength Γ)

ty-dim : Ty Γ n → ℕ
ty-dim {n = n} A = n

ctx-dim : Ctx → ℕ
ctx-dim ∅ = 0
ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A

tm-dim : Tm Γ n → ℕ
tm-dim {n = n} t = n

sub-dim : Sub Γ Δ → ℕ
sub-dim {Γ} σ = ctx-dim Γ

lookupDim : (Γ : Ctx) → Fin (ctxLength Γ) → ℕ
lookupDim (Γ , A) zero = ty-dim A
lookupDim (Γ , A) (suc i) = lookupDim Γ i

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ 0
  _─⟨_⟩⟶_ : (s : Tm Γ n) → (A : Ty Γ n) → (t : Tm Γ n) → Ty Γ (suc n)

data Sub where
  ⟨⟩ : Sub ∅ Δ
  ⟨_,_⟩ : (σ : Sub Γ Δ) → {A : Ty Γ m} → (t : Tm Δ m) → Sub (Γ , A) Δ

data Tm where
  Var : (i : (Fin (ctxLength Γ))) → Tm Γ (lookupDim Γ i)
  Coh : (Δ : Ctx) → (A : Ty Δ m) → (σ : Sub Δ Γ) → Tm Γ (ctx-dim Δ ⊔ m)

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty Γ n → Sub Γ Δ → Ty Δ n
_[_]tm : Tm Γ n → Sub Γ Δ → Tm Δ n

infixl 31 _∘_
_∘_ : Sub Δ Υ → Sub Γ Δ → Sub Γ Υ

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A τ [ σ ]tm = Coh Δ A (σ ∘ τ)

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

liftTerm : Tm Γ n → Tm (Γ , A) n
liftSub : Sub Δ Γ → Sub Δ (Γ , A)
liftType : Ty Γ n → Ty (Γ , A) n

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

idSub : (Γ : Ctx) → Sub Γ Γ
idSub ∅ = ⟨⟩
idSub (Γ , A) = ⟨ liftSub (idSub Γ) , Var zero ⟩

projection : (Γ : Ctx) → {A : Ty Γ m} → Sub Γ (Γ , A)
projection Γ = liftSub (idSub Γ)

infix 45 _‼_
_‼_ : (Γ : Ctx) → (i : Fin (ctxLength Γ)) → Ty Γ (lookupDim Γ i)
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)
