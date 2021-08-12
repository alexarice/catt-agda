{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Syntax where

open import Data.Nat
open import Data.Fin using (Fin;zero;suc)

variable
  n n′ m m′ d d′ : ℕ

data Ctx : ℕ → Set
data Ty : Ctx n → ℕ → Set
data Tm : Ctx n → ℕ → Set
data Sub : Ctx n → Ctx m → Set

variable
  Γ Γ′ Δ Δ′ Υ : Ctx n
  A A′ B C : Ty Γ n
  s s′ t t′ u : Tm Γ n
  σ σ′ τ μ : Sub Γ Δ

infixl 25 _,_
data Ctx where
  ∅ : Ctx 0
  _,_ : (Γ : Ctx m) → (A : Ty Γ n) → Ctx (suc m)

ctxLength : (Γ : Ctx n) → ℕ
ctxLength {n} Γ = n

ty-dim : Ty Γ n → ℕ
ty-dim {n = n} A = n

ctx-dim : Ctx n → ℕ
ctx-dim ∅ = 0
ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A

tm-dim : Tm Γ n → ℕ
tm-dim {n = n} t = n

sub-dim : Sub Γ Δ → ℕ

lookupDim : (Γ : Ctx n) → Fin n → ℕ
lookupDim (Γ , A) zero = ty-dim A
lookupDim (Γ , A) (suc i) = lookupDim Γ i

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ 1
  _─⟨_⟩⟶_ : (s : Tm Γ (suc n)) → (A : Ty Γ n) → (t : Tm Γ (suc n)) → Ty Γ (suc n)

data Sub where
  ⟨⟩ : Sub ∅ Δ
  ⟨_,_⟩ : (σ : Sub Γ Δ) → {A : Ty Γ m} → (t : Tm Δ (suc m)) → Sub (Γ , A) Δ

sub-dim ⟨⟩ = 0
sub-dim ⟨ σ , t ⟩ = sub-dim σ ⊔ tm-dim t

data Tm where
  Var : (i : (Fin (ctxLength Γ))) → Tm Γ (suc (lookupDim Γ i))
  Coh : (Δ : Ctx (suc n)) → (A : Ty Δ m) → .(ctx-dim Δ ≤ m) → (σ : Sub Δ Γ) → Tm Γ (suc m)

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty Γ n → Sub Γ Δ → Ty Δ n
_[_]tm : Tm Γ n → Sub Γ Δ → Tm Δ n

infixl 31 _∘_
_∘_ : Sub Δ Υ → Sub Γ Δ → Sub Γ Υ

⋆ [ σ ]ty = ⋆
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A p τ [ σ ]tm = Coh Δ A p (σ ∘ τ)

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

liftTerm : Tm Γ n → Tm (Γ , A) n
liftSub : Sub Δ Γ → Sub Δ (Γ , A)
liftType : Ty Γ n → Ty (Γ , A) n

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A p σ) = Coh Δ A p (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

idSub : (Γ : Ctx n) → Sub Γ Γ
idSub ∅ = ⟨⟩
idSub (Γ , A) = ⟨ liftSub (idSub Γ) , Var zero ⟩

projection : (Γ : Ctx n) → {A : Ty Γ m} → Sub Γ (Γ , A)
projection Γ = liftSub (idSub Γ)

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty Γ (lookupDim Γ i)
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)
