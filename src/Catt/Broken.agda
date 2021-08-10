{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Broken where


open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns

variable
  n m d d′ submax : ℕ

data Ctx : ℕ → ℕ → Set
data Ty : Ctx n d → ℕ → Set
data Tm : Ctx n d → ℕ → Set
data Sub : Ctx n d → Ctx m d′ → Set

variable
  Γ Δ : Ctx n d
  A : Ty Γ n
  s t  : Tm Γ n
  σ  : Sub Γ Δ

infixl 25 _,_
data Ctx where
  ∅ : Ctx 0 0
  _,_ : (Γ : Ctx m d) → (A : Ty Γ n) → Ctx (suc m) (d ⊔ n)

ctxLength : (Γ : Ctx n d) → ℕ
ctxLength {n} Γ = n

ty-dim : Ty Γ n → ℕ
ty-dim {n = n} A = n

ctx-dim : Ctx n d → ℕ
ctx-dim {d = d} Γ = d

tm-dim : Tm Γ n → ℕ
tm-dim {n = n} t = n

lookupDim : (Γ : Ctx n d) → Fin n → ℕ
lookupDim (Γ , A) zero = ty-dim A
lookupDim (Γ , A) (suc i) = lookupDim Γ i

infix 30 _─⟨_⟩⟶_
data Ty where
  ⋆ : Ty Γ 1
  _─⟨_⟩⟶_ : (s : Tm Γ (suc n)) → (A : Ty Γ n) → (t : Tm Γ (suc n)) → Ty Γ (suc n)

data Sub where
  ⟨⟩ : Sub ∅ Δ
  ⟨_,_⟩ : (σ : Sub Γ Δ) → {A : Ty Γ m} → (t : Tm Δ (suc m)) → Sub (Γ , A) Δ

data Tm where
  Var : (i : (Fin (ctxLength Γ))) → Tm Γ (suc (lookupDim Γ i))
  Coh : (Δ : Ctx n d) → (A : Ty Δ m) → (σ : Sub Δ Γ) → Tm Γ (suc (ctx-dim Δ) ⊔ suc m)

liftTerm : Tm Γ n → Tm (Γ , A) n
liftSub : Sub Δ Γ → Sub Δ (Γ , A)
liftType : Ty Γ n → Ty (Γ , A) n

liftTerm (Var i) = Var (suc i)
liftTerm (Coh Δ A σ) = Coh Δ A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

data _⊢pd[_][_]_∶_ : (Γ : Ctx n d) → ℕ → (d : ℕ) → Tm Γ (suc (suc d)) → Ty Γ (suc d) → Set


getFocusTerm : Γ ⊢pd[ submax ][ d ] t ∶ A → Tm Γ (suc (suc d))
getFocusTerm {t = t} pdb = t

getFocusType : Γ ⊢pd[ submax ][ d ] t ∶ A → Ty Γ (suc d)
getFocusType {A = A} pdb = A

-- Uniquely extend a pasting context
extend : {Γ : Ctx n m} {t : Tm Γ (suc (suc d))} {A : Ty Γ (suc d)} → Γ ⊢pd[ submax ][ d ] t ∶ A → Ctx (suc (suc n)) (m ⊔ suc d ⊔ suc (suc d))
extend {Γ = Γ} pdb = Γ , getFocusType pdb , liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F

data _⊢pd[_][_]_∶_ where
  ExtendM : {Γ : Ctx n m}
          → {t : Tm Γ (suc (suc d))}
          → {A : Ty Γ (suc d)}
          → (pdb : Γ ⊢pd[ 0 ][ d ] t ∶ A) →
            Γ , A , liftTerm t ─⟨ liftType A ⟩⟶ Var 0F ⊢pd[ 0 ][ suc d ] Var 0F ∶ liftTerm (liftTerm t) ─⟨ liftType (liftType A) ⟩⟶ Var 1F


test : Γ ⊢pd[ submax ][ d ] t ∶ A → Set
test (ExtendM pdb) = ?
