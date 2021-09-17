{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection where

open import Catt.Syntax
open import Catt.Suspension
open import Catt.Variables
open import Data.Nat
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Sum
open import Data.Bool using (Bool; true; false)

connect : (Γ : Ctx (suc n)) → (x : Tm (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (x : Tm (suc n)) → (m : ℕ) → Sub (suc m) (suc (m + n))

connect Γ x (∅ , A) = Γ
connect Γ x (Δ , A , B) = (connect Γ x (Δ , A)) , B [ connect-inc-right x (ctxLength Δ) ]ty

connect-inc-right x zero = ⟨ ⟨⟩ , x ⟩
connect-inc-right x (suc m) = ⟨ liftSub (connect-inc-right x m) , 0V ⟩

connect-inc-left : (x : Tm (suc n)) → (m : ℕ) → Sub (suc n) (suc (m + n))
connect-inc-left x zero = idSub (suc _)
connect-inc-left x (suc m) = liftSub (connect-inc-left x m)

connect-susp : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + (2 + n)))
connect-susp Γ Δ = connect (suspCtx Γ) getSnd Δ

connect-susp-inc-right : (n m : ℕ) → Sub (suc m) (suc (m + (2 + n)))
connect-susp-inc-right n m = connect-inc-right getSnd m

connect-susp-inc-left : (n m : ℕ) → Sub (3 + n) (suc (m + (2 + n)))
connect-susp-inc-left n m = connect-inc-left getSnd m

sub-from-connect : Sub (suc n) l → (t : Tm (suc n)) → Sub (suc m) l → Sub (suc (m + n)) l
sub-from-connect σ s ⟨ ⟨⟩ , t ⟩ = σ
sub-from-connect σ s ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-connect σ s ⟨ τ , u ⟩ , t ⟩

sub-between-connects : Sub (suc n) (suc l) → (t : Tm (suc n)) → Sub (suc m) (suc l′) → (s : Tm (suc l)) → Sub (suc (m + n)) (suc (l′ + l))
sub-between-connects {l′ = l′} σ t τ s = sub-from-connect (connect-inc-left s l′ ∘ σ) t (connect-inc-right s l′ ∘ τ)

sub-between-connect-susps : Sub (suc n) (suc l) → Sub (suc m) (suc l′) → Sub (suc (m + (2 + n))) (suc (l′ + (2 + l)))
sub-between-connect-susps σ τ = sub-between-connects (suspSub σ) getSnd τ getSnd

connect-var-split : (n m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split n zero i = inj₁ i
connect-var-split n (suc m) zero = inj₂ zero
connect-var-split n (suc m) (suc i) with connect-var-split n m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)

connect-var-split-right : (t : Tm (suc n)) → .⦃ isVar t ⦄ → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split-right t zero i with toℕ (getVarFin t) ≡ᵇ toℕ i
... | true = inj₂ zero
... | false = inj₁ i
connect-var-split-right t (suc m) zero = inj₂ zero
connect-var-split-right t (suc m) (suc i) with connect-var-split-right t m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)
