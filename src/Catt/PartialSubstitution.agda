{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.PartialSubstitution where

open import Catt.Syntax
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Catt.Suspension
open import Data.Empty
open import Catt.Syntax.SyntacticEquality
open import Relation.Nullary

newLength : (d : ℕ) → (n : ℕ) → ℕ
newLength zero n = n
newLength (suc d) n = newLength d (2 + n)

newHeight : (d : ℕ) → (n : ℕ) → ℕ
newHeight zero n = n
newHeight (suc d) n = newHeight d (suc n)

n-fold-suspTree : (d : ℕ) → (T : Tree n) → (Tree (newLength d n))
n-fold-suspTree zero T = T
n-fold-suspTree (suc d) T = n-fold-suspTree d (suspTree T)

n-fold-suspTy : (d : ℕ) → (A : Ty (suc n) d′) → Ty (suc (newLength d n)) (newHeight d d′)
n-fold-suspTy zero A = A
n-fold-suspTy (suc d) A = n-fold-suspTy d (suspTy A)

n-fold-suspSub : (d : ℕ) → (σ : Sub (suc n) (suc m)) → Sub (suc (newLength d n)) (suc (newLength d m))
n-fold-suspSub zero σ = σ
n-fold-suspSub (suc d) σ = n-fold-suspSub d (suspSub σ)

restrict : Sub (2 + n) m → Sub n m
restrict ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = ⟨⟩
restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , t ⟩ = ⟨ restrict σ , t ⟩

unrestrict : Sub n m → Ty m (suc d) → Sub (2 + n) m
unrestrict ⟨⟩ (s ─⟨ A ⟩⟶ t) = ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩
unrestrict ⟨ σ , t ⟩ A = ⟨ unrestrict σ A , t ⟩

full-unrestrict : Sub (suc n) m → Ty m d → Sub (suc (newLength d n)) m
full-unrestrict {d = 0} σ A = σ
full-unrestrict {d = suc d} σ A = full-unrestrict (unrestrict σ A) (ty-base A)

n-to-0-sub-impossible : ¬ (Sub (suc n) 0)
n-to-0-sub-impossible ⟨ μ , t ⟩ = no-term-in-empty-context t

infixr 30 _[_]⟨_⟩ty _[_]⟨_⟩tm
_[_]⟨_⟩ty : Ty n d → Sub n m → Ty m d′ → Ty m (d + d′)
_[_]⟨_⟩tm : Tm n → Sub n m → Ty m d′ → Tm m

⋆ [ σ ]⟨ A ⟩ty = A
(s ─⟨ B ⟩⟶ t) [ σ ]⟨ A ⟩ty = (s [ σ ]⟨ A ⟩tm) ─⟨ (B [ σ ]⟨ A ⟩ty) ⟩⟶ (t [ σ ]⟨ A ⟩tm)

Var zero [ ⟨ σ , t ⟩ ]⟨ A ⟩tm = t
Var (suc i) [ ⟨ σ , t ⟩ ]⟨ A ⟩tm = Var i [ σ ]⟨ A ⟩tm
Coh {m = zero} S B τ [ σ ]⟨ A ⟩tm = ⊥-elim (n-to-0-sub-impossible τ)
Coh {m = suc m} S B τ [ σ ]⟨ A ⟩tm = Coh (n-fold-suspTree (ty-dim A) S) (n-fold-suspTy (ty-dim A) B) (full-unrestrict σ A ∘ n-fold-suspSub (ty-dim A) τ)

infixl 31 _∘⟨_⟩_
_∘⟨_⟩_ : Sub n m → (A : Ty m d) → Sub l n → Sub l m

σ ∘⟨ A ⟩ ⟨⟩ = ⟨⟩
σ ∘⟨ A ⟩ ⟨ τ , t ⟩ = ⟨ (σ ∘⟨ A ⟩ τ) , (t [ σ ]⟨ A ⟩tm) ⟩
