{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.PartialSubstitution where

open import Catt.Syntax
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Catt.Suspension
open import Data.Empty
open import Catt.Syntax.SyntacticEquality
open import Relation.Nullary





infixr 30 _[_]⟨_⟩ty _[_]⟨_⟩tm
_[_]⟨_⟩ty : Ty n → Sub n m → Ty m → Ty m
_[_]⟨_⟩tm : Tm n → Sub n m → Ty m → Tm m

⋆ [ σ ]⟨ A ⟩ty = A
(s ─⟨ B ⟩⟶ t) [ σ ]⟨ A ⟩ty = (s [ σ ]⟨ A ⟩tm) ─⟨ (B [ σ ]⟨ A ⟩ty) ⟩⟶ (t [ σ ]⟨ A ⟩tm)

Var zero [ ⟨ σ , t ⟩ ]⟨ A ⟩tm = t
Var (suc i) [ ⟨ σ , t ⟩ ]⟨ A ⟩tm = Var i [ σ ]⟨ A ⟩tm
Coh {m = zero} S B τ [ σ ]⟨ A ⟩tm = ⊥-elim (n-to-0-sub-impossible τ)
Coh {m = suc m} S B τ [ σ ]⟨ A ⟩tm = Coh (n-fold-suspTree (ty-dim A) S) (n-fold-suspTy (ty-dim A) B) (full-unrestrict σ A ∘ n-fold-suspSub (ty-dim A) τ)

infixl 31 _∘⟨_⟩_
_∘⟨_⟩_ : Sub n m → (A : Ty m) → Sub l n → Sub l m

σ ∘⟨ A ⟩ ⟨⟩ = ⟨⟩
σ ∘⟨ A ⟩ ⟨ τ , t ⟩ = ⟨ (σ ∘⟨ A ⟩ τ) , (t [ σ ]⟨ A ⟩tm) ⟩
