{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax where

open import Catt.Syntax.Base public
open import Catt.Suspension.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty Γ → Sub Γ Δ A → Ty Δ
_[_]tm : Tm Γ → Sub Γ Δ A → Tm Δ

sub-ty : Sub Γ Δ B → Ty Δ
sub-ty {B = B} σ = B

infixl 31 _∘_
_∘_ : Sub Δ Υ B → Sub Γ Δ ⋆ → Sub Γ Υ B

⋆ [ σ ]ty = sub-ty σ
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
Coh Δ A τ [ σ ]tm = Coh (susp-ctx-n (sub-level σ) Δ) (susp-ty-n (sub-level σ) A) (susp-adjoint-full (σ ∘ τ))

σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

idSub : (Γ : Ctx) → Sub Γ Γ ⋆
idSub ∅ = ⟨⟩
idSub (Γ , A) = ⟨ liftSub (idSub Γ) , Var zero ⟩

infix 45 _‼_
_‼_ : (Γ : Ctx) → (i : Fin (ctxLength Γ)) → Ty Γ
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)
