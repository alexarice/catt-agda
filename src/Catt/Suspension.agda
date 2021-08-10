{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns

suspCtx : Ctx n d → Ctx (suc (suc n)) (suc d)
suspTy : Ty Γ n → Ty (suspCtx Γ) (suc n)
baseTy : Ty (suspCtx Γ) 1
suspTm : Tm Γ n → Tm (suspCtx Γ) (suc n)

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = baseTy
suspTy (s ─⟨ A ⟩⟶ t) = {!!} ─⟨ suspTy A ⟩⟶ {!!}

baseTy {Γ = ∅} = Var 1F ─⟨ ⋆ ⟩⟶ Var 0F
baseTy {Γ = Γ , A} = liftType baseTy

suspTm {Γ = Γ , A} (Var i) = {!!}
suspTm {Γ = ∅} (Coh Δ A σ) = Coh (suspCtx {!Δ!}) {!!} {!!}
suspTm {Γ = Γ , A} (Coh Δ A₁ σ) = Coh {!suspCtx Δ!} {!!} {!!}
