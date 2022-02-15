module Catt.Suspension where

open import Catt.Prelude
open import Catt.Syntax.Base

suspCtx : Ctx n → Ctx (2 + n)
suspTy : Ty n → Ty (2 + n)
getFst : Tm (2 + n)
getSnd : Tm (2 + n)
suspTm : Tm n → Tm (2 + n)
restrict : Sub (2 + n) m A → (s t : Tm m) → Sub n m (s ─⟨ A ⟩⟶ t)
unrestrict : Sub n m (s ─⟨ A ⟩⟶ t) → Sub (2 + n) m A
suspSubRes : (σ : Sub n m A) → Sub n (2 + m) (suspTy A)
suspSub : Sub n m ⋆ → Sub (2 + n) (2 + m) ⋆

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst = Var (fromℕ _)

getSnd = Var (inject₁ (fromℕ _))

suspTm (Var i) = Var (inject₁ (inject₁ i))
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

restrict ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = ⟨⟩
restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = ⟨ restrict σ s t , u ⟩

unrestrict {s = s} {A = A} {t = t} ⟨⟩  = ⟨ ⟨ ⟨⟩ {A = A} , s ⟩ , t ⟩
unrestrict ⟨ σ , u ⟩ = ⟨ unrestrict σ , u ⟩

suspSubRes ⟨⟩ = ⟨⟩
suspSubRes ⟨ σ , t ⟩ = ⟨ suspSubRes σ , suspTm t ⟩

suspSub σ = unrestrict (suspSubRes σ)
