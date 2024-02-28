module Catt.Suspension where

open import Catt.Prelude
open import Catt.Syntax.Base

susp-ctx : Ctx n → Ctx (2 + n)
susp-ty : Ty n → Ty (2 + n)
get-fst : Tm (2 + n)
get-snd : Tm (2 + n)
susp-tm : Tm n → Tm (2 + n)

↓ : Sub n m (s ─⟨ A ⟩⟶ t) → Sub (2 + n) m A
susp-sub-↑ : (σ : Sub n m A) → Sub n (2 + m) (susp-ty A)
susp-sub : Sub n m ⋆ → Sub (2 + n) (2 + m) ⋆

susp-ctx ∅ = ∅ , ⋆ , ⋆
susp-ctx (Γ , A) = (susp-ctx Γ) , (susp-ty A)

susp-ty ⋆ = get-fst ─⟨ ⋆ ⟩⟶ get-snd
susp-ty (s ─⟨ A ⟩⟶ t) = susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm t

get-fst = Var (fromℕ _)

get-snd = Var (inject₁ (fromℕ _))

susp-tm (Var i) = Var (inject₁ (inject₁ i))
susp-tm (Coh Δ A σ) = Coh (susp-ctx Δ) (susp-ty A) (susp-sub σ)

↓ ⟨ σ , u ⟩ = ⟨ ↓ σ , u ⟩
↓ ⟨ s ─⟨ A ⟩⟶ t ⟩′  = ⟨ ⟨ ⟨ A ⟩′ , s ⟩ , t ⟩

susp-sub-↑ ⟨ A ⟩′ = ⟨ susp-ty A ⟩′
susp-sub-↑ ⟨ σ , t ⟩ = ⟨ susp-sub-↑ σ , susp-tm t ⟩

susp-sub σ = ↓ (susp-sub-↑ σ)

↑ : (σ : Sub (2 + n) m A) → Sub n m ((fromℕ _ [ σ ]v) ─⟨ A ⟩⟶ (inject₁ (fromℕ _) [ σ ]v))
↑ ⟨ ⟨ ⟨ A ⟩′ , s ⟩ , t ⟩ = ⟨ s ─⟨ A ⟩⟶ t ⟩′
↑ ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ = ⟨ ↑ σ , u ⟩
