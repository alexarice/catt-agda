module Catt.Suspension where

open import Catt.Prelude
open import Catt.Syntax.Base

susp-ctx : Ctx n → Ctx (2 + n)
susp-ty : Ty n → Ty (2 + n)
get-fst : Tm (2 + n)
get-snd : Tm (2 + n)
susp-tm : Tm n → Tm (2 + n)
restrict : Sub (2 + n) m A → (s t : Tm m) → Sub n m (s ─⟨ A ⟩⟶ t)
unrestrict : Sub n m (s ─⟨ A ⟩⟶ t) → Sub (2 + n) m A
susp-sub-res : (σ : Sub n m A) → Sub n (2 + m) (susp-ty A)
susp-sub : Sub n m ⋆ → Sub (2 + n) (2 + m) ⋆

susp-ctx ∅ = ∅ , ⋆ , ⋆
susp-ctx (Γ , A) = (susp-ctx Γ) , (susp-ty A)

susp-ty ⋆ = get-fst ─⟨ ⋆ ⟩⟶ get-snd
susp-ty (s ─⟨ A ⟩⟶ t) = susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm t

get-fst = Var (fromℕ _)

get-snd = Var (inject₁ (fromℕ _))

susp-tm (Var i) = Var (inject₁ (inject₁ i))
susp-tm (Coh Δ A σ) = Coh (susp-ctx Δ) (susp-ty A) (susp-sub σ)

restrict ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = ⟨⟩
restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = ⟨ restrict σ s t , u ⟩

unrestrict ⟨ σ , u ⟩ = ⟨ unrestrict σ , u ⟩
unrestrict {s = s} {A = A} {t = t} ⟨⟩  = ⟨ ⟨ ⟨⟩ {A = A} , s ⟩ , t ⟩

susp-sub-res ⟨⟩ = ⟨⟩
susp-sub-res ⟨ σ , t ⟩ = ⟨ susp-sub-res σ , susp-tm t ⟩

susp-sub σ = unrestrict (susp-sub-res σ)
