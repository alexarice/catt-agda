open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Strict.ECR.Base (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Discs
open import Catt.Typing index rule

HasECR : Set
HasECR = ∀ {m n}
       → {Δ : Ctx m}
       → {Γ : Ctx (suc n)}
       → {A : Ty (suc n)}
       → {s : Tm (suc n)}
       → {σ : Sub (suc n) m ⋆}
       → {B : Ty m}
       → Typing-Tm Δ (Coh Γ (s ─⟨ A ⟩⟶ s) σ) B
       → Coh Γ (s ─⟨ A ⟩⟶ s) σ ≈[ Δ ]tm identity (s [ σ ]tm) (A [ σ ]ty)
