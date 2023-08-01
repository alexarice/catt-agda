module Catt.Typing.EndoCoherenceRemoval.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Typing.Rule

open Rule

EndoCoherenceRemoval : (Γ : Ctx m)
                     → (Δ : Ctx (suc n))
                     → (s : Tm (suc n))
                     → (A : Ty (suc n))
                     → (σ : Sub (suc n) m ⋆)
                     → Rule
EndoCoherenceRemoval Γ Δ s A σ .len = _
EndoCoherenceRemoval Γ Δ s A σ .tgtCtx = Γ
EndoCoherenceRemoval Γ Δ s A σ .lhs = Coh Δ (s ─⟨ A ⟩⟶ s) σ
EndoCoherenceRemoval Γ Δ s A σ .rhs = identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))
