module Catt.Suspension.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension

get-fst-Lem : susp-ctx Γ ≃c susp-ctx Δ → get-fst {n = ctxLength Γ} ≃tm get-fst {n = ctxLength Δ}
get-fst-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → suc (toℕ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

get-snd-Lem : susp-ctx Γ ≃c susp-ctx Δ → get-snd {n = ctxLength Γ} ≃tm get-snd {n = ctxLength Δ}
get-snd-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → toℕ (inject₁ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

susp-‼ : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → susp-ctx Γ ‼ inject₁ (inject₁ i) ≃ty susp-ty (Γ ‼ i)
susp-‼ (Γ , A) zero = sym≃ty (susp-ty-lift A)
susp-‼ (Γ , A) (suc i) = trans≃ty (lift-ty-≃ (susp-‼ Γ i)) (sym≃ty (susp-ty-lift (Γ ‼ i)))

susp-functorial-id : {n : ℕ} → susp-sub (idSub {n}) ≃s idSub {2 + n}
susp-functorial-id {zero} = refl≃s
susp-functorial-id {suc n} = Ext≃ (trans≃s (susp-sub-lift idSub) (lift-sub-≃ (susp-functorial-id))) refl≃tm

susp-sub-preserve-star : (σ : Sub n m ⋆) → susp-ty ⋆ [ susp-sub σ ]ty ≃ty susp-ty (⋆ {n = m})
susp-sub-preserve-star ⟨ _ ⟩′ = refl≃ty
susp-sub-preserve-star ⟨ σ , t ⟩ = trans≃ty (apply-sub-lifted-ty-≃ (get-fst ─⟨ ⋆ ⟩⟶ get-snd) (susp-sub ⟨ σ , t ⟩)) (susp-sub-preserve-star σ)

inject-susp-sub : (σ : Sub n m ⋆) → (i : Fin n) → Var (inject₁ (inject₁ i)) [ susp-sub σ ]tm ≃tm susp-tm (Var i [ σ ]tm)
inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

susp-↑-↓-comm : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → susp-sub-↑ (↓ σ) ≃s ↓ (susp-sub-↑ σ)
susp-↑-↓-comm ⟨ _ ⟩′ = refl≃s
susp-↑-↓-comm ⟨ σ , t ⟩ = Ext≃ (susp-↑-↓-comm σ) refl≃tm

susp-↑-comp-ty : (B : Ty n) → (σ : Sub n m A) → susp-ty (B [ σ ]ty) ≃ty B [ susp-sub-↑ σ ]ty
susp-↑-comp-tm : (t : Tm n) → (σ : Sub n m A) → susp-tm (t [ σ ]tm) ≃tm t [ susp-sub-↑ σ ]tm
susp-↑-comp-sub : (τ : Sub l n B) → (σ : Sub n m A) → susp-sub-↑ (τ ● σ) ≃s τ ● susp-sub-↑ σ

susp-↑-comp-ty ⋆ σ = refl≃ty
susp-↑-comp-ty (s ─⟨ B ⟩⟶ t) σ = Arr≃ (susp-↑-comp-tm s σ) (susp-↑-comp-ty B σ) (susp-↑-comp-tm t σ)

susp-↑-comp-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
susp-↑-comp-tm (Var (suc i)) ⟨ σ , t ⟩ = susp-↑-comp-tm (Var i) σ
susp-↑-comp-tm {A = ⋆} (Coh Δ B τ) σ = Coh≃ refl≃c refl≃ty (susp-functorial τ σ)
susp-↑-comp-tm {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = begin
  < susp-tm (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ σ ]tm) >tm
    ≈⟨ susp-↑-comp-tm {A = A} (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ)) (↓ σ) ⟩
  < Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ susp-sub-↑ (↓ σ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ)}) (susp-↑-↓-comm σ) ⟩
  < Coh Δ B τ [ susp-sub-↑ σ ]tm >tm ∎
    where
      open Reasoning tm-setoid

susp-↑-comp-sub ⟨ _ ⟩′ σ = Null≃ (susp-↑-comp-ty _ σ)
susp-↑-comp-sub ⟨ τ , t ⟩ σ = Ext≃ (susp-↑-comp-sub τ σ) (susp-↑-comp-tm t σ)

susp-↑-↑ : (σ : Sub (2 + n) m A) → susp-sub-↑ (↑ σ) ≃s ↑ (susp-sub-↑ σ)
susp-↑-↑ ⟨ ⟨ ⟨ _ ⟩′ , _ ⟩ , _ ⟩ = refl≃s
susp-↑-↑ ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ = Ext≃ (susp-↑-↑ σ) refl≃tm

↑-comp-sub : (σ : Sub (2 + l) n B)
           → (τ : Sub n m A)
           → ↑ σ ● τ ≃s ↑ (σ ● τ)
↑-comp-sub ⟨ ⟨ ⟨ _ ⟩′ , _ ⟩ , _ ⟩ τ = refl≃s
↑-comp-sub ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ τ = Ext≃ (↑-comp-sub σ τ) refl≃tm

↑-susp : (u : Tm n) → .⦃ isVar u ⦄ → (σ : Sub (2 + n) m A) → susp-tm u [ σ ]tm ≃tm u [ ↑ σ ]tm
↑-susp (Var zero) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = refl≃tm
↑-susp (Var (suc i)) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = ↑-susp (Var i) ⟨ ⟨ σ , u ⟩ , s ⟩

↓-↑-≃ : (σ : Sub (2 + n) m A) → ↓ (↑ σ) ≃s σ
↓-↑-≃ ⟨ ⟨ ⟨ _ ⟩′ , s ⟩ , t ⟩ = refl≃s
↓-↑-≃ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = Ext≃ (↓-↑-≃ ⟨ ⟨ σ , u ⟩ , s ⟩) refl≃tm

↑-susp-full : (u : Tm n)
            → (σ : Sub (2 + n) m A)
            → susp-tm u [ σ ]tm ≃tm u [ ↑ σ ]tm
↑-susp-full (Var i) σ = ↑-susp (Var i) σ
↑-susp-full (Coh S A τ) σ = sub-action-≃-tm (refl≃tm {s = susp-tm (Coh S A τ)}) (sym≃s (↓-↑-≃ σ))

susp-tm-glob : (t : Tm n) → ⦃ isVar t ⦄ → isVar (susp-tm t)
susp-tm-glob (Var i) = tt

susp-ty-glob : (A : Ty n) → ⦃ ty-is-globular A ⦄ → ty-is-globular (susp-ty A)
susp-ty-glob ⋆ = tt ,, (tt ,, tt)
susp-ty-glob (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ = susp-tm-glob s ⦃ a ⦄ ,, (susp-ty-glob A ⦃ b ⦄) ,, (susp-tm-glob t ⦃ c ⦄)

susp-ctx-glob : (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → ctx-is-globular (susp-ctx Γ)
susp-ctx-glob ∅ = (tt ,, tt) ,, tt
susp-ctx-glob (Γ , A) ⦃ a ,, b ⦄ = susp-ctx-glob Γ ⦃ a ⦄ ,, susp-ty-glob A ⦃ b ⦄

tm-to-ty-susp : (t : Tm n) → (Γ : Ctx n) → susp-ty (tm-to-ty Γ t) ≃ty tm-to-ty (susp-ctx Γ) (susp-tm t)
tm-to-ty-susp (Var zero) (Γ , A) = susp-ty-lift A
tm-to-ty-susp (Var (suc i)) (Γ , A) = trans≃ty (susp-ty-lift (Γ ‼ i)) (lift-ty-≃ (tm-to-ty-susp (Var i) Γ))
tm-to-ty-susp (Coh S A σ) Γ = susp-functorial-ty σ A

ty-base-susp : (A : Ty n) → .⦃ NonZero (ty-dim A) ⦄ → ty-base (susp-ty A) ≃ty susp-ty (ty-base A)
ty-base-susp (s ─⟨ A ⟩⟶ t) = refl≃ty

ty-src-susp : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src (susp-ty A) ⦃ NonZero-subst (sym (susp-dim A)) it ⦄ ≃tm susp-tm (ty-src A)
ty-src-susp (s ─⟨ A ⟩⟶ t) = refl≃tm

ty-tgt-susp : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt (susp-ty A) ⦃ NonZero-subst (sym (susp-dim A)) it ⦄ ≃tm susp-tm (ty-tgt A)
ty-tgt-susp (s ─⟨ A ⟩⟶ t) = refl≃tm

ty-src′-susp : (A : Ty (suc n)) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src′ (susp-ty A) ≃tm susp-tm (ty-src′ A)
ty-src′-susp (s ─⟨ A ⟩⟶ t) = refl≃tm

ty-tgt′-susp : (A : Ty (suc n)) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt′ (susp-ty A) ≃tm susp-tm (ty-tgt′ A)
ty-tgt′-susp (s ─⟨ A ⟩⟶ t) = refl≃tm
