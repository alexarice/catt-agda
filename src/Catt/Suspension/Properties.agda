module Catt.Suspension.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Relation.Nullary
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Variables

getFst-Lem : suspCtx Γ ≃c suspCtx Δ → getFst {n = ctxLength Γ} ≃tm getFst {n = ctxLength Δ}
getFst-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → suc (toℕ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

getSnd-Lem : suspCtx Γ ≃c suspCtx Δ → getSnd {n = ctxLength Γ} ≃tm getSnd {n = ctxLength Δ}
getSnd-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → toℕ (inject₁ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

susp-‼ : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suspCtx Γ ‼ inject₁ (inject₁ i) ≃ty suspTy (Γ ‼ i)
susp-‼ (Γ , A) zero = sym≃ty (susp-ty-lift A)
susp-‼ (Γ , A) (suc i) = trans≃ty (lift-ty-≃ (susp-‼ Γ i)) (sym≃ty (susp-ty-lift (Γ ‼ i)))

susp-functorial-id : {n : ℕ} → suspSub (idSub {n}) ≃s idSub {2 + n}
susp-functorial-id {zero} = refl≃s
susp-functorial-id {suc n} = Ext≃ (trans≃s (susp-sub-lift idSub) (lift-sub-≃ (susp-functorial-id))) refl≃tm

suspSub-preserve-star : (σ : Sub n m ⋆) → suspTy ⋆ [ suspSub σ ]ty ≃ty suspTy (⋆ {n = m})
suspSub-preserve-star ⟨⟩ = refl≃ty
suspSub-preserve-star ⟨ σ , t ⟩ = trans≃ty (lift-sub-comp-lem-ty {t = suspTm t} (suspSub σ) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) (suspSub-preserve-star σ)

inject-susp-sub : (σ : Sub n m ⋆) → (i : Fin n) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

sub-res-unrestrict-comm : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → suspSubRes (unrestrict σ) ≃s unrestrict (suspSubRes σ)
sub-res-unrestrict-comm ⟨⟩ = refl≃s
sub-res-unrestrict-comm ⟨ σ , t ⟩ = Ext≃ (sub-res-unrestrict-comm σ) refl≃tm

susp-res-comp-ty : (B : Ty n) → (σ : Sub n m A) → suspTy (B [ σ ]ty) ≃ty B [ suspSubRes σ ]ty
susp-res-comp-tm : (t : Tm n) → (σ : Sub n m A) → suspTm (t [ σ ]tm) ≃tm t [ suspSubRes σ ]tm
susp-res-comp-sub : (σ : Sub n m A) → (τ : Sub l n B) → suspSubRes (σ ∘ τ) ≃s suspSubRes σ ∘ τ

susp-res-comp-ty ⋆ σ = refl≃ty
susp-res-comp-ty (s ─⟨ B ⟩⟶ t) σ = Arr≃ (susp-res-comp-tm s σ) (susp-res-comp-ty B σ) (susp-res-comp-tm t σ)

susp-res-comp-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
susp-res-comp-tm (Var (suc i)) ⟨ σ , t ⟩ = susp-res-comp-tm (Var i) σ
susp-res-comp-tm {A = ⋆} (Coh Δ B τ) σ = Coh≃ refl≃c refl≃ty (susp-functorial σ τ)
susp-res-comp-tm {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = trans≃tm (susp-res-comp-tm (Coh (suspCtx Δ) (suspTy B) (suspSub τ)) (unrestrict σ)) (sub-action-≃-tm (refl≃tm {s = Coh (suspCtx Δ) (suspTy B) (suspSub τ)}) (sub-res-unrestrict-comm σ))

susp-res-comp-sub σ ⟨⟩ = Null≃ (susp-res-comp-ty _ σ)
susp-res-comp-sub σ ⟨ τ , t ⟩ = Ext≃ (susp-res-comp-sub σ τ) (susp-res-comp-tm t σ)

susp-res-restrict : (σ : Sub (2 + n) m A) → (s t : Tm m) → suspSubRes (restrict σ s t) ≃s restrict (suspSubRes σ) (suspTm s) (suspTm t)
susp-res-restrict ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = refl≃s
susp-res-restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = Ext≃ (susp-res-restrict σ s t) refl≃tm

restrict-comp-sub : (τ : Sub n m A)
                  → (σ : Sub (2 + l) n B)
                  → (s t : Tm n)
                  → τ ∘ restrict σ s t ≃s restrict (τ ∘ σ) (s [ τ ]tm) (t [ τ ]tm)
restrict-comp-sub τ ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = refl≃s
restrict-comp-sub τ ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = Ext≃ (restrict-comp-sub τ σ s t) refl≃tm

restrict-susp : (u : Tm n) → .⦃ isVar u ⦄ → (σ : Sub (2 + n) m A) → suspTm u [ σ ]tm ≃tm u [ restrict σ s t ]tm
restrict-susp (Var zero) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = refl≃tm
restrict-susp (Var (suc i)) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = restrict-susp (Var i) ⟨ ⟨ σ , u ⟩ , s ⟩

unrestrict-restrict-≃ : (σ : Sub (2 + n) m A)
                      → s ≃tm getFst [ σ ]tm
                      → t ≃tm getSnd [ σ ]tm
                      → unrestrict (restrict σ s t) ≃s σ
unrestrict-restrict-≃ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = Ext≃ (Ext≃ refl≃s p) q
unrestrict-restrict-≃ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ p q = Ext≃ (unrestrict-restrict-≃ ⟨ ⟨ σ , u ⟩ , s ⟩ p q) refl≃tm

restrict-susp-full : (u : Tm n)
                   → (σ : Sub (2 + n) m A)
                   → s ≃tm getFst [ σ ]tm
                   → t ≃tm getSnd [ σ ]tm
                   → suspTm u [ σ ]tm ≃tm u [ restrict σ s t ]tm
restrict-susp-full (Var i) σ p q = restrict-susp (Var i) σ
restrict-susp-full (Coh S A τ) σ p q = sub-action-≃-tm (refl≃tm {s = suspTm (Coh S A τ)}) (sym≃s (unrestrict-restrict-≃ σ p q))

susp-tm-glob : (t : Tm n) → ⦃ isVar t ⦄ → isVar (suspTm t)
susp-tm-glob (Var i) = tt

susp-ty-glob : (A : Ty n) → ⦃ ty-is-globular A ⦄ → ty-is-globular (suspTy A)
susp-ty-glob ⋆ = tt ,, (tt ,, tt)
susp-ty-glob (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ = susp-tm-glob s ⦃ a ⦄ ,, (susp-ty-glob A ⦃ b ⦄) ,, (susp-tm-glob t ⦃ c ⦄)

susp-ctx-glob : (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → ctx-is-globular (suspCtx Γ)
susp-ctx-glob ∅ = (tt ,, tt) ,, tt
susp-ctx-glob (Γ , A) ⦃ a ,, b ⦄ = susp-ctx-glob Γ ⦃ a ⦄ ,, susp-ty-glob A ⦃ b ⦄

tm-to-ty-susp : (t : Tm n) → (Γ : Ctx n) → suspTy (tm-to-ty Γ t) ≃ty tm-to-ty (suspCtx Γ) (suspTm t)
tm-to-ty-susp (Var zero) (Γ , A) = susp-ty-lift A
tm-to-ty-susp (Var (suc i)) (Γ , A) = trans≃ty (susp-ty-lift (Γ ‼ i)) (lift-ty-≃ (tm-to-ty-susp (Var i) Γ))
tm-to-ty-susp (Coh S A σ) Γ = susp-functorial-ty σ A

ty-base-susp : (A : Ty n) → .⦃ NonZero (ty-dim A) ⦄ → ty-base (suspTy A) ≃ty suspTy (ty-base A)
ty-base-susp (s ─⟨ A ⟩⟶ t) = refl≃ty

ty-src-susp : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src (suspTy A) ⦃ NonZero-subst (sym (susp-dim A)) it ⦄ ≃tm suspTm (ty-src A)
ty-src-susp (s ─⟨ A ⟩⟶ t) = refl≃tm

ty-tgt-susp : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt (suspTy A) ⦃ NonZero-subst (sym (susp-dim A)) it ⦄ ≃tm suspTm (ty-tgt A)
ty-tgt-susp (s ─⟨ A ⟩⟶ t) = refl≃tm
