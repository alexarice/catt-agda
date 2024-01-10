open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Path

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Tree.Structured.Typing rule

open import Catt.Typing.EndoCoherenceRemoval.Base public

open Rule

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {Γ : Ctx m}
                        → {s : Tm (suc n)}
                        → {A : Ty (suc n)}
                        → {σ : Sub (suc n) m ⋆}
                        → {Δ : Ctx (suc n)}
                        → {B : Ty m}
                        → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ s) σ) B
                        → Coh Δ (s ─⟨ A ⟩⟶ s) σ ≈[ Γ ]tm identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))

HasEndoCoherenceRemoval-STm : Set
HasEndoCoherenceRemoval-STm = ∀ {m n}
                        → {Γ : Ctx m}
                        → {X : MaybeTree m}
                        → (S : Tree n)
                        → (s : STm (someTree S))
                        → (As : STy (someTree S))
                        → (L : Label X S)
                        → Typing-STm ⌊ S ⌋ s As
                        → Typing-STy ⌊ S ⌋ As
                        → Typing-Label Γ (L ,, S⋆)
                        → SCoh S (SArr s As s) (L ,, S⋆)
                          ≈[ Γ ]stm
                          (identity-stm (n-disc (sty-dim As))
                            >>= (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ●lt (L ,, S⋆))

module Conditions (ecr : HasEndoCoherenceRemoval) where
  open import Catt.Typing.Rule rule

  lift-rule : LiftRule (EndoCoherenceRemoval Γ Δ s A σ)
  lift-rule {Δ = Δ} {s = s} {A = A} {σ = σ} tty = begin
    Coh Δ (s ─⟨ A ⟩⟶ s) (lift-sub σ)
      ≈⟨ ecr tty ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ lift-sub σ ]ty) _ (s [ lift-sub σ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-≃ (ty-dim A) (ty-dim A) (apply-lifted-sub-ty-≃ A σ) _ _ (apply-lifted-sub-tm-≃ s σ))) ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (lift-ty (A [ σ ]ty)) _ (lift-tm (s [ σ ]tm)))
      ≈˘⟨ reflexive≈tm (identity-≃ refl (lift-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ⟩
    identity (ty-dim A) (lift-sub (sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm))) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  susp-rule : SuspRule (EndoCoherenceRemoval Γ Δ s A σ)
  susp-rule {Δ = Δ} {s = s} {A = A} {σ = σ} tty = begin
    Coh (susp-ctx Δ) (susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm s) (susp-sub σ)
      ≈⟨ ecr tty ⟩
    identity (ty-dim (susp-ty A)) (sub-from-disc (ty-dim (susp-ty A)) (susp-ty A [ susp-sub σ ]ty) _
       (susp-tm s [ susp-sub σ ]tm))
      ≈˘⟨ reflexive≈tm (identity-≃ (sym (susp-dim A)) (sub-from-disc-≃ (suc (ty-dim A)) (ty-dim (susp-ty A)) (susp-functorial-ty σ A) (trans (susp-dim (A [ σ ]ty)) (cong suc (sym (sub-dim σ A)))) (sym (sub-dim (susp-sub σ) (susp-ty A))) (susp-functorial-tm σ s))) ⟩
    identity (suc (ty-dim A)) (sub-from-disc (suc (ty-dim A)) (susp-ty (A [ σ ]ty)) _ (susp-tm (s [ σ ]tm)))
      ≈˘⟨ reflexive≈tm (Coh≃ lem (Arr≃ (Var≃ (≃c-preserve-length lem) refl) lem2 (Var≃ (≃c-preserve-length lem) refl)) (susp-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ⟩
    susp-tm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm))) ∎
    where
      lem : susp-ctx (Disc (ty-dim A)) ≃c Disc (suc (ty-dim A))
      lem = disc-susp (ty-dim A)

      lem2 : susp-ty (lift-ty (sphere-type (ty-dim A))) ≃ty
               lift-ty (sphere-type (suc (ty-dim A)))
      lem2 = begin
        < susp-ty (lift-ty (sphere-type (ty-dim A))) >ty
          ≈⟨ susp-ty-lift (sphere-type (ty-dim A)) ⟩
        < lift-ty (susp-ty (sphere-type (ty-dim A))) >ty
          ≈⟨ lift-ty-≃ (sphere-type-susp (ty-dim A)) ⟩
        < lift-ty (sphere-type (suc (ty-dim A))) >ty ∎
        where
          open Reasoning ty-setoid
      open Reasoning (tm-setoid-≈ _)

  sub-rule : SubRule (EndoCoherenceRemoval Γ Δ s A τ)
  sub-rule {Δ = Δ} {s = s} {A = A} {τ = τ} {σ = σ} τty tty = begin
    Coh Δ (s ─⟨ A ⟩⟶ s) (σ ● τ)
      ≈⟨ ecr tty ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ● τ ]ty) _ (s [ σ ● τ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-≃ (ty-dim A) (ty-dim A) (assoc-ty σ τ A) (sym (sub-dim (σ ● τ) A)) (trans (sym (sub-dim σ (A [ τ ]ty))) (sym (sub-dim τ A))) (assoc-tm σ τ s))) ⟩
    identity (ty-dim A)
      (sub-from-disc (ty-dim A) (A [ τ ]ty [ σ ]ty) _ (s [ τ ]tm [ σ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-sub (ty-dim A) (A [ τ ]ty) (sym (sub-dim τ A)) (s [ τ ]tm) σ)) ⟩
    identity (ty-dim A) (σ ● sub-from-disc (ty-dim A) (A [ τ ]ty) _ (s [ τ ]tm)) ∎
    where
      open Reasoning (tm-setoid-≈ _)
