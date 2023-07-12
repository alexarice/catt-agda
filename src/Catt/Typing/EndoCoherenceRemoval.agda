open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Tree.Label.Typing rule

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {Γ : Ctx m}
                        → {s : Tm (suc n)}
                        → {A : Ty (suc n)}
                        → {σ : Sub (suc n) m ⋆}
                        → {Δ : Ctx (suc n)}
                        → .⦃ pd : Δ ⊢pd ⦄
                        → Typing-Ty Δ A
                        → Typing-Tm Δ s A
                        → Typing-Sub Δ Γ σ
                        → Coh Δ (s ─⟨ A ⟩⟶ s) σ ≈[ Γ ]tm identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))

HasEndoCoherenceRemoval-STm : Set
HasEndoCoherenceRemoval-STm = ∀ {m n}
                        → {Γ : Ctx m}
                        → {X : MaybeTree m}
                        → (S : Tree n)
                        → (s : STm (someTree S))
                        → (As : STy (someTree S))
                        → (L : Label X S)
                        → Typing-STm (tree-to-ctx S) s As
                        → Typing-STy (tree-to-ctx S) As
                        → Typing-Label Γ (L ,, S⋆)
                        → SCoh S (SArr s As s) (L ,, S⋆) ≈[ Γ ]stm (identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆))

module Conditions (ecr : HasEndoCoherenceRemoval) where

  lift-rule : .⦃ pd : Δ ⊢pd ⦄
            → Typing-Ty Δ A
            → Typing-Tm Δ s A
            → Typing-Sub Δ (Γ , B) (lift-sub σ)
            → lift-tm (Coh Δ (s ─⟨ A ⟩⟶ s) σ) ≈[ Γ , B ]tm lift-tm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)))
  lift-rule {Δ = Δ} {A = A} {s = s} {σ = σ} Aty sty σty = begin
    Coh Δ (s ─⟨ A ⟩⟶ s) (lift-sub σ)
      ≈⟨ ecr Aty sty σty ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ lift-sub σ ]ty) _ (s [ lift-sub σ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-≃ (ty-dim A) (ty-dim A) (apply-lifted-sub-ty-≃ A σ) _ _ (apply-lifted-sub-tm-≃ s σ))) ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (lift-ty (A [ σ ]ty)) _ (lift-tm (s [ σ ]tm)))
      ≈˘⟨ reflexive≈tm (identity-≃ refl (lift-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ⟩
    identity (ty-dim A) (lift-sub (sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm))) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  susp-rule : .⦃ pd : susp-ctx Δ ⊢pd ⦄
            → Typing-Ty (susp-ctx Δ) (susp-ty A)
            → Typing-Tm (susp-ctx Δ) (susp-tm s) (susp-ty A)
            → Typing-Sub (susp-ctx Δ) (susp-ctx Γ) (susp-sub σ)
            → susp-tm (Coh Δ (s ─⟨ A ⟩⟶ s) σ) ≈[ susp-ctx Γ ]tm susp-tm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)))
  susp-rule {Δ = Δ} {A = A} {s = s} {σ = σ} Aty sty σty = begin
    Coh (susp-ctx Δ) (susp-tm s ─⟨ susp-ty A ⟩⟶ susp-tm s) (susp-sub σ)
      ≈⟨ ecr Aty sty σty ⟩
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

  sub-rule : .⦃ pd : Δ ⊢pd ⦄
           → Typing-Ty Δ A
           → Typing-Tm Δ s A
           → {τ : Sub n m ⋆}
           → Typing-Sub Δ Γ (τ ● σ)
           → Coh Δ (s ─⟨ A ⟩⟶ s) σ [ τ ]tm ≈[ Γ ]tm identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)) [ τ ]tm
  sub-rule {Δ = Δ} {A = A} {s = s} {σ = σ} Aty sty {τ} σty = begin
    Coh Δ (s ─⟨ A ⟩⟶ s) (τ ● σ)
      ≈⟨ ecr Aty sty σty ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ τ ● σ ]ty) _ (s [ τ ● σ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-≃ (ty-dim A) (ty-dim A) (assoc-ty τ σ A) (sym (sub-dim (τ ● σ) A)) (trans (sym (sub-dim τ (A [ σ ]ty))) (sym (sub-dim σ A))) (assoc-tm τ σ s))) ⟩
    identity (ty-dim A)
      (sub-from-disc (ty-dim A) (A [ σ ]ty [ τ ]ty) _ (s [ σ ]tm [ τ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-sub (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm) τ)) ⟩
    identity (ty-dim A) (τ ● sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm)) ∎
    where
      open Reasoning (tm-setoid-≈ _)
