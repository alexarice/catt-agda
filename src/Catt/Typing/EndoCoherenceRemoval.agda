open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Pasting
open import Catt.Globular
open import Catt.Globular.Properties

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
            → Typing-Sub Δ (Γ , B) (liftSub σ)
            → liftTerm (Coh Δ (s ─⟨ A ⟩⟶ s) σ) ≈[ Γ , B ]tm liftTerm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)))
  lift-rule {Δ = Δ} {A = A} {s = s} {σ = σ} Aty sty σty = begin
    Coh Δ (s ─⟨ A ⟩⟶ s) (liftSub σ)
      ≈⟨ ecr Aty sty σty ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ liftSub σ ]ty) _ (s [ liftSub σ ]tm))
      ≈⟨ reflexive≈tm (identity-≃ refl (sub-from-disc-≃ (ty-dim A) (ty-dim A) (apply-lifted-sub-ty-≃ A σ) _ _ (apply-lifted-sub-tm-≃ s σ))) ⟩
    identity (ty-dim A) (sub-from-disc (ty-dim A) (liftType (A [ σ ]ty)) _ (liftTerm (s [ σ ]tm)))
      ≈˘⟨ reflexive≈tm (identity-≃ refl (lift-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ⟩
    identity (ty-dim A) (liftSub (sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm))) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  susp-rule : .⦃ pd : suspCtx Δ ⊢pd ⦄
            → Typing-Ty (suspCtx Δ) (suspTy A)
            → Typing-Tm (suspCtx Δ) (suspTm s) (suspTy A)
            → Typing-Sub (suspCtx Δ) (suspCtx Γ) (suspSub σ)
            → suspTm (Coh Δ (s ─⟨ A ⟩⟶ s) σ) ≈[ suspCtx Γ ]tm suspTm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm)))
  susp-rule {Δ = Δ} {A = A} {s = s} {σ = σ} Aty sty σty = begin
    Coh (suspCtx Δ) (suspTm s ─⟨ suspTy A ⟩⟶ suspTm s) (suspSub σ)
      ≈⟨ ecr Aty sty σty ⟩
    identity (ty-dim (suspTy A)) (sub-from-disc (ty-dim (suspTy A)) (suspTy A [ suspSub σ ]ty) _
       (suspTm s [ suspSub σ ]tm))
      ≈˘⟨ reflexive≈tm (identity-≃ (sym (susp-dim A)) (sub-from-disc-≃ (suc (ty-dim A)) (ty-dim (suspTy A)) (susp-functorial-ty σ A) (trans (susp-dim (A [ σ ]ty)) (cong suc (sym (sub-dim σ A)))) (sym (sub-dim (suspSub σ) (suspTy A))) (susp-functorial-tm σ s))) ⟩
    identity (suc (ty-dim A)) (sub-from-disc (suc (ty-dim A)) (suspTy (A [ σ ]ty)) _ (suspTm (s [ σ ]tm)))
      ≈˘⟨ reflexive≈tm (Coh≃ lem (Arr≃ (Var≃ (≃c-preserve-length lem) refl) lem2 (Var≃ (≃c-preserve-length lem) refl)) (susp-sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))) ⟩
    suspTm (identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm))) ∎
    where
      lem : suspCtx (Disc (ty-dim A)) ≃c Disc (suc (ty-dim A))
      lem = disc-susp (ty-dim A)

      lem2 : suspTy (liftType (sphere-type (ty-dim A))) ≃ty
               liftType (sphere-type (suc (ty-dim A)))
      lem2 = begin
        < suspTy (liftType (sphere-type (ty-dim A))) >ty
          ≈⟨ susp-ty-lift (sphere-type (ty-dim A)) ⟩
        < liftType (suspTy (sphere-type (ty-dim A))) >ty
          ≈⟨ lift-ty-≃ (sphere-type-susp (ty-dim A)) ⟩
        < liftType (sphere-type (suc (ty-dim A))) >ty ∎
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
