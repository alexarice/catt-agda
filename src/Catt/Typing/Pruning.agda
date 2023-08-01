open import Catt.Typing.Base

module Catt.Typing.Pruning {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule

open import Catt.Typing.Pruning.Base public

open Rule

HasPruning : Set
HasPruning = ∀ {m n}
           → {Γ : Ctx m}
           → {dy : Dyck (suc n) 0}
           → {A : Ty (3 + n * 2)}
           → (p : Peak dy)
           → {σ : Sub (3 + n * 2) m ⋆}
           → {B : Ty m}
           → {t : Tm m}
           → (peak-term p [ σ ]tm ≃tm identity-term B t)
           → {C : Ty m}
           → Typing-Tm Γ (Coh (dyck-to-ctx dy) A σ) C
           → Coh (dyck-to-ctx dy) A σ ≈[ Γ ]tm Coh (dyck-to-ctx (prune-peak p)) (A [ prune-project p ]ty) (prune-sub p σ)

module Conditions (prune : HasPruning) where
  open import Catt.Typing.Rule rule

  lift-rule : (p : Peak dy) → (pf : peak-term p [ σ ]tm ≃tm identity-term B t) → LiftRule (Pruning Γ dy A p σ B t pf)
  lift-rule {dy = dy} {σ = σ} {B = B} {t = t} {Γ = Γ} {A = A} p pf {A = C} tty = begin
    Coh (dyck-to-ctx dy) A (lift-sub σ)
      ≈⟨ prune {Γ = (Γ , C)} p lem {lift-ty _} tty ⟩
    Coh (dyck-to-ctx (prune-peak p)) (A [ prune-project p ]ty) (prune-sub p (lift-sub σ))
      ≈⟨ Coh≈ refl≈ty (reflexive≈s (lift-prune-sub p σ)) ⟩
    Coh (dyck-to-ctx (prune-peak p)) (A [ prune-project p ]ty) (lift-sub (prune-sub p σ)) ∎
    where
      lem : (peak-term p [ lift-sub σ ]tm) ≃tm identity-term (lift-ty B) (lift-tm t)
      lem = begin
        < peak-term p [ lift-sub σ ]tm >tm
          ≈⟨ apply-lifted-sub-tm-≃ (peak-term p) σ ⟩
        < lift-tm (peak-term p [ σ ]tm) >tm
          ≈⟨ lift-tm-≃ pf ⟩
        < lift-tm (identity-term B t) >tm
          ≈⟨ identity-term-lift B t ⟩
        < identity-term (lift-ty B) (lift-tm t) >tm ∎
        where
          open Reasoning tm-setoid

      open Reasoning (tm-setoid-≈ _)

  susp-rule : (p : Peak dy) → (pf : peak-term p [ σ ]tm ≃tm identity-term B t) → SuspRule (Pruning Γ dy A p σ B t pf)
  susp-rule {dy = dy} {σ = σ} {B = B} {t = t} {Γ = Γ} {A = A} p pf tty = begin
    Coh (susp-ctx (dyck-to-ctx dy)) (susp-ty A) (susp-sub σ)
      ≈˘⟨ reflexive≈tm (Coh≃ (dyck-to-ctx-≃ {!!}) refl≃ty refl≃s) ⟩
    Coh (dyck-to-ctx (susp-dyck dy)) (susp-ty A) (susp-sub σ)
      ≈⟨ {!!} ⟩
    {!!}
      ≈⟨ {!!} ⟩
    {!!} ∎
    where
      open Reasoning (tm-setoid-≈ _)
