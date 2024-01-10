open import Catt.Typing.Base

module Catt.Typing.Pruning {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
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
           → Typing-Tm Γ (Coh ⌊ dy ⌋d A σ) C
           → Coh ⌊ dy ⌋d A σ ≈[ Γ ]tm Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (prune-sub p σ)

module Conditions (prune : HasPruning) where
  open import Catt.Typing.Rule rule

  lift-rule : (p : Peak dy) → {B : Ty (ctxLength Γ)} → (pf : peak-term p [ σ ]tm ≃tm identity-term B t) → LiftRule (Pruning Γ dy A p σ)
  lift-rule {dy = dy} {Γ = Γ} {σ = σ} {t = t} {A = A} p {B} pf {A = C} tty = begin
    Coh ⌊ dy ⌋d A (lift-sub σ)
      ≈⟨ prune {Γ = (Γ , C)} p lem {lift-ty _} tty ⟩
    Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (prune-sub p (lift-sub σ))
      ≈⟨ Coh≈ refl≈ty (reflexive≈s (lift-prune-sub p σ)) ⟩
    Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (lift-sub (prune-sub p σ)) ∎
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

  susp-rule : (p : Peak dy) → {B : Ty (ctxLength Γ)} → (pf : peak-term p [ σ ]tm ≃tm identity-term B t) → SuspRule (Pruning Γ dy A p σ)
  susp-rule {dy = dy}  {Γ = Γ} {σ = σ} {t = t}{A = A} p {B} pf tty = begin
    Coh (susp-ctx ⌊ dy ⌋d) (susp-ty A) (susp-sub σ)
      ≈˘⟨ reflexive≈tm (Coh≃ (susp-⌊⌋d dy) refl≃ty refl≃s) ⟩
    Coh ⌊ susp-dyck dy ⌋d (susp-ty A) (susp-sub σ)
      ≈⟨ prune (⇓pk (susp-peak p)) lem (transport-typing tty (Coh≃ (sym≃c (susp-⌊⌋d dy)) refl≃ty refl≃s)) ⟩
    Coh ⌊ prune-peak (susp-peak p) ⌋d
        (susp-ty A [ prune-project (susp-peak p) ]ty)
        (prune-sub (susp-peak p) (susp-sub σ))
      ≈⟨ reflexive≈tm (Coh≃ l1 l2 (susp-prune-sub p σ)) ⟩
    Coh (susp-ctx ⌊ prune-peak p ⌋d)
        (susp-ty (A [ prune-project p ]ty))
        (susp-sub (prune-sub p σ)) ∎
    where
      l1 : ⌊ prune-peak (susp-peak p) ⌋d ≃c
            susp-ctx ⌊ prune-peak p ⌋d
      l1 = begin
        < ⌊ prune-peak (susp-peak p) ⌋d >c
          ≈⟨ ⌊⌋d-≃ (prune-susp-peak p) ⟩
        < ⌊ susp-dyck (prune-peak p) ⌋d >c
          ≈⟨ susp-⌊⌋d (prune-peak p) ⟩
        < susp-ctx ⌊ prune-peak p ⌋d >c ∎
        where
          open Reasoning ctx-setoid

      l2 : (susp-ty A [ prune-project (susp-peak p) ]ty) ≃ty
            susp-ty (A [ prune-project p ]ty)
      l2 = begin
        < susp-ty A [ prune-project (susp-peak p) ]ty >ty
          ≈⟨ sub-action-≃-ty refl≃ty (susp-prune-project p) ⟩
        < susp-ty A [ susp-sub (prune-project p) ]ty >ty
          ≈˘⟨ susp-functorial-ty (prune-project p) A ⟩
        < susp-ty (A [ prune-project p ]ty) >ty ∎
        where
          open Reasoning ty-setoid

      lem : (peak-term (susp-peak p) [ susp-sub σ ]tm) ≃tm identity-term (susp-ty B) (susp-tm t)
      lem = begin
        < peak-term (susp-peak p) [ susp-sub σ ]tm >tm
          ≈⟨ sub-action-≃-tm (susp-peak-term p) refl≃s ⟩
        < susp-tm (peak-term p) [ susp-sub σ ]tm >tm
          ≈˘⟨ susp-functorial-tm σ (peak-term p) ⟩
        < susp-tm (peak-term p [ σ ]tm) >tm
          ≈⟨ susp-tm-≃ pf ⟩
        < susp-tm (identity-term B t) >tm
          ≈⟨ identity-term-susp B t ⟩
        < identity-term (susp-ty B) (susp-tm t) >tm ∎
        where
          open Reasoning tm-setoid
      open Reasoning (tm-setoid-≈ _)

  sub-rule : (p : Peak dy) → {B : Ty (ctxLength Γ)} → (pf : peak-term p [ σ ]tm ≃tm identity-term B t) → SubRule (Pruning Γ dy A p σ)
  sub-rule {dy = dy} {σ = σ} {t = t} {A = A} p {B} pf {σ = τ} σty tty = begin
    Coh ⌊ dy ⌋d A (τ ● σ)
      ≈⟨ prune p lem tty ⟩
    Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (prune-sub p (τ ● σ))
      ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (prune-sub-sub p σ τ)) ⟩
    Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (τ ● prune-sub p σ) ∎
    where
      lem : (peak-term p [ τ ● σ ]tm) ≃tm identity-term (B [ τ ]ty) (t [ τ ]tm)
      lem = begin
        < peak-term p [ τ ● σ ]tm >tm
          ≈⟨ assoc-tm τ σ (peak-term p) ⟩
        < peak-term p [ σ ]tm [ τ ]tm >tm
          ≈⟨ sub-action-≃-tm pf refl≃s ⟩
        < identity-term B t [ τ ]tm >tm
          ≈⟨ identity-term-sub B t τ ⟩
        < identity-term (B [ τ ]ty) (t [ τ ]tm) >tm ∎
        where
          open Reasoning tm-setoid
      open Reasoning (tm-setoid-≈ _)
