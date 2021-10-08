{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Globular.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open P index rule
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Syntax.SyntacticEquality
open import Data.Nat.Properties
open import Data.Fin.Properties

tm-to-ty-prop : Typing-Tm Γ t A → tm-to-ty Γ t ≈[ Γ ]ty A
tm-to-ty-prop (TyVarZ x) = x
tm-to-ty-prop (TyVarS i tty x) = trans≈ty (lift-ty-equality (tm-to-ty-prop tty)) x
tm-to-ty-prop (TyCoh v w x y z) = z

tm-to-ty-Ty : Typing-Tm Γ t A → Typing-Tm Γ t (tm-to-ty Γ t)
tm-to-ty-Ty (TyVarZ x) = TyVarZ refl≈ty
tm-to-ty-Ty (TyVarS i tty x) = TyVarS i (tm-to-ty-Ty tty) refl≈ty
tm-to-ty-Ty (TyCoh v w x y z) = TyCoh v w x y refl≈ty

Ty-unique : Typing-Tm Γ t A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique (TyVarZ x) (TyVarZ y) = trans≈ty (sym≈ty x) y
Ty-unique (TyVarS _ tty x) (TyVarS _ tty2 y) = trans≈ty (trans≈ty (sym≈ty x) (lift-ty-equality (Ty-unique tty tty2))) y
Ty-unique (TyCoh _ _ _ _ x) (TyCoh _ _ _ _ y) = trans≈ty (sym≈ty x) y

Ty-unique-≃ : s ≃tm t → Typing-Tm Γ s A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique-≃ p tty tty2 with ≃tm-to-≡ p
... | refl = Ty-unique tty tty2

tm-height-is-ty-dim : Typing-Tm Δ t A → tm-height Δ t ≡ ty-dim A
tm-height-is-ty-dim tty = ≈ty-preserve-height (tm-to-ty-prop tty)

sub-tm-height : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m A} → Typing-Sub Γ Δ σ → tm-height Γ t + ty-dim A ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height {A = A} {Δ = Δ} (Var zero) (Γ , B) (TyExt {σ = σ} {t = t} σty x) = begin
  ty-dim (liftType B) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (lift-ty-dim B) ⟩
  ty-dim B + ty-dim A
    ≡⟨ sub-dim′ σ B ⟩
  ty-dim (B [ σ ]ty)
    ≡˘⟨ tm-height-is-ty-dim x ⟩
  tm-height Δ (Var zero [ ⟨ σ , t ⟩ ]tm) ∎
  where
    open ≡-Reasoning
sub-tm-height {A = A} (Var (suc i)) (Γ , B) (TyExt {σ = σ} {t = t} σty x) = begin
  ty-dim (liftType (Γ ‼ i)) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (lift-ty-dim (Γ ‼ i)) ⟩
  ty-dim (Γ ‼ i) + ty-dim A
    ≡⟨ sub-tm-height (Var i) Γ σty ⟩
  tm-height _ (Var (suc i) [ ⟨ σ , t ⟩ ]tm) ∎
  where
    open ≡-Reasoning
sub-tm-height {A = A} (Coh S B τ) Γ {σ} σty = begin
  ty-dim (B [ τ ]ty) + ty-dim A
    ≡⟨ sub-dim′ σ (B [ τ ]ty) ⟩
  ty-dim ((B [ τ ]ty) [ σ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (assoc-ty σ τ B)) ⟩
  ty-dim (B [ σ ∘ τ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (tm-to-ty-coh-sub S B τ _ σ)) ⟩
  tm-height _ (Coh S B τ [ σ ]tm) ∎
  where
    open ≡-Reasoning

sub-tm-height-0 : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → tm-height Γ t ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height-0 t Γ σty = trans (sym (+-identityʳ _)) (sub-tm-height t Γ σty)
