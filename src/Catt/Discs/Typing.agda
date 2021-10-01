{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Discs.Typing (index : ℕ)
                         (rule : Fin index → Rule)
                         (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Discs
open import Catt.Globular
open import Catt.Globular.Typing index rule lift-rule
open P index rule
open import Catt.Discs.Properties
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles

sub-from-sphere-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p)
sub-from-sphere-Ty zero TyStar p = TyNull TyStar
sub-from-sphere-Ty (suc d) (TyArr sty Aty tty) p = TyExt (TyExt (sub-from-sphere-Ty d Aty (cong pred p))
                                                      (term-conversion sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ (cong pred p))))))
                                               (term-conversion tty (reflexive≈ty (sym≃ty (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d _ (cong pred p)) (sphere-type _)) (sub-from-sphere-prop d _ (cong pred p))))))

sub-from-disc-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Tm Γ t A → Typing-Sub (Disc d) Γ (sub-from-disc d A p t)
sub-from-disc-Ty {t = t} d Aty p tty = TyExt (sub-from-sphere-Ty d Aty p) (term-conversion tty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ p))))

sub-from-sphere-Eq : (d : ℕ) → {σ : Sub (sphere-size d) n A} → {τ : Sub (sphere-size d) n A} → Typing-Sub (Sphere d) Γ σ → Typing-Sub (Sphere d) Γ τ → sphere-type d [ σ ]ty ≈[ Γ ]ty sphere-type d [ τ ]ty → σ ≈[ Γ ]s τ
sub-from-sphere-Eq zero (TyNull x) (TyNull x₁) p = Null≈ refl≈ty
sub-from-sphere-Eq {Γ = Γ} (suc d) (TyExt (TyExt {σ = σ} σty y) x) (TyExt (TyExt {σ = τ} τty y′) x′) (Arr≈ p q r) = Ext≈ (Ext≈ (sub-from-sphere-Eq d σty τty lem) p) r
  where
    lem : (sphere-type d [ σ ]ty) ≈[ Γ ]ty (sphere-type d [ τ ]ty)
    lem = begin
      sphere-type d [ σ ]ty
        ≈˘⟨ reflexive≈ty (lift-sub-comp-lem-ty σ (sphere-type d)) ⟩
      liftType (sphere-type d) [ ⟨ σ , _ ⟩ ]ty
        ≈˘⟨ reflexive≈ty (lift-sub-comp-lem-ty ⟨ σ , _ ⟩ (liftType (sphere-type d))) ⟩
      liftType (liftType (sphere-type d)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]ty
        ≈⟨ q ⟩
      liftType (liftType (sphere-type d)) [ ⟨ ⟨ τ , _ ⟩ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (lift-sub-comp-lem-ty ⟨ τ , _ ⟩ (liftType (sphere-type d))) ⟩
      liftType (sphere-type d) [ ⟨ τ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (lift-sub-comp-lem-ty τ (sphere-type d)) ⟩
      sphere-type d [ τ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Γ)

sub-from-disc-Eq : (d : ℕ) → {σ : Sub (disc-size d) n A} → {τ : Sub (disc-size d) n A} → Typing-Sub (Disc d) Γ σ → Typing-Sub (Disc d) Γ τ → 0V [ σ ]tm ≃tm 0V [ τ ]tm → σ ≈[ Γ ]s τ
sub-from-disc-Eq d (TyExt σty x) (TyExt τty y) p = Ext≈ (sub-from-sphere-Eq d σty τty (Ty-unique-≃ p x y)) (reflexive≈tm p)
