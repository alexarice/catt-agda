open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Discs.Typing (index : ℕ)
                         (rule : Fin index → Rule)
                         (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Discs
open import Catt.Globular
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open P index rule
open import Catt.Discs.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles

disc-tm-Ty : (d : ℕ) → Typing-Tm (Disc d) 0V (liftType (sphere-type d))
sphere-type-Ty : (d : ℕ) → Typing-Ty (Sphere d) (sphere-type d)
sphere-type-Ty zero = TyStar
sphere-type-Ty (suc d) = TyArr (TyVarS zero (disc-tm-Ty d) refl≈ty) (lift-ty-typing (lift-ty-typing (sphere-type-Ty d))) (TyVarZ (lift-ty-typing (sphere-type-Ty d)) refl≈ty)

disc-tm-Ty d = TyVarZ (sphere-type-Ty d) refl≈ty


sub-from-sphere-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p)
sub-from-sphere-Ty zero TyStar p = TyNull TyStar
sub-from-sphere-Ty (suc d) (TyArr {A = A} sty Aty tty) p
  = TyExt (TyExt (sub-from-sphere-Ty d Aty (cong pred p))
                 (sphere-type-Ty d)
                 (term-conversion sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ (cong pred p))))))
          (lift-ty-typing (sphere-type-Ty d))
          (term-conversion tty (reflexive≈ty lem))
  where
    open Reasoning ty-setoid
    lem : A ≃ty
            (liftType (sphere-type d) [ ⟨ sub-from-sphere d A (cong pred p) , _ ⟩ ]ty)
    lem = begin
      < A >ty
        ≈˘⟨ sub-from-sphere-prop d A (cong pred p) ⟩
      < sphere-type d [ sub-from-sphere d A (cong pred p) ]ty >ty
        ≈˘⟨ lift-sub-comp-lem-ty (sub-from-sphere d A _) (sphere-type d) ⟩
      < liftType (sphere-type d) [ ⟨ sub-from-sphere d A (cong pred p) , _ ⟩ ]ty >ty ∎

sub-from-disc-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Tm Γ t A → Typing-Sub (Disc d) Γ (sub-from-disc d A p t)
sub-from-disc-Ty {t = t} d Aty p tty
  = TyExt (sub-from-sphere-Ty d Aty p)
          (sphere-type-Ty d)
          (term-conversion tty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ p))))

sub-from-sphere-Eq : (d : ℕ) → {σ : Sub (sphere-size d) n A} → {τ : Sub (sphere-size d) n A} → Typing-Sub (Sphere d) Γ σ → Typing-Sub (Sphere d) Γ τ → sphere-type d [ σ ]ty ≈[ Γ ]ty sphere-type d [ τ ]ty → σ ≈[ Γ ]s τ
sub-from-sphere-Eq zero (TyNull x) (TyNull x₁) p = Null≈ refl≈ty
sub-from-sphere-Eq {Γ = Γ} (suc d) (TyExt (TyExt {σ = σ} σty Bty y) Aty x) (TyExt (TyExt {σ = τ} τty Bty′ y′) Aty′ x′) (Arr≈ p q r) = Ext≈ (Ext≈ (sub-from-sphere-Eq d σty τty lem) p) r
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
sub-from-disc-Eq d (TyExt σty Aty x) (TyExt τty Bty y) p = Ext≈ (sub-from-sphere-Eq d σty τty (Ty-unique-≃ p x y)) (reflexive≈tm p)
