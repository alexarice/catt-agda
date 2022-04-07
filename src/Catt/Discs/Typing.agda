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
open import Catt.Discs.Pasting
open import Catt.Discs.Support
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles

disc-tm-Ty : (d : ℕ) → Typing-Tm (Disc d) 0V (liftType (sphere-type d))
disc-tm-Ty d = TyVar zero

sphere-type-Ty : (d : ℕ) → Typing-Ty (Sphere d) (sphere-type d)
sphere-type-Ty zero = TyStar
sphere-type-Ty (suc d) = TyArr (TyVar (suc zero)) (lift-ty-typing (lift-ty-typing (sphere-type-Ty d))) (TyVar zero)

sub-from-sphere-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p)
sub-from-sphere-Ty zero TyStar p = TyNull TyStar
sub-from-sphere-Ty (suc d) (TyArr {A = A} sty Aty tty) p
  = TyExt (TyExt (sub-from-sphere-Ty d Aty (cong pred p))
                 (TyConv sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ (cong pred p))))))
          (TyConv tty (reflexive≈ty lem))
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
          (TyConv tty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ p))))

sub-from-sphere-≈ : (d : ℕ) → (q : A ≈[ Γ ]ty B) → .(p : ty-dim A ≡ d) → sub-from-sphere d A p ≈[ Γ ]s sub-from-sphere d B (trans (sym (ty-dim-≈ q)) p)
sub-from-sphere-≈ zero Star≈ q = Null≈ Star≈
sub-from-sphere-≈ (suc d) (Arr≈ x p y) q = Ext≈ (Ext≈ (sub-from-sphere-≈ d p (cong pred q)) x) y

sub-from-disc-≈ : (d : ℕ) → (q : A ≈[ Γ ]ty B) → .(p : ty-dim A ≡ d) → s ≈[ Γ ]tm t → sub-from-disc d A p s ≈[ Γ ]s sub-from-disc d B (trans (sym (ty-dim-≈ q)) p) t
sub-from-disc-≈ d q p r = Ext≈ (sub-from-sphere-≈ d q p) r

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

identity-Ty : Typing-Tm Γ t A → Typing-Ty Γ A → Typing-Tm Γ (identity t A) (t ─⟨ A ⟩⟶ t)
identity-Ty {t = t} {A = A} tty Aty
  = TyConv (TyCoh ⦃ disc-pd (ty-dim A) ⦄
          (TyArr (disc-tm-Ty (ty-dim A)) (lift-ty-typing (sphere-type-Ty (ty-dim A))) (disc-tm-Ty (ty-dim A)))
          (sub-from-disc-Ty (ty-dim A) Aty refl tty)
          false
          lem)
          (Arr≈ refl≈tm (reflexive≈ty (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere (ty-dim A) A refl) (sphere-type (ty-dim A))) (sub-from-sphere-prop (ty-dim A) A refl))) refl≈tm)
  where
    open ≡-Reasoning

    lem : FVTy (liftType (sphere-type (ty-dim A))) ∪ ewt empty ∪ ewt empty ≡ full
    lem = begin
      FVTy (liftType (sphere-type (ty-dim A))) ∪ ewt empty ∪ ewt empty
        ≡⟨ cong (λ - → - ∪ ewt empty ∪ ewt empty) (supp-lift-ty (sphere-type (ty-dim A))) ⟩
      ewf (FVTy (sphere-type (ty-dim A))) ∪ ewt empty ∪ ewt empty
        ≡⟨ cong ewt (∪-right-unit (FVTy (sphere-type (ty-dim A)) ∪ empty)) ⟩
      ewt (FVTy (sphere-type (ty-dim A)) ∪ empty)
        ≡⟨ cong ewt (∪-right-unit (FVTy (sphere-type (ty-dim A)))) ⟩
      ewt (FVTy (sphere-type (ty-dim A)))
        ≡⟨ cong ewt (sphere-supp (ty-dim A)) ⟩
      full ∎

identity-≈ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → identity s A ≈[ Γ ]tm identity t B
identity-≈ {A = A} {B = B} p q
  = trans≈tm (reflexive≈tm (identity-lem (ty-dim-≈ q) (sub-from-disc-≃ (ty-dim A) (ty-dim B) refl≃ty refl (ty-dim-≈ q) refl≃tm)))
             (Coh≈ refl≈ty (sub-from-disc-≈ (ty-dim B) q (ty-dim-≈ q) p))

sub-from-disc-to-term-Ty : (d : ℕ) → (p : ty-dim A ≡ d) → Typing-Sub (Disc d) Γ (sub-from-disc d A p t) → Typing-Tm Γ t A
sub-from-disc-to-term-Ty {A = A} d p (TyExt _ tty) = TyConv tty (reflexive≈ty (sub-from-sphere-prop d A p))

sub-from-sphere-to-ty-Ty : (d : ℕ) → (p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p) → Typing-Ty Γ A
sub-from-sphere-to-ty-Ty {A = ⋆} zero p σty = TyStar
sub-from-sphere-to-ty-Ty {A = s ─⟨ A ⟩⟶ t} (suc d) p (TyExt (TyExt σty sty) tty)
  = TyArr (TyConv sty (reflexive≈ty (sub-from-sphere-prop d A (cong pred p))))
          (sub-from-sphere-to-ty-Ty d (cong pred p) σty)
          (TyConv tty (reflexive≈ty (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d A _) (sphere-type d)) (sub-from-sphere-prop d A (cong pred p)))))

identity-to-term-Ty : Typing-Tm Γ (identity t A) B → Typing-Tm Γ t A
identity-to-term-Ty (TyConv tty p) = identity-to-term-Ty tty
identity-to-term-Ty (TyCoh Aty σty _ _) = sub-from-disc-to-term-Ty (ty-dim _) refl σty

identity-to-type-Ty : Typing-Tm Γ (identity t A) B → Typing-Ty Γ A
identity-to-type-Ty (TyConv tty p) = identity-to-type-Ty tty
identity-to-type-Ty (TyCoh Aty (TyExt σty _) _ _) = sub-from-sphere-to-ty-Ty (ty-dim _) refl σty
